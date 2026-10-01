#!/usr/bin/env python3
"""Forbidden-construct lint for EG/, EGTest/, EGCheck/ (PLAN_FORMALIZATION.md §4 CI).

    scripts/lint.py              # development mode: `sorry` allowed
    scripts/lint.py --release    # release mode: `sorry` / `sorryAx` forbidden too
    scripts/lint.py --self-test  # run the built-in evasion/false-positive tests
    scripts/lint.py FILE...      # lint only these files (paths relative to formal/)

This is HYGIENE, not the soundness guarantee. It keeps the proof free of meta-programming and
compiler escapes so that the out-of-band checks (kernel replay with `leanchecker`, comparator,
the environment scans in scripts/Axioms.lean and scripts/FinalCheck.lean) have a simple job.
A determined adversary can still write Lean the lint misreads; that is what those checks are for
(TRUST.md, APPROVALS/reviews/trust.*.md).

How it reads a file: a tokenizer that follows Lean's lexical rules closely enough for this
purpose — nested block comments, line comments, string literals with escapes, interpolated
strings (`s!"..{code}.."`, `m!`, `f!`, `throwError`, ...: the `{code}` parts are linted as code),
raw strings (`r"..."`, `r#"..."#`), character literals (`'"'`, `'\\''`), identifiers with
`'`/`!`/`?`, and `«»`-quoted name components, which are normalised (`«debug».skipKernelTC` is
read as `debug.skipKernelTC`). Comments are ignored (documentation may mention anything). The
words inside every string literal are checked against the keyword rules too, so a string that
the tokenizer mis-classifies cannot hide a forbidden word (at the price of rare false positives).

Rules (see RULES below for the exact lists):
* compiler/kernel escapes: `axiom` (in any position, e.g. `@[simp]axiom`, end of line),
  `admit`, `native_decide`, `native` (decide +native), `bv_decide`, `implemented_by`, `extern`,
  `unsafe`, `partial` (`partial def`: not kernel-replayable, see FinalCheck `replay`), `opaque`,
  `ofReduceBool`/`ofReduceNat`/`trustCompiler`, `debug.*` options,
  `skipKernelTC` in any spelling (also inside strings), `addDecl*`/`addAndCompile`,
  `modifyEnv`/`setEnv`;
* code that runs at elaboration time: `run_cmd`/`run_elab`/`run_meta`, `run_tac`, `by_elab`,
  `#eval`/`#eval!`, `#guard` (allowed in EGTest/ only: it evaluates a closed `Bool`, which
  cannot perform IO without `unsafe`/`implemented_by`/`extern`, all forbidden), `elab`,
  `elab_rules`, `macro`, `macro_rules`, `syntax`, `declare_syntax_cat`, `initialize`,
  `builtin_initialize`, simproc declarations, `register_option`, `meta` (module-system
  `meta def` / `meta import`), and meta attributes
  `@[command_elab|term_elab|tactic|csimp|init|macro|...]` (also via `attribute [...]`);
* meta-programming identifiers (`Lean.Elab.*`, `CommandElabM`, `MetaM`, `IO`, `getEnv`,
  `withOptions`, ...): a proof file has no use for them;
* no notation (`notation`, `infixl`, `prefix`, ...; also `local`): a global or `scoped` notation
  can take over syntax used by EGCheck/Final.lean (e.g. `type_of%` with a higher priority), and
  even a `local notation` leaves a macro and a parser constant in the environment, which the
  MetaScan of scripts/Axioms.lean rejects. Use a `def`/`abbrev` instead;
* `set_option` allowlist: `maxHeartbeats N` (0 < N <= 1000000), `maxRecDepth N`,
  `synthInstance.*` (a `*.maxHeartbeats` value must also satisfy 0 < N <= 1000000), `linter.*`,
  `pp.*`;
* only files under EGCheck/ may `import FormalConjectures*` (checked on every `import` token,
  not only at the start of a line);
* release mode: `sorry`, `sorryAx`.

`EGCheck/Final.lean` is protected (hash-locked, user-approved); its `run_cmd` meta-check and the
meta identifiers it needs are allowlisted (ALLOW below). Everything else in it is still linted.
Exit code 1 on any finding.
"""
import os
import sys
if __name__ == "__main__" and not sys.flags.isolated:
    # Never import from the script or the working directory (trust2.opus N2/N3): re-run as python3 -I.
    os.execv(sys.executable, [sys.executable, "-I"] + sys.argv)
import re

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DIRS = ["EG", "EGTest", "EGCheck"]
ROOT_FILES = ["EG.lean", "EGTest.lean", "EGCheck.lean"]

# --------------------------------------------------------------------------------------------
# Tokenizer
# --------------------------------------------------------------------------------------------


def _is_letter_like(c):
    o = ord(c)
    return ((0x3B1 <= o <= 0x3C9 and o != 0x3BB) or (0x391 <= o <= 0x3A9 and o not in (0x3A0, 0x3A3))
            or (0x3CA <= o <= 0x3FB) or (0x1F00 <= o <= 0x1FFE) or (0x2100 <= o <= 0x214F)
            or (0x1D49C <= o <= 0x1D59F))


def _is_sub_alnum(c):
    o = ord(c)
    return (0x2080 <= o <= 0x2089) or (0x2090 <= o <= 0x209C) or (0x1D62 <= o <= 0x1D6A)


def id_first(c):
    return ("a" <= c <= "z") or ("A" <= c <= "Z") or c == "_" or _is_letter_like(c)


def id_rest(c):
    return (id_first(c) or ("0" <= c <= "9") or c in "'!?" or _is_sub_alnum(c))


class Tok:
    __slots__ = ("kind", "text", "line", "in_string")

    def __init__(self, kind, text, line, in_string=False):
        self.kind, self.text, self.line, self.in_string = kind, text, line, in_string

    def __repr__(self):
        return f"{self.kind}:{self.text}@{self.line}{'(s)' if self.in_string else ''}"


# A string is lexed as an interpolated string (`{...}` = code) after these tokens.
INTERP_HEADS = {"s!", "m!", "f!", "v!", "println!", "throwError", "throwErrorAt", "dbg_trace",
                "reportIssue!", "reportDbgIssue!", "reportEMatchIssue!", "throwPRError",
                "logNamedError", "logNamedErrorAt", "logNamedWarning", "logNamedWarningAt",
                "throwNamedError", "throwNamedErrorAt"}
INTERP_BRACKET_HEADS = {"trace", "trace_goal", "aesop_trace!", "Macro.trace"}

_WORD = re.compile(r"#?(?:[A-Za-z_\u0370-\u03ff\u1f00-\u1fff\u2100-\u214f]|«[^»]*»)"
                   r"(?:[A-Za-z0-9_'!?\u0370-\u03ff\u1f00-\u1fff\u2100-\u214f\u2080-\u209c]|«[^»]*»|\.(?=[A-Za-z_«]))*")


class Lexer:
    def __init__(self, src):
        self.s, self.n = src, len(src)
        self.i, self.line = 0, 1
        self.toks, self.errors = [], []

    def peek(self, k=0):
        j = self.i + k
        return self.s[j] if j < self.n else ""

    def adv(self, k=1):
        for _ in range(k):
            if self.i < self.n and self.s[self.i] == "\n":
                self.line += 1
            self.i += 1

    def emit(self, kind, text, line, in_string=False):
        self.toks.append(Tok(kind, text, line, in_string))

    def string_words(self, text, line):
        """Treat the words of a string literal as (string-marked) identifier tokens."""
        for m in _WORD.finditer(text):
            w = m.group(0)
            ln = line + text.count("\n", 0, m.start())
            if w.startswith("#"):
                self.emit("hash", normalize(w[1:]) and "#" + normalize(w[1:]), ln, True)
            else:
                self.emit("ident", normalize(w), ln, True)

    def block_comment(self):
        start = self.line
        self.adv(2)
        depth = 1
        while self.i < self.n:
            if self.s.startswith("/-", self.i):
                depth += 1
                self.adv(2)
            elif self.s.startswith("-/", self.i):
                depth -= 1
                self.adv(2)
                if depth == 0:
                    return
            else:
                self.adv()
        self.errors.append((start, "unterminated block comment"))

    def ident(self):
        """Identifier with `.`-separated components; `«»` components are unquoted."""
        comps = []
        while True:
            if self.peek() == "«":
                j = self.s.find("»", self.i + 1)
                if j < 0:
                    self.errors.append((self.line, "unterminated «» identifier"))
                    comps.append(self.s[self.i + 1:])
                    self.adv(self.n - self.i)
                    break
                comps.append(self.s[self.i + 1:j])
                self.adv(j + 1 - self.i)
            else:
                j = self.i
                while j < self.n and (id_rest(self.s[j]) if j > self.i else id_first(self.s[j])):
                    j += 1
                comps.append(self.s[self.i:j])
                self.adv(j - self.i)
            if self.peek() == "." and (id_first(self.peek(1)) or self.peek(1) == "«"):
                self.adv()
                continue
            break
        return ".".join(comps)

    def plain_string(self, line):
        """At the opening quote. Returns the raw content."""
        self.adv()
        buf = []
        while self.i < self.n:
            c = self.peek()
            if c == "\\":
                buf.append(c + self.peek(1))
                self.adv(2)
            elif c == '"':
                self.adv()
                return "".join(buf)
            else:
                buf.append(c)
                self.adv()
        self.errors.append((line, "unterminated string literal"))
        return "".join(buf)

    def interp_string(self, line):
        """At the opening quote of an interpolated string: `{...}` segments are code."""
        self.adv()
        buf = []
        while self.i < self.n:
            c = self.peek()
            if c == "\\":
                buf.append(c + self.peek(1))
                self.adv(2)
            elif c == '"':
                self.adv()
                self.string_words("".join(buf), line)
                return
            elif c == "{":
                self.string_words("".join(buf), line)
                buf = []
                self.adv()
                self.lex(stop_at_brace=True)
                if self.peek() == "}":
                    self.adv()
            else:
                buf.append(c)
                self.adv()
        self.errors.append((line, "unterminated interpolated string"))
        self.string_words("".join(buf), line)

    def raw_string(self, line):
        """At `r`, followed by `#*"`."""
        self.adv()
        hashes = 0
        while self.peek() == "#":
            hashes += 1
            self.adv()
        self.adv()  # opening quote
        close = '"' + "#" * hashes
        j = self.s.find(close, self.i)
        if j < 0:
            self.errors.append((line, "unterminated raw string"))
            j = self.n
        text = self.s[self.i:j]
        self.adv(min(j + len(close), self.n) - self.i)
        self.string_words(text, line)

    def char_literal(self):
        """At `'`. Returns True if a character literal was consumed."""
        s, i = self.s, self.i
        j = i + 1
        if j < self.n and s[j] == "\\":
            k = j + 1
            if k < self.n and s[k] in "\\\"'ntr":
                k += 1
            elif k < self.n and s[k] == "x":
                k += 3
            elif k < self.n and s[k] == "u":
                k += 5
            else:
                return False
            if k < self.n and s[k] == "'":
                self.adv(k + 1 - i)
                return True
            return False
        if j + 1 < self.n and s[j] != "\n" and s[j + 1] == "'":
            self.adv(2 + 1)
            return True
        return False

    def prev_code(self, k=1):
        cnt = 0
        for t in reversed(self.toks):
            if not t.in_string:
                cnt += 1
                if cnt == k:
                    return t
        return None

    def string_is_interpolated(self):
        p = self.prev_code()
        if p is None:
            return False
        if p.kind == "ident" and p.text in INTERP_HEADS:
            return True
        if p.kind == "sym" and p.text == "]":
            # trace[cls] "..", aesop_trace![opt] ".."
            depth = 0
            for t in reversed(self.toks):
                if t.in_string:
                    continue
                if t.kind == "sym" and t.text == "]":
                    depth += 1
                elif t.kind == "sym" and t.text == "[":
                    depth -= 1
                    if depth == 0:
                        idx = self.toks.index(t)
                        prev = [x for x in self.toks[:idx] if not x.in_string]
                        return bool(prev) and prev[-1].kind == "ident" and prev[-1].text in INTERP_BRACKET_HEADS
            return False
        # throwErrorAt ref "..", logNamedError id ".." : head two code tokens back
        p2 = self.prev_code(2)
        return p2 is not None and p2.kind == "ident" and p2.text in INTERP_HEADS

    def number(self):
        s, i = self.s, self.i
        j = i
        if s.startswith(("0x", "0X", "0b", "0B", "0o", "0O"), i):
            j = i + 2
            while j < self.n and (s[j].isalnum() or s[j] == "_"):
                j += 1
        else:
            while j < self.n and (s[j].isdigit() or s[j] == "_"):
                j += 1
            if j + 1 < self.n and s[j] == "." and s[j + 1].isdigit():
                j += 1
                while j < self.n and s[j].isdigit():
                    j += 1
            if j < self.n and s[j] in "eE":
                k = j + 1
                if k < self.n and s[k] in "+-":
                    k += 1
                if k < self.n and s[k].isdigit():
                    j = k
                    while j < self.n and s[j].isdigit():
                        j += 1
        text = s[i:j]
        self.emit("num", text, self.line)
        self.adv(j - i)

    def lex(self, stop_at_brace=False):
        depth = 0
        while self.i < self.n:
            c = self.peek()
            line = self.line
            if c.isspace():
                self.adv()
            elif self.s.startswith("--", self.i):
                j = self.s.find("\n", self.i)
                self.adv((self.n if j < 0 else j) - self.i)
            elif self.s.startswith("/-", self.i):
                self.block_comment()
            elif c == '"':
                if self.string_is_interpolated():
                    self.interp_string(line)
                else:
                    self.string_words(self.plain_string(line), line)
            elif c == "r" and (self.peek(1) == '"' or (self.peek(1) == "#" and re.match(r'#+"', self.s[self.i + 1:self.i + 40]))):
                self.raw_string(line)
            elif c == "'" and self.char_literal():
                self.emit("char", "'", line)
            elif id_first(c) or c == "«":
                self.emit("ident", self.ident(), line)
            elif c == "#" and (id_first(self.peek(1)) or self.peek(1) == "«"):
                self.adv()
                self.emit("hash", "#" + self.ident(), line)
            elif c.isdigit():
                self.number()
            elif self.s.startswith("@[", self.i):
                self.emit("sym", "@[", line)
                self.adv(2)
            else:
                if stop_at_brace:
                    if c == "{":
                        depth += 1
                    elif c == "}":
                        if depth == 0:
                            return
                        depth -= 1
                self.emit("sym", c, line)
                self.adv()


def normalize(name):
    return name.replace("«", "").replace("»", "")


def tokenize(src):
    lx = Lexer(src)
    lx.lex()
    return lx.toks, lx.errors


# --------------------------------------------------------------------------------------------
# Rules
# --------------------------------------------------------------------------------------------

KEYWORDS = {  # exact identifier/keyword -> category
    "admit": "admit",
    "axiom": "axiom declaration",
    "native_decide": "native_decide",
    "bv_decide": "bv_decide",
    "implemented_by": "implemented_by",
    "extern": "@[extern]",
    "unsafe": "unsafe",
    "opaque": "opaque",
    "run_cmd": "run_cmd/run_elab/run_meta",
    "run_elab": "run_cmd/run_elab/run_meta",
    "run_meta": "run_cmd/run_elab/run_meta",
    "run_tac": "run_tac/by_elab",
    "by_elab": "run_tac/by_elab",
    "meta": "meta (module-system meta def/import)",
    # `partial def` compiles to `._unsafe_rec` constants of safety `partial`, which the kernel
    # cannot check: `Environment.replay` (FinalCheck, leanchecker, comparator) skips them BY
    # DESIGN, so anything using one fails replay, and the safe wrapper carries @[implemented_by]
    # (trust2.fable §4.3). Structural/well-founded recursion is kernel-checked; use that.
    "partial": "partial def (not kernel-replayable)",
}
META_COMMANDS = {"elab", "elab_rules", "macro", "macro_rules", "syntax", "declare_syntax_cat",
                 "initialize", "builtin_initialize", "simproc", "simproc_decl", "dsimproc",
                 "dsimproc_decl", "builtin_simproc", "builtin_simproc_decl", "builtin_dsimproc",
                 "builtin_dsimproc_decl", "register_option", "register_builtin_option",
                 "register_simp_attr", "declare_simp_like_tactic", "binder_predicate",
                 "declare_config_elab", "register_linter_set", "register_tactic_tag",
                 "elab_stx_quot", "grind_propagator", "builtin_grind_propagator"}
COMPONENT_RULES = {  # any dotted component -> category
    "native": "decide +native / native config",
    "ofReduceBool": "ofReduceBool/ofReduceNat/trustCompiler",
    "ofReduceNat": "ofReduceBool/ofReduceNat/trustCompiler",
    "reduceBool": "ofReduceBool/ofReduceNat/trustCompiler",
    "reduceNat": "ofReduceBool/ofReduceNat/trustCompiler",
    "trustCompiler": "ofReduceBool/ofReduceNat/trustCompiler",
    "modifyEnv": "environment mutation",
    "setEnv": "environment mutation",
    "addAndCompile": "addDecl (kernel/environment API)",
}
META_IDENTS = {"Elab", "CommandElabM", "TermElabM", "TacticM", "MetaM", "CoreM", "MacroM",
               "CommandElab", "TermElab", "liftCoreM", "liftTermElabM", "liftMetaM",
               "liftMetaTactic", "liftMetaTacticAux", "liftCommandElabM", "runTermElabM",
               "withOptions", "evalExpr", "evalDecl", "evalConst", "evalTerm", "unsafeIO",
               "unsafeBaseIO", "unsafeEIO", "IO", "EIO", "BaseIO", "getEnv", "Environment",
               "compileDecl", "compileDecls", "ConstantInfo", "Declaration", "thmDecl",
               "defnDecl", "axiomDecl", "opaqueDecl", "Syntax", "TSyntax", "ParserDescr",
               "TrailingParserDescr", "throwError", "logInfo", "withoutModifyingEnv",
               "mkConst", "instantiateLevelParams", "dbgTrace", "dbg_trace", "println!",
               "evalTactic", "elabTerm", "elabCommand"}  # not `Kernel` (ProbabilityTheory.Kernel)
META_PREFIXES = ("Lean.Elab", "Lean.Meta", "Lean.Parser", "Lean.Syntax", "Lean.Kernel",
                 "Lean.Environment", "Lean.Compiler", "Lean.IR", "Lean.Server", "Lean.Widget",
                 "Lean.PrettyPrinter", "Lean.Macro", "Lean.Core", "Meta.")
BAD_HASH = {"#eval": "#eval", "#eval!": "#eval", "#guard": "#guard", "#exec": "#eval"}
BAD_ATTRS = {"command_elab", "term_elab", "tactic", "csimp", "init", "macro", "delab",
             "app_unexpander", "export", "implemented_by", "extern", "simproc", "sevalproc",
             "env_linter", "code_action_provider", "command_code_action", "hole_code_action",
             "widget_module", "server_rpc_method", "norm_num", "positivity", "incremental",
             "run_builtin_parser_attribute_hooks", "doElem_parser", "command_parser",
             "term_parser", "tactic_parser", "cbv_simproc", "inductive_elab", "grind_propagator"}
# `<keyword> <name>` declares or opens `<name>`: no project file may declare anything in (or open
# a namespace with) an `Erdos184` component (trust review attacks B0/C: a fake or shadowing
# `Erdos184.erdos_184`). EG/EGTest may not mention `Erdos184` at all.
DECL_KEYWORDS = {"theorem", "lemma", "def", "abbrev", "instance", "structure", "class", "inductive",
                 "opaque", "axiom", "alias", "namespace", "section", "noncomputable", "irreducible_def",
                 "export"}
NOTATION_CMDS = {"notation", "notation3", "infix", "infixl", "infixr", "prefix", "postfix"}
OPTION_ALLOW_PREFIX = ("synthInstance.", "linter.", "pp.")
MAX_HEARTBEATS = 1_000_000
RELEASE_ONLY = {"sorry": "sorry", "sorryAx": "sorry"}

# Files allowed to use specific categories (the final check's syntactic type comparison).
ALLOW = {"EGCheck/Final.lean": {"run_cmd/run_elab/run_meta", "meta-programming identifier"}}
# Directories where `#guard` is allowed (unit tests).
GUARD_OK = ("EGTest/", "EGTest.lean")


def parse_nat(text):
    if not re.fullmatch(r"(0|[1-9][0-9_]*)", text):
        return None
    return int(text.replace("_", ""))


def check_tokens(rel, toks, release):
    """Yield (line, category, detail)."""
    in_egcheck = rel.startswith("EGCheck")
    code = [t for t in toks if not t.in_string]
    for t in toks:
        if t.kind == "ident":
            name = t.text
            comps = name.split(".")
            if "Erdos184" in comps and not in_egcheck and not t.in_string:
                yield t.line, "reserved upstream name", name
            if name in KEYWORDS:
                yield t.line, KEYWORDS[name], name
            if name in META_COMMANDS:
                yield t.line, "meta-programming command", name
            for c in comps:
                if c in COMPONENT_RULES:
                    yield t.line, COMPONENT_RULES[c], name
                if c.startswith("addDecl"):
                    yield t.line, "addDecl (kernel/environment API)", name
                if "skipkerneltc" in c.lower():
                    yield t.line, "skipKernelTC", name
            if name == "debug" or name.startswith("debug."):
                yield t.line, "debug.* option", name
            if any(c in META_IDENTS for c in comps) or name.startswith(META_PREFIXES):
                yield t.line, "meta-programming identifier", name
            if release and name in RELEASE_ONLY:
                yield t.line, RELEASE_ONLY[name], name
        elif t.kind == "hash":
            if t.text in BAD_HASH:
                if t.text == "#guard" and (rel.startswith(GUARD_OK)):
                    continue
                yield t.line, BAD_HASH[t.text], t.text
    # context rules on code tokens
    for k, t in enumerate(code):
        nxt = code[k + 1] if k + 1 < len(code) else None
        prv = code[k - 1] if k > 0 else None
        if t.kind == "ident" and t.text == "set_option":
            if nxt is None or nxt.kind != "ident":
                yield t.line, "set_option not in allowlist", "unparsable set_option"
                continue
            opt = nxt.text
            val = code[k + 2] if k + 2 < len(code) else None
            vtext = val.text if val is not None else ""
            if opt.endswith("maxHeartbeats") and (opt == "maxHeartbeats" or opt.startswith(OPTION_ALLOW_PREFIX)):
                n = parse_nat(vtext) if val is not None and val.kind == "num" else None
                if n is None or not (0 < n <= MAX_HEARTBEATS):
                    yield t.line, "set_option not in allowlist", f"{opt} {vtext} (need 0 < N <= {MAX_HEARTBEATS})"
            elif opt == "maxRecDepth" or opt.startswith(OPTION_ALLOW_PREFIX):
                pass
            else:
                yield t.line, "set_option not in allowlist", f"{opt} {vtext}"
        elif (t.kind == "sym" and t.text == "@[") or (
                t.kind == "ident" and t.text == "attribute" and nxt is not None and nxt.text == "["):
            j = k + 1 if t.text == "@[" else k + 2
            depth, seg_start = 0, True
            while j < len(code):
                u = code[j]
                if u.kind == "sym" and u.text in "[(":
                    depth += 1
                elif u.kind == "sym" and u.text in ")]":
                    if depth == 0:
                        break
                    depth -= 1
                elif u.kind == "sym" and u.text == "," and depth == 0:
                    seg_start = True
                    j += 1
                    continue
                if seg_start and depth == 0:
                    if u.kind == "ident" and u.text in ("local", "scoped"):
                        j += 1
                        continue
                    if u.kind == "sym" and u.text == "-":
                        j += 1
                        continue
                    seg_start = False
                    if u.kind == "ident":
                        a = u.text
                        if (a in BAD_ATTRS or a.startswith("builtin_") or a.endswith("_elab")
                                or a.endswith("_parser") or a.endswith("_elab_attribute")):
                            yield u.line, "meta attribute", f"@[{a}]"
                j += 1
        elif t.kind == "ident" and t.text in NOTATION_CMDS:
            loc = prv is not None and prv.kind == "ident" and prv.text == "local"
            yield t.line, "notation", t.text if loc else f"{t.text} (non-local: can take over syntax used by EGCheck/Final.lean)"
        elif t.kind == "ident" and t.text in DECL_KEYWORDS and nxt is not None and nxt.kind == "ident":
            if "Erdos184" in nxt.text.split("."):
                yield nxt.line, "reserved upstream name", f"{t.text} {nxt.text}"
        elif t.kind == "ident" and t.text == "import":
            j = k + 1
            if j < len(code) and code[j].kind == "ident" and code[j].text == "all":
                j += 1
            if j < len(code) and code[j].kind == "ident":
                mod = code[j].text
                if mod.startswith("FormalConjectures") and not in_egcheck:
                    yield t.line, "FormalConjectures import outside EGCheck", mod


def lint_source(rel, src, release):
    toks, errors = tokenize(src)
    findings = [(ln, "tokenizer", msg) for ln, msg in errors]
    allowed = ALLOW.get(rel, set())
    for ln, cat, detail in check_tokens(rel, toks, release):
        if cat not in allowed:
            findings.append((ln, cat, detail))
    return sorted(set(findings))


def files():
    for f in ROOT_FILES:
        if os.path.exists(os.path.join(ROOT, f)):
            yield f
    for d in DIRS:
        for dirpath, dirnames, fs in os.walk(os.path.join(ROOT, d)):
            dirnames.sort()
            for f in sorted(fs):
                if f.endswith(".lean"):
                    yield os.path.relpath(os.path.join(dirpath, f), ROOT)


# --------------------------------------------------------------------------------------------
# Self-test: each case is (file path, Lean source, set of categories expected).
# --------------------------------------------------------------------------------------------

SELF_TESTS = [
    # L1: a character literal must not start a string
    ("EG/T.lean", "def q : Char := '\"'\naxiom EGX.bad : False\ntheorem t : True := by native_decide\n"
     "set_option debug.skipKernelTC true\ndef r : String := \"x\"\n",
     {"axiom declaration", "native_decide", "debug.* option", "skipKernelTC", "set_option not in allowlist"}),
    ("EG/T.lean", "def q : Char := '\\''\naxiom a : False\n", {"axiom declaration"}),
    # L2: axiom at end of line / after attribute
    ("EG/T.lean", "axiom\n  bad : False\n", {"axiom declaration"}),
    ("EG/T.lean", "@[simp]axiom bad2 : (1:Nat) = 1\n", {"axiom declaration"}),
    ("EG/T.lean", "private axiom p : False\n", {"axiom declaration"}),
    # L3/L4: «» spellings
    ("EG/T.lean", "set_option «debug».skipKernelTC true in\ntheorem x : True := trivial\n",
     {"debug.* option", "skipKernelTC", "set_option not in allowlist"}),
    ("EG/T.lean", "set_option «maxHeartbeats» 0 in\ntheorem x : True := trivial\n", {"set_option not in allowlist"}),
    ("EG/T.lean", "set_option maxHeartbeats 00 in\ntheorem x : True := trivial\n", {"set_option not in allowlist"}),
    ("EG/T.lean", "set_option maxHeartbeats 2000000 in\ntheorem x : True := trivial\n", {"set_option not in allowlist"}),
    ("EG/T.lean", "set_option synthInstance.maxHeartbeats 0 in\ntheorem x : True := trivial\n", {"set_option not in allowlist"}),
    ("EG/T.lean", "set_option backward.isDefEq.lazyWhnfCore false\n", {"set_option not in allowlist"}),
    # option name assembled from strings
    ("EG/T.lean", "def n := Lean.Name.mkStr (.mkSimple \"debug\") \"skipKernelTC\"\n",
     {"skipKernelTC", "debug.* option"}),
    # L5: code-running constructs
    ("EG/T.lean", "#eval IO.FS.writeFile \"/tmp/x\" \"y\"\n", {"#eval", "meta-programming identifier"}),
    ("EG/T.lean", "#eval! (1 : Nat)\n", {"#eval"}),
    ("EG/T.lean", "#guard 1 + 1 == 2\n", {"#guard"}),
    ("EGTest/T.lean", "#guard 1 + 1 == 2\n", set()),
    ("EGTest/T.lean", "#eval 1 + 1\n", {"#eval"}),
    ("EG/T.lean", "theorem t : True := by\n  run_tac do\n    pure ()\n  trivial\n", {"run_tac/by_elab"}),
    ("EG/T.lean", "theorem t : True := by_elab do return default\n", {"run_tac/by_elab"}),
    ("EG/T.lean", "elab \"x\" : command => pure ()\n", {"meta-programming command"}),
    ("EG/T.lean", "macro \"close_it\" : tactic => `(tactic| exact sorryAx _ false)\n", {"meta-programming command"}),
    ("EG/T.lean", "macro_rules | `(foo) => `(bar)\n", {"meta-programming command"}),
    ("EG/T.lean", "syntax \"foo\" : term\n", {"meta-programming command"}),
    ("EG/T.lean", "initialize r : Nat ← pure 0\n", {"meta-programming command"}),
    ("EG/T.lean", "builtin_initialize pure ()\n", {"meta-programming command"}),
    ("EG/T.lean", "module\npublic meta import Lean\n", {"meta (module-system meta def/import)"}),
    ("EG/T.lean", "meta def f : Nat := 1\n", {"meta (module-system meta def/import)"}),
    ("EG/T.lean", "partial def f (n : Nat) : Nat := f n\n", {"partial def (not kernel-replayable)"}),
    ("EGCheck/T.lean", "private partial def g : Nat → Nat\n  | n => g n\n",
     {"partial def (not kernel-replayable)"}),
    ("EG/T.lean", "/-- the image of the partial products -/\ntheorem t : True := trivial\n", set()),
    ("EG/T.lean", "@[command_elab Lean.runCmd] def h : Nat := 0\n", {"meta attribute"}),
    ("EG/T.lean", "@[simp, term_elab foo] def h : Nat := 0\n", {"meta attribute"}),
    ("EG/T.lean", "@[scoped macro foo] def h : Nat := 0\n", {"meta attribute", "meta-programming command"}),
    ("EG/T.lean", "attribute [csimp] foo_eq\n", {"meta attribute"}),
    ("EG/T.lean", "attribute [local init] foo\n", {"meta attribute"}),
    ("EG/T.lean", "@[tactic foo] def h : Nat := 0\n", {"meta attribute"}),
    ("EG/T.lean", "open Lean Elab Command in\nrun_cmd pure ()\n",
     {"run_cmd/run_elab/run_meta", "meta-programming identifier"}),
    ("EG/T.lean", "def x := addDecl d\n", {"addDecl (kernel/environment API)"}),
    ("EG/T.lean", "def x := s.modify fun s => { s with env := e }\ndef y := withOptions id\n",
     {"meta-programming identifier"}),
    ("EG/T.lean", "theorem t : True := by decide +native\n", {"decide +native / native config"}),
    ("EG/T.lean", "theorem t : True := by decide (config := { native := true })\n",
     {"decide +native / native config"}),
    ("EG/T.lean", "instance (priority := high) : MonadEnv CommandElabM := sorry\n", {"meta-programming identifier"}),
    # interpolated strings: `{}` is code
    ("EGTest/T.lean", "def s := s!\"{show True by run_tac pure (); trivial}\"\n", {"run_tac/by_elab"}),
    ("EGTest/T.lean", "def s := s!\"a{f \"}\"}b\"\naxiom z : False\n", {"axiom declaration"}),
    # raw strings
    ("EG/T.lean", "def s := r#\"a \" b\"#\naxiom z : False\n", {"axiom declaration"}),
    # nested comments hide nothing after they close
    ("EG/T.lean", "/- a /- b -/ c -/ axiom z : False\n", {"axiom declaration"}),
    ("EG/T.lean", "/- a /- b -/ axiom c -/ theorem t : True := trivial\n", set()),
    # L6: imports anywhere
    ("EG/T.lean", "module\npublic import Mathlib.Logic.Basic\npublic import «FormalConjectures».ErdosProblems.«184»\n",
     {"FormalConjectures import outside EGCheck"}),
    ("EG/T.lean", "import Mathlib.Logic.Basic import FormalConjectures.Util\n", {"FormalConjectures import outside EGCheck"}),
    ("EG/T.lean", "import\n  FormalConjectures.Util\n", {"FormalConjectures import outside EGCheck"}),
    ("EGCheck/T.lean", "import FormalConjectures.ErdosProblems.«184»\n", set()),
    # reserved upstream names (attack C, B0)
    ("EGCheck/T.lean", "import Mathlib.Analysis.SpecialFunctions.Exp\ntheorem Erdos184.erdos_184.{u} : ∀ (_ : PUnit.{u+1}), 0 < Real.exp 0 := fun _ => Real.exp_pos 0\n",
     {"reserved upstream name"}),
    ("EGCheck/T.lean", "theorem EGCheck.Erdos184.erdos_184 : True := trivial\n", {"reserved upstream name"}),
    ("EGCheck/T.lean", "namespace Erdos184\ntheorem erdos_184 : True := trivial\nend Erdos184\n", {"reserved upstream name"}),
    ("EGCheck/T.lean", "theorem EGCheck.Bridge.solution : type_of% @Erdos184.erdos_184 := sorry\n", set()),
    ("EG/T.lean", "theorem x : True := by have := @Erdos184.erdos_184; trivial\n", {"reserved upstream name"}),
    # no notation (local notation still leaves meta constants, see MetaScan)
    ("EG/T.lean", "notation:max (priority := high) \"type_of%\" x => x\n", {"notation"}),
    ("EG/T.lean", "scoped[Lean] infixl:65 \" +' \" => HAdd.hAdd\n", {"notation"}),
    ("EG/T.lean", "local notation \"‖\" x \"‖\" => abs x\n", {"notation"}),
    # release-only
    ("EG/T.lean", "theorem t : False := sorryAx _ false\n", set()),
    # benign constructs: no findings
    ("EG/T.lean", "module\npublic import Mathlib.Logic.Basic\n/-! doc: axiom sorry #eval run_tac -/\n"
     "@[expose] public section\nnamespace EG\n-- axiom in a comment\n"
     "theorem t (h' : 1 = 1) (c' : Nat) : c' = c' := by\n  obtain ⟨w', hw'W⟩ := (⟨0, rfl⟩ : ∃ x : Nat, x = x)\n"
     "  exact rfl\n@[simp, ext] theorem u : True := trivial\nattribute [local simp] Nat.add_comm\n"
     "set_option maxHeartbeats 400000 in\ntheorem v : True := trivial\nset_option linter.unusedVariables false\n"
     "set_option pp.all true\nset_option maxRecDepth 2000\ndef ch : Char := 'a'\ndef s : String := \"-- /- not a comment\"\n"
     "theorem card (s : Finset Nat) : #s = s.card := rfl\n#check t\n#print axioms t\nend EG\n", set()),
]


def self_test():
    bad = 0
    for idx, (rel, src, want) in enumerate(SELF_TESTS):
        got = {cat for _, cat, _ in lint_source(rel, src, release=False)}
        if got != want:
            bad += 1
            print(f"self-test {idx} ({rel}): want {sorted(want)} got {sorted(got)}\n  {src!r}")
    rel_src = "theorem t : False := sorryAx _ false\ntheorem u : False := sorry\n"
    got = {cat for _, cat, _ in lint_source("EG/T.lean", rel_src, release=True)}
    if got != {"sorry"}:
        bad += 1
        print(f"self-test release: got {sorted(got)}")
    print(f"lint self-test: {len(SELF_TESTS) + 1 - bad}/{len(SELF_TESTS) + 1} passed")
    return bad == 0


def main():
    args = sys.argv[1:]
    if "--self-test" in args:
        sys.exit(0 if self_test() else 1)
    release = "--release" in args
    targets = [a for a in args if not a.startswith("--")] or list(files())
    bad = 0
    for rel in targets:
        with open(os.path.join(ROOT, rel), encoding="utf-8") as fh:
            src = fh.read()
        for ln, cat, detail in lint_source(rel, src, release):
            print(f"{rel}:{ln}: forbidden {cat}: {detail[:100]}")
            bad += 1
    mode = "release" if release else "development"
    print(f"lint ({mode}): {bad} findings")
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
