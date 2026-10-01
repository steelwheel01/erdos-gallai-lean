# Clean-room review, round 2: Fact EG0 (s1:factEG0), task [eg0]

Reviewer: clean-room agent (round 2), 2026-09-26. Files reviewed (not edited):
`EG/Spec/Found/EG0.lean` (statements), `EG/Proof/Found/EG0.lean` (523 lines, proofs), author notes
`work/ext/eg0.md`, round-1 review `work/ext/eg0.review1.md`. Both Lean files are unchanged since
round 1 (`git status` clean; last commit 933730e). Manuscript: `proofs/manuscript/s1.tex`
l. 635–708; CONVENTIONS.md (T0-eg0-loop); blueprint_s1.md entry `s1:factEG0` (l. 354–395).

**Verdict: APPROVE.** No fidelity, non-vacuity, proof or hygiene issue. Two cosmetic notes for the
integrator (§5).

## 1. Fidelity of the Spec to the manuscript

Manuscript (s1.tex l. 636–645), quoted:
> (a) Every graph $H$ with $h\ge1$ vertices has a decomposition into at most $h(\log h+1)$ objects,
> at most $h-1$ of which are single edges. In particular $\f(H)\le h(\log h+1)$.
> (b) Let $N>1$ and $L\defeq\log N$, and let $\alpha$ and $\beta$ be real numbers with
> $0\le\alpha\le N$, $\beta>0$ and $4\beta\le L$. If $F$ is the edge set of a (simple) graph, so that
> $F$ has no loops and no parallel edges, and every edge of $F$ has both ends in a set $W$ with
> $|W|\le\beta\alpha/L$, then $F$ has a decomposition into at most $\beta\alpha$ objects, at most
> $|W|$ of which are single edges.

Checked clause by clause against `FactEG0aStatement`, `FactEG0aFnumStatement`, `FactEG0bStatement`:

| Manuscript | Spec | OK |
|---|---|---|
| graph $H$ (simple, s1:convGraphs(a)), $h=\lvert V(H)\rvert\ge1$ | `H : EG.FGraph V` (loopless `Finset (Sym2 V)` edges, ends in `verts`), `1 ≤ H.card` (`card := verts.card`) | yes |
| $\log=\log_2$ (s1:convGraphs(b)) | `Real.logb 2` | yes |
| decomposition of $E(H)$ | `EG.IsDecomp (H.edges : Set _) D`: WF objects (edge not a loop; cycle nodup, length ≥ 3), edge lists nodup, exactly the edges of `E` | yes |
| at most $h(\log h+1)$ objects | `(D.length : ℝ) ≤ H.card * (logb 2 H.card + 1)` | yes |
| at most $h-1$ single edges | `D.countP (fun o => o matches .edge _) ≤ H.card - 1`; ℕ-subtraction harmless because `1 ≤ H.card` | yes |
| $\f(H)\le h(\log h+1)$ | `(EG.fnum H.edges : ℝ) ≤ …`; `H.edges` is loopless, so `fnum` is the manuscript $\f$ (CONVENTIONS) | yes |
| $N>1$, $L=\log N$ | `1 < N`, `Real.logb 2 N` (positive) | yes |
| $0\le\alpha\le N$, $\beta>0$, $4\beta\le L$ | `0 ≤ α`, `α ≤ N`, `0 < β`, `4 * β ≤ Real.logb 2 N` | yes |
| $F$ edge set of a simple graph (no loops, no parallel edges) | `F : Finset (Sym2 V)`, `∀ e ∈ F, ¬ e.IsDiag` (a `Finset` has no parallel edges) — recorded decision T0-eg0-loop | yes |
| every edge of $F$ has both ends in $W$ | `W : Finset V`, `∀ e ∈ F, ∀ v ∈ e, v ∈ W`; `W` not tied to a graph, as in the text | yes |
| $\lvert W\rvert\le\beta\alpha/L$ | `(W.card : ℝ) ≤ β * α / Real.logb 2 N` | yes |
| at most $\beta\alpha$ objects, at most $\lvert W\rvert$ single edges | `(D.length : ℝ) ≤ β * α`, `countP … ≤ W.card` | yes |

* Constants: `4`, `1`, `2` (base) all as in the text; no slack introduced, no hypothesis added
  beyond the T0 decision, no conclusion weakened (both single-edge counts kept; they are used by
  s4:thmVXp).
* Edge cases: $h=1$ gives bound $1\cdot(0+1)=1$ objects and $0$ single edges; $W=\emptyset$ forces
  $F=\emptyset$; $\alpha=0$ forces $W=\emptyset$ and the bound $0$ — all consistent with the
  manuscript's proof of (b). Universe-polymorphic `V : Type u`, arbitrary `DecidableEq V`.
* `IsDecomp` is the Defs notion (s1:defObject) — a cycle object requires `c.Nodup ∧ 3 ≤ c.length`,
  matching "cycle (of length at least 3)".

## 2. Non-vacuity (scratch file, compiled with `lake env lean`;
`/tmp/claude-0/.../scratchpad/eg0rev2/T.lean`, not part of the project)

All of the following compile without error:
* (a) on the triangle (`Fin 3`): hypothesis discharged by `decide`; conclusion with bound
  `3 (log₂ 3 + 1)` and `≤ 2` single edges.
* (a) on $K_4$: the returned decomposition has `≤ 3` single edges while there are 6 edges, and from
  that I derived in Lean `∃ c, Obj.cycle c ∈ D` — so the single-edge clause genuinely forces a
  cycle object (it is not satisfiable by the all-single-edges decomposition).
* (a) on one vertex ($h=1$): `D.length ≤ 1 * (logb 2 1 + 1)`, `0` single edges.
* (a) f-form on the triangle.
* (b) on the triangle with $N=256$ ($L=8$), $\alpha=256$, $\beta=2$, $W=$ `univ` ($3\le64$): every
  hypothesis discharged (`norm_num`, `logb 2 256 = 8`), conclusion obtained.
* (b) with $W=\emptyset$, $F=\emptyset$, $\alpha=0$: hypotheses hold, conclusion `D.length ≤ 0`.
* The loop hypothesis is necessary: `{s(0,0)}` on `Fin 1` has no `IsDecomp` at all (proved).
* `#print axioms`: `EG.factEG0a`, `EG.factEG0aFnum`, `EG.factEG0b` each depend on
  `[propext, Classical.choice, Quot.sound]` only.

## 3. The proof proves exactly the Spec

`theorem factEG0a : EG.Spec.FactEG0aStatement.{u}`, `factEG0aFnum : FactEG0aFnumStatement.{u}`,
`factEG0b : FactEG0bStatement.{u}` — the Spec constants themselves, no restatement, no extra
hypotheses (the module has no `variable` assumptions in scope of these theorems). I re-read the
whole proof against s1.tex:
* `exists_core` = the peeling ("delete a vertex of degree ≤ d−1 as long as one exists; not all
  vertices go since $m'\le(h-1)(d-1)<m'$"), as induction on `|S|` with invariant
  `(|S|−1)(d−1) < e(H[S])` via `card_induce_edges_le_erase`. The `S = {v}` case correctly uses
  looplessness (no edge inside a singleton).
* `exists_long_cycle_of_deg` = the longest-path closing ("largest index $i$ with $v_0v_i\in E$,
  $i\ge d$"): all neighbours of `v₀` lie on the path (else extend), they lie in the prefix ending at
  the last neighbour minus `v₀`, so the cycle has ≥ d+1 vertices; `cycleEdges_subset_of_chain`
  puts its edges in `E(G)`.
* `exists_cycle_of_card_le` = the Claim, in the strict form `m' < h·ℓ`, with
  `d = max(2, ⌊m'/h⌋)` (the author's documented departure from `⌈m'/h⌉`; the peeling hypothesis
  `(h−1)(d−1) < m'` is checked in both branches, and `ℓ ≥ d+1 ≥ ⌊m'/h⌋+1` gives `m' < hℓ`). Correct.
* `block` (`j` removals, `|E'| < h` or `|E'| ≤ (1−1/h)^j|E|`) and `decomp_of_card_lt`
  (`|E| < 2^q h` ⇒ `≤ qh` cycles + `≤ h−1` single edges, using `(1−1/h)^h ≤ e^{-1} ≤ 1/2`) are the
  manuscript's "removal of long cycles" and its count `t ≤ (q+1)h`, reorganised by induction on
  `q`; `exists_decomp_log` fixes `q = ⌊log₂ h⌋` and uses `|E| < C(h+1,2) ≤ 2^q h` (from
  `E ⊊ W.sym2`) in place of `m ≤ h²/2`. The final bound `qh + h − 1 ≤ h log₂ h + h` uses
  `Nat.log 2 h ≤ logb 2 h` (`Real.natLog_le_logb`).
* `factEG0b` follows the text exactly: `W = ∅ ⇒ F = ∅`; else `h ≤ βα/L ≤ βN/L ≤ N/4`,
  `log₂ h ≤ L − 2`, `h(log h + 1) ≤ h(L−1) ≤ hL ≤ βα`, and `h − 1 ≤ |W|`.
None of the departures (all documented in docstrings and in `eg0.md` §3) changes a statement.

## 4. Hygiene

* `lake build EG.Proof.Found.EG0`: "Build completed successfully (2039 jobs)".
* `lake env lean --run scripts/Axioms.lean --prefix EG EG.Spec.Found.EG0 EG.Proof.Found.EG0`:
  "inspected 559 constants under [EG]; 0 use sorryAx; 0 meta-scan hits; 0 violations".
* `python3 scripts/lint.py`: "0 findings". No `sorry`, no `set_option`, no forbidden token in
  either file.
* Module headers: Spec is `module` + `public import EG.Defs.Fnum / EG.Defs.Graph / Mathlib…` +
  `@[expose] public section` (Defs-only imports, as required for a Spec); Proof is `module` +
  `public section`. Every formalizing declaration has a `[s1:factEG0]` docstring.
* Author notes `work/ext/eg0.md` now exist (round-1 issue 1 resolved) and match the code.

## 5. Issues

1. (cosmetic, integrator; no Lean change required) The Spec docstring says the inlined
   `fun o => o matches .edge _` is "the same as `D.countP EG.Obj.isEdge` of
   `EG/Lib/Found/Fnum.lean`, inlined here so that the statement depends on `EG/Defs` only".
   `Obj.isEdge` has since moved to `EG/Defs/Objects.lean` (P2-D, TRIAGE §2.11), so that reason is
   obsolete. Note that the inlined match is *not* reducibly defeq to `Obj.isEdge`: in my scratch
   tests `exact hcnt` against a goal stated with `Obj.isEdge` fails, and the conversion needs
   `List.countP_congr (fun o _ => by cases o <;> exact Iff.rfl)` (the author's proof does the same).
   Suggested fix (integrator, before locking): either replace the two occurrences by
   `D.countP EG.Obj.isEdge` (the blueprint's lean_shape) so that s4 consumers stating single-edge
   counts with `Obj.isEdge` compose directly, or keep the match and update the docstring.
   Equivalence is settled either way; not a fidelity issue.
2. (cosmetic, integrator) `EG/Spec/Found/EG0.lean` is still absent from `LOCK.json`; blueprint_s1.md
   row `s1:factEG0` still reads "risk (EG0-UNREVIEWED)" and its "Formalization" line names
   `EG/Spec/Ext/EG0.lean`, `EG/Proof/Ext/EG0.lean` (actual paths: `EG/Spec/Found/EG0.lean`,
   `EG/Proof/Found/EG0.lean`). Two clean-room reviews (round 1 and this one) now cover EG0; the
   integrator can lock the Spec and mark the row done.
