# Clean-room review of the s2a Specs (lens: fidelity-first, model A)

Reviewed: `work/p2s/s2a.md`; new Spec modules `EG/Spec/HB/HS.lean`, `EG/Spec/HB/CapRound.lean`,
`EG/Spec/HB/HBtpFacts.lean`; test `EGTest/Spec_s2a.lean`; against `proofs/manuscript/s2.tex`
lines 503–783 (s2:defHBtp, s2:defAncestors, s2:lemCap, s2:lemHS, and the consumer
s2:propStructure (i)–(iii)). Defs read: `EG/Defs/HB/Round.lean`, `Run.lean`, `SplitTree.lean`
(`IsTauRun`, `graft`), `EG/Defs/Expander.lean`, `EG/Defs/Graph.lean` (`induce`, `deleteVerts`,
`nbrs`, `nbrSet`), `EG/Defs/Gamma/Core.lean` (`Gamma2a`). No Lean file edited.

**Verdict: approve.** All 9 new statements are faithful; no vacuity; no hidden hypothesis
(only `Gamma2a` is assumed, never Γ2(b),(c)); lint clean. Remarks below are cosmetic.

## 1. Fidelity (back-translation vs TeX)

### `HSStatement` [s2:lemHS]
TeX: "Let ε'>0 and s≥0, let X be an (ε',s)-expander on a vertex set of size z≥11, let W⊆V(X) with
|W|≤z/2, and suppose every u∈V(X)\W has at most s_W≤s neighbours in W in X. Then X−W is an
(ε'(log z'/log z)², s−s_W)-expander on z':=z−|W| vertices, and ε'(log z'/log z)²≥ε'/2."
Back-translation: for all V, X, W, reals ε', s, s_W with ε'>0, s≥0, |V(X)|≥11, X an
(ε',s)-expander (Def 11, log₂ of |V(X)|), W⊆V(X), |W| ≤ |V(X)|/2 (real), s_W ≤ s, and
|N_X(u)∩W| ≤ s_W for every u∈V(X)\W: (1) |V(X−W)| = |V(X)|−|W| (ℕ, exact since W⊆V(X));
(2) X−W is an (ε'(log₂(|V(X)|−|W|)/log₂|V(X)|)², s−s_W)-expander; (3) ε'/2 ≤ that constant.
Match: quantifiers, strictness (ε'>0 strict, others non-strict), z≥11, log₂, real s, s_W. `X − W`
= `deleteVerts W` = `induce (V(X)\W)` with vertex set `V(X) ∩ (V(X)\W) = V(X)\W`, so Def 11 of
X−W uses log₂ z' with the same z' as the constant. `nbrs u` excludes nothing relevant (u∉W).
Truth in the model: the TeX proof transfers verbatim (FGraph is loopless; `nbrSet` is
`(V\U).filter …`, so W-vertices are excluded exactly as in the TeX; s_W<0 makes the hypothesis
unsatisfiable because V(X)\W ≠ ∅). OK.

### `HSCorStatement` [s2:lemHS] last sentence
TeX: "In particular, if X is a (2^{-5},s)-expander and s_W=s/2, then X−W is a spanning
(2^{-6},s/2)-expander of V(X)\W." Lean keeps the standing hypotheses s≥0, z≥11, W⊆V(X), |W|≤z/2
and the neighbour bound with s_W=s/2; conclusion `V(X−W) = V(X)\W ∧ (X−W).IsExpander 2^{-6}
(s/2)` (CONVENTIONS "spanning expander"). Constants as `(2:ℝ)^(-5:ℤ)`, `(2:ℝ)^(-6:ℤ)`, the same
literals as `Run.ancEps`. Matches the consumer s2:propStructure (i) ("each light X_Z is a
(2^{-6},s_l/2)-expander on the light part Z"; the (L2) bound in G'_l[Z^0] transfers to X^0_Z by
monotonicity, as in the TeX proof). OK.

### `CapRoundStatement` [s2:lemCap] (ii), round level
TeX: "In every round l≤R of a valid HB^tp run, every s=0 piece 𝒫 satisfies |𝒫|≤M_l. Hence every
round-l pre-part has |Z^0|≤M_l; for every round-l part Z (light or standalone) every vertex is
incident with at most M_l−1 edges of E_l(Z); and τ_l≥128 s_l log²|𝒫|, so Lemma s2:lem14tau
applies to the τ-run of every piece with |𝒫|≥P_l."
Back-translation: for every H, choices c, real D_* with D_*≥2^{117}, D_* ≤ d(H)=2|E(H)|/|V(H)| and
`Round.Valid H c`: (1) every piece has |𝒫| ≤ M(d); (2) every pre-part a has |Z^0_a| ≤ M(d) and
deg_{E(a)}(v) ≤ M(d)−1 (ℕ) for every v; (3) 128·s(d)·log₂²|𝒫| ≤ τ(d) (reals) for every piece;
(4) s(d) ≥ 1; (5) every big piece's `c.tauRun q` is `IsTauRun epsC s(d) τ(d)` of the piece.
- "part Z (light or standalone)" ↔ pre-part address a with `Round.E H c a` (E_l of its light part
  if light, of itself if standalone): one part per pre-part. OK.
- "every s=0 piece" in the τ clause is read for all pieces (TeX's 𝒫 is any piece; the proof ends
  "τ_l ≥ 128 s_l log² M_l ≥ 128 s_l log²|𝒫|"). OK; empty or one-vertex pieces give log = 0.
- "so Lemma 14^τ applies" = (3)–(5), which are exactly the hypotheses `1 ≤ s`,
  `128 * (s:ℝ) * logb 2 H.card ^ 2 ≤ τ`, `t.IsTauRun epsC s τ H` of the L14* Specs
  (`EG/Spec/HB/Lemma14Tau.lean`), with H = the piece graph. Checked textually.
- Hypotheses vs TeX context: only Γ2(a) (the proof's only use: "By Γ2(a), d_l ≥ D_* ≥ 2^{117}")
  and the round-local form of "round l ≤ R of a valid run" (`Round.Valid`, `D_* ≤ d_l`). The
  round-level form holds for any H, not only for G_l of a run: strictly stronger than the TeX,
  and the TeX proof is round-local (uses (R1) CyclesValid, (R3) StopsAt at (ε,0), (R2), (R5),
  citLem25 with m ≥ 2^{40} ≥ 2), so it remains true. No Γ2(b),(c). OK.

### `CapRunTauStatement` [s2:lemCap] (ii), last clause, run level
Back-translation: for every G, D_* ≥ 2^{117}, valid run on G with threshold D_*, every round
l∈[1,R]: 128·s_l·log₂²|𝒫_q| ≤ τ_l for all pieces q; s_l ≥ 1; for all big pieces q
(`run.bigPieceAddrs G l`, |𝒫| ≥ P_l), `run.tauRun l q` is a τ-run of `run.piece G l q` with
(ε, s_l, τ_l). Faithful; complements the existing `CapPrePartStatement` (which states the first
three clauses at run level and explicitly omits this one). Reads `tauRun` only at big pieces
(CONVENTIONS). OK.

### `HBMCeilStatement` [s2:defHBtp] (R2)
TeX: "M_l ≥ max(2^{40}, 2^{16} t^HB_l d_l log⁴(t^HB_l d_l)), and M_l ≤ max(…)+1." Lean: for every
real d, with T = `TOf d` = log₂²d·d: max(2^40, 2^16·T·log₂⁴T) ≤ (M(d):ℝ) ≤ max(…)+1. Parse checked
(`Real.logb 2 (TOf d) ^ 4` = (log₂T)^4). Holds for every d (stronger than per round). Proved in
scratch (`Nat.le_ceil`, `Nat.ceil_lt_add_one`). OK.

### `HBTwoLevelStatement` [s2:defHBtp] (R3)
TeX: "Its leaves are the pieces of size less than P_l and the leaves of the τ-runs. The round-l
pre-parts are the leaves of the τ-runs with at least P_l vertices; equivalently, the leaves of
the two-level recursion with at least P_l vertices."
Lean conjuncts (1) leaf addresses of `twoLevel` = small pieces ∪ {q++b : q big, b leaf of
`tauRun q`}; (2) X^0 at a small piece = the piece graph; (3) X^0 at q++b = leaf graph of the
τ-run rooted at the piece; (4) pre-parts (defined by the "equivalently" form) = {q++b : q big,
b leaf of τ-run, |graph| ≥ P}. Faithful to both sentences; "big/small" uses the same test
`POf (d H) ≤ card` as `twoLevel`'s graft function; `graft .nil f = f []` and
`leafAddrs .nil = {[]}` make small pieces q = q ++ [] leaves. No validity hypothesis — correct,
these are structural (Lib already proves the "→" direction of (4):
`Round.exists_tauRun_leaf_of_mem_prePartAddrs`). OK.

### `HBStdStatement` [s2:defHBtp] (R4)
TeX: "Std_l … contains the GC-parts and the pre-parts failing (L1) or (L2)." Lean: pre-part a,
GC-part or ¬L1 or ¬L2 → a ∈ Std. Proved in scratch in 5 lines (definitional). OK.

### `HBStep1Statement` [s2:defHBtp] (R5)(1)
TeX: "(The graphs X^0_Z of distinct pre-parts are edge-disjoint, being distinct leaves of the
two-level recursion, Lemma SEP(i), and X_Z ⊆ X^0_Z; so no edge is assigned twice in this step.)"
Lean (under `Round.Valid`): pairwise edge-disjoint X^0 for distinct pre-part addresses;
E(X_a) ⊆ E(X^0_a) (all a; true by `deleteVerts = induce`); an edge in `partGraph` of two
pre-parts forces equality. The last conjunct is the content of "no edge is assigned twice"
(`assign` itself takes a `find?` and would be well defined anyway, as the Defs note). The
validity hypothesis is needed (SEP (i) requires WF of the grafted tree). Distinctness is by
address, matching (Naming) "distinct pre-parts are counted separately even if their vertex sets
coincide". OK.

### `AncestorFactsStatement` [s2:defAncestors]
Conjuncts (0) ancestors of round r = round-r pre-parts (r a round) [TeX: light part or standalone
pre-part, one per pre-part]; (1) V(Y) ⊆ Y^0; (2) anc_l(x)=∅ for l≤2; (3) F_Z = U_Z for l≤2;
(4) w∈D_r ⟺ μ_r(w)≥2 (all r; both sides trivial outside [1,R]). Faithful to the "so"-claims and
to "Y^0 ⊇ V(Y)". Proved in scratch from existing Lib lemmas (`Run.mem_ancestors`,
`anc_eq_empty_of_le_two`, `fresh_eq_ports_of_le_two`, `mem_D_iff`). OK.

## 2. Vacuity
- HS / HSCor: hypotheses satisfiable (K₁₁, W=∅, s=s_W=0; `EGTest/Spec_s2a.lean`). Conclusions not
  trivially true (Def 11 for X−W is a real content statement).
- `Round.Valid`, `Run.Valid` satisfiable (EGTest.HB). Joint satisfiability with Γ2(a) and
  d ≥ D_* not checked concretely (needs d ≥ 2^{117}); no contradiction is visible: `Round.Valid`
  does not include the Lemma 14^τ hypotheses (HB-VALID-NO-TERMINATION), so it does not presuppose
  what CapRound concludes, and existence is s2:propExists.
- Scratch `/tmp/s2arev/Scratch.lean` (not in repo): `HBMCeilStatement`, `HBStdStatement`,
  `AncestorFactsStatement` proved outright (compiles with 0 errors) — confirms they are true and
  correctly typed; they are definitional, as the status note says, not vacuous.

## 3. Consistency
- Reuse: `IsExpander`, `deleteVerts`, `Round.*`, `Run.*`, `IsTauRun`, `Gamma2a`, `epsC`; no new
  Defs. Γ hypothesis: only `Gamma2a` (Γ2(a)); Γ2(b),(c) never assumed.
- Duplication: `CapRoundStatement` (1)–(2) restate `CapPrePartStatement` at round level —
  intended by TRIAGE §2.2 (round-level Specs with run-level corollaries), and needed by
  s2:propExists; `CapRunTauStatement` fills exactly the clause `CapPrePartStatement` omits. No
  other Spec carries [s2:lemHS] or the (R2)–(R5)/defAncestors claims.
- Consumer forms: CapRunTau/CapRound conclusions match the L14* hypotheses syntactically
  (`(tauOf … : ℝ)`, `sOf … : ℕ`, `Real.logb 2 (piece).card ^ 2`); HSCor matches propStructure (i).

## 4. Hygiene
`python3 -I scripts/lint.py`: 0 findings. Module headers, `@[expose] public section`, docstrings
start with the label and quote the TeX. `.olean`s of the three modules are newer than sources.

## Cosmetic remarks (no change required)
- C1. HS non-vacuity uses only W=∅, s=0; a witness with W≠∅ would exercise the (s−s_W) and z'
  parts, but none is needed for approval.
- C2. `HBMCeil`, `HBStd`, `AncestorFacts` (and HBTwoLevel (4) "→") are one-screen consequences
  of the Defs / existing Lib lemmas; they can be discharged immediately in P3 (scratch proofs
  above).

## Math findings
None. The TeX statements of s2:lemHS, s2:lemCap (ii) and the embedded claims of s2:defHBtp /
s2:defAncestors were re-derived; the HS proof (edge count |E_X(U,W)| ≤ s_W|U|, z' ≥ z/2 ≥ 5.5,
z ≥ 10.67 ⇒ (log z'/log z)² ≥ 1/2) and the cap argument check out.
