# P2 Specs, chunk s2a (s2: witnesses, τ-rules, SEP, thin cut, OV, Lemma 14^τ, HB*^{τ+}, ancestors, size cap, Lemma HS): status

Manuscript v6.1 `proofs/manuscript/s2.tex` lines 1–720 (a CANDIDATE proof, AI-reviewed only).
Blueprint `work/p2/blueprint_s2a.md`, `nodes_s2a.json`; data model TRIAGE §2.1, §2.2 (round-local
API, round-level Specs), §2.12; Defs `EG/Defs/HB/{Witness,SplitTree,Round,Run}.lean` (locked, not
edited).

Result: 3 new Spec modules (9 `…Statement` defs), 1 test file; no new Defs. Most s2a nodes already
had Specs from probes P3A / P2J (τ-rules, SEP, thin cut, OV, Lemma 14^τ, Cap). All new modules
compile (`lake build EG.Spec.HB.HS EG.Spec.HB.CapRound EG.Spec.HB.HBtpFacts`: success);
`scripts/check.sh EGTest/Spec_s2a.lean`: 0 errors, 0 sorry. `python3 -I scripts/lint.py`: 0
findings. No proofs, no stubs, no existing file edited. Root imports to add (I did not edit root
files): `EG.Spec.HB.HS`, `EG.Spec.HB.CapRound`, `EG.Spec.HB.HBtpFacts` to `EG`;
`EGTest.Spec_s2a` to `EGTest`.

## Table: label → Lean name → file → status

All names in namespace `EG.Spec`.

| label | Lean name(s) | file | status |
|---|---|---|---|
| s2:defWitness (Fact; "then `m ≥ 2`"; "a witness exists") | `WitnessExistsStatement`, `WitnessFactStatement` (Defs `IsWitness`, `witN`, `witF0`) | `EG/Spec/HB/TauRules.lean` | existing (P3A) |
| s2:defTauRules (Facts (a)–(c)) | `TauFactAStatement`, `TauFactBStatement`, `TauFactCStatement` | `EG/Spec/HB/TauRules.lean` | existing (P3A) |
| s2:eqSplit | `TauEqSplitStatement` | `EG/Spec/HB/TauRules.lean` | existing (P3A) |
| s2:lemSEP ((0), (0'), (i), (ii), (iii)) | `SEP0Statement`, `SEPMonoStatement`, `SEPiStatement`, `SEPiiStatement`, `SEPiiiStatement` | `EG/Spec/HB/SEP.lean` | existing (P3A) |
| s2:lemThinCut (main; Moreover) | `ThinCutStatement`, `ThinCutEdgeStatement` | `EG/Spec/HB/ThinCut.lean` | existing (P3A) |
| s2:lemOVgeneric ((a)–(c); instance c = 1) | `OVStatement`, `OVInstanceStatement`; numeric helpers `NumOV*Statement` | `EG/Spec/HB/Overlap.lean`, `EG/Spec/Num/OV.lean` | existing (P3A, NUM) |
| s2:lem14tau ((a) local, termination, global; (b); (c),(d)) | `L14SplitStatement`, `L14TermStatement`, `L14GlobalStatement`, `L14OVStatement`, `L14ThinStatement`; `NumLem14tauConstStatement` | `EG/Spec/HB/Lemma14Tau.lean`, `EG/Spec/Num/OV.lean` | existing (P3A, NUM) |
| s2:defHBtp (definition) | Defs `EG.HB.*`, `EG.HB.Round.*`, `EG.HB.Run.*` | `EG/Defs/HB/Round.lean`, `Run.lean` | existing Defs (locked); no Spec of its own |
| s2:defHBtp (embedded claims) | `HBMCeilStatement` ((R2)), `HBTwoLevelStatement` ((R3)), `HBStdStatement` ((R4)), `HBStep1Statement` ((R5)(1)) | `EG/Spec/HB/HBtpFacts.lean` | **new** |
| s2:defAncestors (definition) | Defs `EG.HB.Run.{ancestors, ancVerts, ancGraph, ancEps, ancS, LY, anc, hubs, ports, fresh, classed, mu, dup, mult, j0, j1}` | `EG/Defs/HB/Run.lean`, `Round.lean` | existing Defs (locked) |
| s2:defAncestors (embedded "so"-claims) | `AncestorFactsStatement` | `EG/Spec/HB/HBtpFacts.lean` | **new** |
| s2:lemCap (i) | `CapStatement` | `EG/Spec/HB/Cap.lean` | existing (P1b; proved `EG.cap`) |
| s2:lemCap (Remark) | `CapUniformStatement` | `EG/Spec/HB/Cap.lean` | existing (proved) |
| s2:lemCap (ii), graph step of the proof | `CapGraphStatement` | `EG/Spec/HB/Cap.lean` | existing (proof depends on `EG.bmLemma25`, sorry) |
| s2:lemCap (ii), first three clauses, run level | `CapPrePartStatement` | `EG/Spec/HB/CapPrePart.lean` | existing (P2J declared input) |
| s2:lemCap (ii), all clauses, round level | `CapRoundStatement` | `EG/Spec/HB/CapRound.lean` | **new** |
| s2:lemCap (ii), last clause (`τ_l ≥ 128 s_l log²|𝒫|`, "Lemma 14^τ applies"), run level | `CapRunTauStatement` | `EG/Spec/HB/CapRound.lean` | **new** |
| s2:lemHS | `HSStatement` | `EG/Spec/HB/HS.lean` | **new** |
| s2:lemHS (last sentence, "In particular") | `HSCorStatement` | `EG/Spec/HB/HS.lean` | **new** |

Existing Specs were checked against the TeX for coverage (every clause of every node has a
statement) and skimmed for faithfulness; they have their own two-review records
(`work/p2b/P3A.review{1,2}.md`, `P2J.review{1,2}.md`, `NUM.*`). No problem found. The one gap was
lemCap (ii)'s last clause, which `CapPrePartStatement` deliberately omits (its docstring says so);
it is now `CapRoundStatement` (round level) and `CapRunTauStatement` (run level).

## New Specs: TeX next to a back-translation of the Lean

### `HSStatement` (s2:lemHS)
TeX: "Let `ε'>0` and `s≥0`, let `X` be an `(ε',s)`-expander on a vertex set of size `z≥11`, let
`W⊆V(X)` with `|W|≤z/2`, and suppose every `u∈V(X)\W` has at most `s_W≤s` neighbours in `W` in
`X`. Then `X−W` is an `(ε'(log z'/log z)², s−s_W)`-expander on `z':=z−|W|` vertices, and
`ε'(log z'/log z)² ≥ ε'/2`."
Lean, read back: for every type `V`, graph `X`, finite `W`, reals `ε', s, s_W`: if `ε' > 0`,
`s ≥ 0`, `|V(X)| ≥ 11`, `X` is an `(ε', s)`-expander, `W ⊆ V(X)`, `|W| ≤ |V(X)|/2`, `s_W ≤ s`, and
every `u ∈ V(X) \ W` has `|N_X(u) ∩ W| ≤ s_W`, then (1) `|V(X − W)| = |V(X)| − |W|`, (2) `X − W`
is an `(ε'·(log₂(|V(X)| − |W|)/log₂|V(X)|)², s − s_W)`-expander, (3)
`ε'/2 ≤ ε'·(log₂(|V(X)| − |W|)/log₂|V(X)|)²`.

### `HSCorStatement` (s2:lemHS, last sentence)
TeX: "In particular, if `X` is a `(2^{-5},s)`-expander and `s_W=s/2`, then `X−W` is a spanning
`(2^{-6},s/2)`-expander of `V(X)\W`."
Lean, read back: if `s ≥ 0`, `|V(X)| ≥ 11`, `X` is a `(2^{-5}, s)`-expander, `W ⊆ V(X)`,
`|W| ≤ |V(X)|/2`, and every `u ∈ V(X) \ W` has at most `s/2` neighbours in `W` in `X`, then
`V(X − W) = V(X) \ W` and `X − W` is a `(2^{-6}, s/2)`-expander.

### `CapRoundStatement` (s2:lemCap (ii), round level)
TeX: "In every round `l≤R` of a valid `HB^tp` run, every `s=0` piece `𝒫` satisfies `|𝒫|≤M_l`.
Hence every round-`l` pre-part has `|Z^0|≤M_l`; for every round-`l` part `Z` (light or
standalone) every vertex is incident with at most `M_l−1` edges of `E_l(Z)`; and
`τ_l≥128 s_l log²|𝒫|`, so Lemma s2:lem14tau applies to the `τ`-run of every piece with
`|𝒫|≥P_l`."
Lean, read back: for every graph `H` (the input `G_l` of the round), round choices `c` and real
`D_*` with `D_* ≥ 2^{117}`, `D_* ≤ d(H) = 2|E(H)|/|V(H)|` and `Round.Valid H c`, writing
`d = d(H)`: (1) every piece `q` (leaf of the `s = 0` tree) has `|𝒫_q| ≤ M(d)`; (2) every pre-part
`a` has `|Z^0_a| ≤ M(d)` and every vertex `v` has `deg_{E(a)}(v) ≤ M(d) − 1`; (3) every piece `q`
has `128·s(d)·log₂²|𝒫_q| ≤ τ(d)`; (4) `s(d) ≥ 1`; (5) for every piece with `|𝒫_q| ≥ P(d)`, the
chosen tree `c.tauRun q` is a `τ`-run of `𝒫_q` with parameters `(s(d), τ(d))` and `ε = 2^{-5}`.
((4), (5) and (3) are exactly the hypotheses of the Lemma 14^τ Specs.)

### `CapRunTauStatement` (s2:lemCap (ii), last clause, run level)
TeX: as above, the clause "`τ_l≥128 s_l log²|𝒫|`, so Lemma s2:lem14tau applies to the `τ`-run of
every piece with `|𝒫|≥P_l`".
Lean, read back: for every graph `G`, real `D_* ≥ 2^{117}` and valid run on `G` with threshold
`D_*`, for every round `l ∈ [1, R]`: every piece `q` of round `l` has
`128·s_l·log₂²|𝒫_q| ≤ τ_l`; `s_l ≥ 1`; and for every piece with `|𝒫_q| ≥ P_l` the run's tree
`run.tauRun l q` is a `τ`-run of `𝒫_q` with parameters `(s_l, τ_l)`.

### `HBMCeilStatement` (s2:defHBtp (R2))
TeX: "Besides integrality, only two facts about the ceiling are used:
`M_l≥max(2^{40},2^{16} t^HB_l d_l log⁴(t^HB_l d_l))`, and
`M_l≤max(2^{40},2^{16} t^HB_l d_l log⁴(t^HB_l d_l))+1`."
Lean, read back: for every real `d`, with `T = d·log₂²d`:
`max(2^{40}, 2^{16}·T·log₂⁴T) ≤ M(d) ≤ max(2^{40}, 2^{16}·T·log₂⁴T) + 1` (reals).

### `HBTwoLevelStatement` (s2:defHBtp (R3))
TeX: "The two-level recursion … Its leaves are the pieces of size less than `P_l` and the leaves of
the `τ`-runs. The round-`l` pre-parts are the leaves of the `τ`-runs with at least `P_l` vertices;
equivalently, the leaves of the two-level recursion with at least `P_l` vertices."
Lean, read back: for every graph `H` and round choices `c`: (1) an address is a leaf of the
two-level recursion iff it is a piece with `|𝒫| < P` or it is `q ++ b` for a piece `q` with
`|𝒫_q| ≥ P` and a leaf `b` of `c.tauRun q`; (2) the leaf graph at a small piece is the piece graph;
(3) the leaf graph at `q ++ b` is the graph at `b` of `c.tauRun q` rooted at `𝒫_q`; (4) an address
is a pre-part iff it is `q ++ b` for a big piece `q` and a leaf `b` of its `τ`-run whose graph has
at least `P` vertices.

### `HBStdStatement` (s2:defHBtp (R4))
TeX: "`Std_l` is the set of round-`l` standalone pre-parts; it contains the GC-parts and the
pre-parts failing (L1) or (L2)".
Lean, read back: for every `H`, `c` and pre-part `a`: if `a` is a GC-part, or fails (L1), or fails
(L2), then `a ∈ Std`.

### `HBStep1Statement` (s2:defHBtp (R5)(1))
TeX: "(The graphs `X^0_Z` of distinct pre-parts are edge-disjoint, being distinct leaves of the
two-level recursion, Lemma s2:lemSEP(i), and `X_Z⊆X^0_Z`; so no edge is assigned twice in this
step.)"
Lean, read back: for every valid round `(H, c)`: distinct pre-part addresses have edge-disjoint
`X^0`; `E(X_a) ⊆ E(X^0_a)` for every address; an edge lying in the part graph (`X_a` if light,
`X^0_a` if standalone) of two pre-parts `a`, `b` forces `a = b`.

### `AncestorFactsStatement` (s2:defAncestors)
TeX: "Fix a valid `HB^tp` run. An ancestor of round `r` is either a light part … or a standalone
pre-part … Every ancestor corresponds to a distinct pre-part `Y^0⊇V(Y)` of its round. …
`anc_l(x):=∅` for `l≤2` … (so all ports are fresh for `l≤2`) … `μ_r(w)` is the number of round-`r`
pre-parts containing `w` (so `D_r={w:μ_r(w)≥2}`)".
Lean, read back: for every valid run: (0) `(r, a)` is an ancestor iff `1 ≤ r ≤ R` and `a` is a
round-`r` pre-part; (1) `V(Y) ⊆ Y^0` for every ancestor `Y`; (2) `anc_l(x) = ∅` for `l ≤ 2` and
every `x`; (3) fresh ports = ports for `l ≤ 2`; (4) `w ∈ D_r ⟺ μ_r(w) ≥ 2` for every round index
`r` and vertex `w`.

## Hazards and choices (T0 decisions)

* **HS, `z'`.** The expansion parameter uses the real `z' = |V(X)| − |W|`; the vertex count of
  `X − W` is a separate conjunct (natural numbers, exact as `W ⊆ V(X)`), so Def 11 for `X − W`
  (which uses `log₂|V(X − W)|`) and the TeX's `z'` agree. `s_W` is real and may be any real `≤ s`
  (the TeX notes `s_W ≥ 0` is forced; not a hypothesis).
* **HS corollary constants** are the literals `2^{-5}`, `2^{-6}` (`(2:ℝ)^(-5:ℤ)`, as in
  `Run.ancEps`), not `epsC` (equal by definition). The corollary keeps the lemma's standing
  hypotheses.
* **lemCap (ii) at round level** (TRIAGE §2.2): hypotheses `Gamma2a Dstar`, `Dstar ≤ Round.d H`,
  `Round.Valid H c` (CAP-GAMMA-EXPLICIT: the manuscript's "valid run" hides `Γ2(a)`). "so Lemma
  14^τ applies" is read as the remaining hypotheses of the Lemma 14^τ Specs: `1 ≤ s_l` and the
  `IsTauRun` field (restated from `Round.Valid`). `τ_l` compared as a real, `M_l − 1` in `ℕ` (as in
  `CapPrePartStatement`). The two statements are not literally derivable from each other without
  the Run API (`run.d G l = Round.d (run.graph G l)`), hence both.
* **HBtpFacts without validity.** `HBMCeil`, `HBTwoLevel`, `HBStd` hold for every execution of
  the procedure (every `c`), so they carry no validity hypothesis (stronger than the TeX context,
  and checked true: `graft` is structural, `twoLevel` grafts `nil` at small pieces).
  `HBStep1` needs `Round.Valid` (SEP (i) needs the split conditions `WF` of the grafted tree,
  from `IsS0Rec` and `IsTauRun`). `AncestorFacts` keeps the TeX's "Fix a valid run" although its
  conjuncts are definitional consequences.
* **Not restated** (definitional in the locked model): (R1) "`G'_l` has no cycle of length
  `≥ t^HB_l d_l`" (`CyclesValid`), "`X^0_Z` … a graph on `Z^0`", "`Std_l` is a deterministic
  function of the run", the distinctness in "Every ancestor corresponds to a distinct pre-part".
  (R3) "`X^0_Z` is a `(2^{-5}, s_l)`-expander" is s2:propStructure (i) (chunk s2b).
* **Consumers.** `CapRunTauStatement` is the form in which s2:propOV (`EG/Spec/HB/OVRunK.lean`,
  hypothesis `Gamma2a`), s2:propStructure (ii) and s2:propDegRec apply Lemma 14^τ;
  `CapRoundStatement` is the form for one valid round of a possibly unfinished execution
  (DR-ROUND-LOCAL; e.g. the rounds of `RunTerminatesStatement`). It is *not* the form in which
  the `τ`-run termination step of s2:propExists consumes lemCap(ii): that Spec,
  `RoundTauTermStatement` (`EG/Spec/HB/Exists.lean`, s2b), assumes only `CyclesValid ∧ IsS0Rec ∧
  StopsAt` (the `τ`-runs are being constructed there), while `Round.Valid`'s fourth field
  presupposes them. P3 should prove one Lib lemma "piece cap under partial validity" (`Gamma2a`,
  `D_* ≤ d`, `CyclesValid`, `IsS0Rec`, `StopsAt` ⇒ `|𝒫_q| ≤ M(d)` and the `τ`-inequality for every
  piece), from `CapGraphStatement`, (R1) and the `s = 0` stopping rule; it discharges both
  `RoundTauTermStatement`'s first two conjuncts and `CapRoundStatement` (1), (3). `HSCorStatement` is the
  form of s2:propStructure (i) (`X = X^0_Z`, `W = S_Z`, `s = s_l`; the (L2) bound in `G'_l[Z^0]`
  transfers to `X^0_Z` by monotonicity).
* **Dependency on sorry.** A proof of `CapRoundStatement` / `CapRunTauStatement` will go through
  `EG.cap_graph`, which depends on the unproved `EG.bmLemma25` (s1:citLem25, CAP-DEPENDS-SORRY).

## Non-vacuity (`EGTest/Spec_s2a.lean`)

* HS: `K₁₁` is a `(2^{-5}, 0)`-expander (proved, `K11_isExpander`); with `W = ∅`, `s = s_W = 0`
  all hypotheses of `HSStatement` and `HSCorStatement` hold.
* `Round.Valid` and `Run.Valid` (with `R = 1`) are satisfiable (`EGTest.HB.round_valid`,
  `EGTest.HB.run1_valid`); `Gamma2a` is satisfiable.
* Not checked: joint satisfiability of `Gamma2a Dstar ∧ Dstar ≤ d_l ∧ validity` (needs
  s2:propExists on a graph of average degree `≥ 2^{117}`).

## Math findings

None. The ten nodes were re-read against the TeX; no statement appears false. (The blueprint's
blocker HB-M-INTEGER is resolved in v6.1 (R2) and in `MOf : ℕ`; T1 `L14-C-TAU0` is already recorded
in `Lemma14Tau.lean`.)

## Fix round

Reviews: `s2a.review-fidelity-first.md`, `s2a.review-vacuity-and-consumer-form.md`. One item raised.

1. (minor) "Consumers: `CapRoundStatement` is the form s2:propExists needs" — **fixed**. Verified:
   `Round.Valid` (`EG/Defs/HB/Round.lean`) = `CyclesValid ∧ IsS0Rec ∧ StopsAt ∧ (τ-runs at big
   pieces) ∧ home order`, while `RoundTauTermStatement` (s2b) assumes only the first three, so
   invoking `CapRoundStatement` in its proof would be circular in usage (not in truth: the TeX
   proof of lemCap(ii) uses only Γ2(a), (R1), (R2) and the `s = 0` stopping rule, and the TeX
   proof of propExists says these proofs "use only the data of the round"). Reworded the
   "Consumers" bullet above (P3 plan: one Lib lemma "piece cap under partial validity" from
   `CapGraphStatement`), and the same sentence in the module docstring of this unit's own
   `EG/Spec/HB/CapRound.lean` (documentation only; both statements unchanged). No new Spec: the
   partial-validity piece cap is a Lib lemma for P3, and the conclusions propExists needs are
   already `RoundTauTermStatement`'s. Checks: `lake build EG.Spec.HB.CapRound` success;
   `scripts/check.sh EGTest/Spec_s2a.lean`: 0 errors, 0 sorry; `python3 -I scripts/lint.py`:
   0 findings.
