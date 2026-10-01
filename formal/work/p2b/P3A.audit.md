# P3A: independent audit (probe P-3, part 1: τ-rules → SEP → thin cut → OV(sharp) → Lemma 14^τ → GC)

Auditor: independent, clean-room, **2026-09-30**, after the re-dispatched fix rounds of 2026-09-30
(proof-stage fix round 1 re-dispatch, Spec fix round 2 re-dispatch, proof round 1 re-verification)
and the re-run round-2 review of 2026-09-30. This file replaces the audit of 2026-09-29 (git
history, commit fc84210), which I read only after finishing my own checks; where I agree with it I
say so briefly. No Lean file of the repository was edited. Scratch checks are in the session
scratchpad (`P3AAudit.lean`, outside the repo; `lake env lean`: rc=0, 0 errors). The manuscript is a
CANDIDATE proof (AI-reviewed only); nothing here calls the conjecture solved.

Inputs read in full: `work/p2b/P3A.md` (all rounds, including the 2026-09-30 sections),
`P3A.review1.md` (re-run 2026-09-29), `P3A.review2.md` (re-run 2026-09-30); the eight Specs
`EG/Spec/HB/{TauRules,SEP,ThinCut,Overlap,Lemma14Tau,GC,EL,TowerC}.lean`; the eight Proof files
`EG/Proof/HB/{TauRules,SEP,ThinCut,Overlap,Lemma14Tau,GC,EL,TowerC}.lean`; the definition/import
lists of the seven Lib files `EG/Lib/HB/{Split,Address,SEP,OVPotential,Lemma14,Lemma14Ind,GC}.lean`
and the header of `EG/Lib/HB/GC.lean`; `EGTest/ProbeP3A.lean`; the locked Defs
`EG/Defs/HB/{Witness,SplitTree,Round,Run}.lean` in full, `IsExpander`, the `FGraph` primitives
(`induce`, `deleteVerts`, `deleteEdges`, `edgesBetween`, `eBetween`, `nbrSet`, `degE`),
`Gamma1core`, the constants; `proofs/manuscript/s2.tex` v6.1 l.1–505 (defWitness, defTauRules,
eqSplit, lemSEP, lemThinCut, lemOVgeneric, lem14tau, all with proofs), 815–840 (lemEL), 1140–1175
and 1245–1260 (lemTower, proof of (c)), 1280–1320 (lemGC); `work/p2/TRIAGE.md` §4 (row P-3,
refutation targets); the hazard entries of the P3A nodes in `work/p2/nodes_s2a.json`,
`nodes_s2b.json`; `work/p2b/P3B.md` (status of part 2, for the refutation-target check).

## Verdict: APPROVE (no Spec or proof change requested; process notes in §6)

| Check | Result |
|---|---|
| (1) sorry frontier = declared-input stubs | **Yes.** My run of `scripts/Axioms.lean --prefix EG` on `EG.Proof.HB.{TauRules,SEP,ThinCut,Overlap,Lemma14Tau,GC,EL,TowerC}`: "inspected 1214 constants under [EG]; 2 use sorryAx; 0 meta-scan hits; 0 violations", the two being `EG.towerC` (the single declared-input stub, [s2:lemTower] (c), prescribed form) and `EG.gcTheta` (through `EG.towerC` only). `#print axioms` of the other 23 probe theorems: `[propext, Classical.choice, Quot.sound]`. `grep sorry` over the 22 Lib/Proof/Test files of the unit: only `EG/Proof/HB/TowerC.lean:24`. `lint.py`: 0 findings. |
| (2) no Spec changed after its review | **Yes.** The last commit touching any of the eight Spec files is 41e8a4e (2026-09-29 22:27; `TauRules.lean` fix-round-1 c1, `Lemma14Tau.lean` docstring c3); `git diff 41e8a4e HEAD` on the eight files is empty; the working tree equals HEAD for `EG/Spec/HB`, `EG/Proof/HB`, `EG/Lib/HB`, `EG/Defs/HB`, the graph/expander/constants/Γ Defs and `EGTest/ProbeP3A.lean`. Both review files at HEAD are re-runs written after 41e8a4e (review 1 says so explicitly and back-translates the post-c1 `TauEqSplitStatement`; review 2 is dated 2026-09-30 and states the files are byte-identical to HEAD ed552cf). The Defs the Specs depend on were last changed 2026-09-26. Caveat (process): `scripts/lock.py check` reports 865 locked constants, 1 violation (`CONVENTIONS.md`, integrator side, unrelated to P3A) and 234 `PENDING` constants, which include all 25 P3A statements: the freeze on them is enforced by the edit-deny rule only, not by the hash lock. |
| (3) no hidden weakening | **None found.** Every deviation from the TeX is a strengthening, an explicit implicit conjunct, or the documented T1 repair (§3). The Specs import only `EG.Defs.*`; none of the Lib definitions (`TauLabels`, `ovW`, `ovC`, `ovPhi`, `ovCharge`, `tauBuild`) occurs in a Spec. Each probe theorem has *exactly* its Spec's type: `example : EG.Spec.XStatement := EG.x` for all 25 compiled in my scratch. |
| (4) refutation target covered | **Not by P3A, by design; still open in part 2.** TRIAGE §4 names P-3's explicit refutation target "CONC-L(iv) per-ancestor bound" (s6). It belongs to part 2 (P3B), which at HEAD is at stage 1: `ConcLPerAncestorStatement` is stated, `EG.concLPerAncestor` does not exist yet (grep of `EG/`). P3A never claims it. Within P3A every `risk`-class hazard of the chain is discharged by a kernel-checked proof of an unchanged Spec (§4), and the statements part 2 will consume are proved with 0 sorry. |
| (5) math findings classified | One finding, **L14-C-TAU0, class T1**, confirmed with my own Lean witness (§5). One T0 encoding note (Lean `n_0 = 0`). No T2/T3; no new finding. |

## 1. Sorry frontier and build state (my own runs, 2026-09-30)

- `lake build EG.Proof.HB.{TauRules,SEP,ThinCut,Overlap,Lemma14Tau,GC,EL,TowerC}`: up to date
  (replayed); the only warning is `EG/Proof/HB/TowerC.lean:24:8: declaration uses sorry`.
- Axiom scan as in the table: `SORRY EG.gcTheta (EG.Proof.HB.GC)`, `SORRY EG.towerC
  (EG.Proof.HB.TowerC)`, 1214 constants, 0 violations.
- Scratch `P3AAudit.lean` (rc=0): the 25 `example : EG.Spec.XStatement := EG.x` lines; `#print
  axioms` of all 25 (23 clean, `gcTheta`/`towerC` with `sorryAx`); my own refutation of the
  literal lem14tau (c) (§5).
- `LEAN_NUM_THREADS=2 scripts/check.sh EGTest/ProbeP3A.lean 1200`: rc=0, errors=0,
  sorry-warnings=0 (no olean of this file exists in `.lake`, and neither `EG.lean` nor
  `EGTest.lean` imports any P3A module: `grep` finds none; see §6 p3).
- `python3 -I scripts/lint.py`: `lint (development): 0 findings`.
- `python3 -I scripts/lock.py check` (with the toolchain on `PATH`): "865 locked constants, 153
  locked files; 1 violations, 234 pending"; the violation is `CONVENTIONS.md` (locked file whose
  hash lags `LOCK.json`; the working tree equals HEAD for it; not P3A).
- Declared inputs actually used by probe proofs: **only `EG.towerC`** (by `EG.gcTheta`).
  `EG.edgeLaminarity` ([s2:lemEL]) is a real proof (0 sorry) and is not used by any P3A probe
  proof (`EG.gc` proves the `G_{r+1}` clause directly from (R5)(3)).

## 2. Statement fidelity (my own back-translation against s2.tex v6.1)

I back-translated every Spec from the Lean and compared it with the TeX before reading the
reviews' tables; those tables (`P3A.review1.md` §1, `P3A.review2.md` §1.2) are correct and I do
not repeat them line by line. Summary and the points I checked specifically:

- **Defs the reading depends on.** `IsWitness H ε s U F` = `U ⊆ V(H) ∧ F ⊆ E(H) ∧ 1 ≤ |U| ∧
  |U| ≤ 2m/3 ∧ |F| ≤ s|U| ∧ |Nbr_{H−F}(U)| < ε|U|/log²m` (same casts as `IsExpander`, whose
  conclusion is `≤`). `witN H U F = Nbr_{H−F}(U)`; `witF0 H U N = E_H(U, V∖(U∪N))` takes `N`, not
  `F`, so Fact (c) is definitional as the TeX says. `tauHout = {v ∈ U : τ ≤ deg_{F_0} v}` (real
  comparison = TeX `≥ τ`), `tauU1 = U ∖ H_out`, `tauN1 = N ∪ H_out`, `tauF1 = E_H(U', V∖(U'∪N'))`,
  `tauHin = {x ∈ V∖(U'∪N') : τ ≤ deg_{F_1} x}`, `tauN2 = N' ∪ H_in`, `tauF2 = splitDel H U' N''`;
  `tauG1`, `tauG2` are the *literal* children of the TeX, so (eqSplit) is a statement.
  `graphAtD` computes node graphs by `splitFst`/`splitSnd` (the Lemma SEP forms); leaves and
  internal nodes are addresses (`leafAddrs`, `internalAddrs`), so "distinct leaf nodes are
  distinct leaves even if their vertex sets coincide" holds; `dup`, `deleted`, `leafMass`,
  `DeltaGe`, `dupGe` count by address. `WF` (disjoint `U'_a, N''_a ⊆ V(H_a)`), `OVHyp` (`WF` +
  `m ≥ 2`, `|a0| ≤ 3m/4`, `|N''| ≤ cε|U'|/log²m`), `IsS0Rec`, `IsTauSplitTree` (`WF` + at every
  internal node some `s_a < τ` and a parameter-`s_a` witness whose `τ`-rules give the label),
  `IsTauRun` (`WF` + `StopsAt` "leaf ⇔ `(ε,s)`-expander" in **both** directions + labels from
  the `τ`-rules of some parameter-`s` witness) are literal. `cOV = logb 2 (4/3)`.
- **Round/run layer** (`GC`, `EL`, `TowerC`): `Z0 = V(X^0)`; `D = {v ∈ ⋃Z^0 : μ(v) ≥ 2}`;
  `home` = first pre-part of the home order containing `v`; `guests = {v ∈ Z^0 ∩ D : home v ≠ Z}`;
  `isL1`: `2|S| ≤ |Z^0|`; `isL2` in `G'[Z^0]` with real `s/2`; `isGC`: every guest has
  `< θ^GC` neighbours in `Z^0∖S` in `X^0`; `isLight = L1 ∧ L2 ∧ GC`; `isGCPart = L1 ∧ L2 ∧ ¬GC`;
  `Std = prePartAddrs.filter ¬isLight`; `partVerts = Z^0∖S` if light else `Z^0`; `assign` =
  (R5) steps (1)–(3) along the home order, `none` = passes down; `next.edges = passed`;
  `thetaGC d z = ⌈z λ^{−1/2}⌉₊` (rpow); `tauOf = ⌈128 s log²M⌉₊`; `POf = ⌈λ^{103}⌉₊`;
  `Run.Valid` = `∀ l ∈ [1,R], D_* ≤ d_l ∧ Round.Valid` and `d_{R+1} < D_*`; `run.graph` is
  stationary for `l ≥ R+1`; `ancestors = parts`; `ancVerts (l,a) = partVerts l a`. I confirmed
  in `Round.lean` that `prePartAddrs`, `X0`, `Z0`, `DupStar`, `mu`, `D`, `home`, `guests` never
  mention `isGC`/`isLight` (lemGC (i), first clause; a Defs design constraint that holds).
- **Quantifiers.** `L14SplitStatement`/`OVInstanceStatement` quantify over *every* witness
  consistent with the label (stronger than "the chosen witness"; true since the counting uses
  only `(U,F)` and `m ≤ n_0`). `L14TermStatement` (T2) quantifies the rule `W` outside `∃ t`,
  as "for every choice of witnesses" requires; `StopsAt` at the root prevents `t = nil` unless
  `H_0` is an expander, so (T2) is not trivially satisfiable. `SEPiiiStatement`'s `ν*` is
  universally quantified with its two defining properties (prefix of `L` containing `h`, of
  maximal length), which pin it down. In the `τ`-rule statements `N` is a bound variable fixed by
  `N = witN H U F`.
- **Strict vs non-strict, constants, log base.** All logarithms are `Real.logb 2`. lem14tau (a):
  `≤, ≤, ≤` for the `τ`-chain, `<, <` for `|N''|`, `≤` for `127/128` and `0.698 m`, `<` for
  `3m/4` and `n_2 < m`; (b) `≤`; OV `≤`; thin cut `≤ ⌈τ⌉−1`, `= 0`; GC (ii), (iv) `<`; Tower (c)
  `≤, ≤, ≤, ≤, <`. Literals `1.25`, `1.5`, `127/128`, `0.698`, `3/4`, `4 s n_0 log n_0`,
  `2n_0 − 2n_0/(2+log n_0)`, `1.6`, `5.5`, `1.21`, `5.46`, `3.42`, `1.12`, `257`, `2^{111}`
  (`σ+11`), `102` (`σ+2`), `128` are the TeX's. The two conjuncts written `x / logb 2 K.card ^ 2`
  parse as `x/(log m)²`.
- **Integer vs real.** `s : ℕ` cast to ℝ (TeX "`s ≥ 1` an integer"); `τ, c, M` real;
  `m − |U'| < m` in ℕ (exact: `1 ≤ |U'| ≤ m`); `⌈τ⌉ − 1` in ℤ and `k − 1` in ℕ under `τ = k > 0`
  (then `k ≥ 1`); `θ^GC, τ_r, P_r, s_r, M_r` are ℕ ceilings as in v6.1; `λ_r^{−1/2}` is `rpow`.
- **Thin-cut count.** The Lean count is over deleted *edges* `e = s(h,u)` with `u ∈ V(L)∖Dup`;
  `u ↦ s(h,u)` is injective and `s(h,h)` is never an edge (`FGraph` loopless), so it equals the
  TeX count over `u`. `h` ranges over all of `V` (the TeX proof itself reduces to `h` in the root).
- **OV.** (a) in the sharp `c_OV` form plus the `3.42` relaxation as a separate conjunct (needed
  by lem14tau (b), hazard OV-CONST-546); the identity `Σ_{v∈V(H_0)} dup_{≥M}(v) = Δ_{≥M}` loses
  nothing (`N''_a ⊆ V(H_a) ⊆ V(H_0)` under `WF`); (b)'s consequence additive (`Σ ≤ |⋃| + Δ`).
- **GC.** (ii): `eBetween {x} (Z^0∖S)` with `x ∈ S` (so `x ∉ Z^0∖S`) is `|N_{X^0}(x) ∩ (Z^0∖S)|`,
  the quantity of `isGC`. (iii): "assigned at round `r`" = `assign ≠ none` (to *some* part,
  GC-III-WHICH-PART); `E(X^0) ⊆ E_r(Y)` and `V(Y) = Y^0` are the TeX's parenthetical and
  "`V(Y) = Y^0`" made explicit. `GCDefStatement` is the second clause of (i) and is a tautology
  of `isLight = L1 ∧ L2 ∧ GC` (as the TeX's (i) is "the order of definitions"); it is not
  content and `P3A.md` now says so.
- **EL / TowerC.** `ELStatement`: `Y ∈ run.ancestors G`, every `l > Y.1` (includes `l > R+1`,
  where `graph` is stationary: harmless strengthening). `TowerCStatement`: `Gamma1core` (Γ1
  (a)–(e)) instead of Γ1–Γ4, `Dstar ≤ run.d G 1` kept, `r ∈ Icc 1 R`, the five inequalities of
  (c) with `σ+2 = 102`, `σ+11 = 111`.

## 3. Hidden-weakening audit (every deviation, classified by me)

| # | Deviation | Direction | Verdict |
|---|---|---|---|
| 1 | `L14ThinStatement`: `0 < τ` on the two bounds of (c) | weaker than the literal TeX | the literal TeX is false at `τ = 0` (§5); minimal repair (bounds hold for every `τ > 0`, also at `n_0 ≤ 1`; the `= 0` clause and (d) stay unconditional; every application has `τ ≥ 128`). T1. |
| 2 | `L14SplitStatement`, `OVInstanceStatement`: every witness consistent with the label | stronger | true (proved) |
| 3 | `TauEqSplitStatement`: the premise "one end in `U'`, the other in `V∖(U'∪N'')`" as a conjunct (fix round 1, c1) | stronger | true by `splitDel` (proved) |
| 4 | `TauFactAStatement`: `U', N'' ⊆ V(H)` | stronger (implicit in the TeX) | true (proved) |
| 5 | `L14OVStatement`: `2 ≤ |H_a|` at internal nodes; `OVStatement`: `Σ dup = Δ`; `GCStatement`: `V(Y) = Z^0`, `E(X^0) ⊆ E_r(Y)` | stronger (explicit implicit conjuncts) | true (proved) |
| 6 | `GCThetaStatement`, `TowerCStatement`: `Gamma1core` instead of Γ1–Γ4 | stronger; for the *input* `TowerCStatement` the riskier direction | Re-derived by me from the TeX proof of (c) (l.1249–1257) and the Defs: `s_r = ⌈Λ^σ⌉ ≤ 2Λ^σ` (needs `Λ ≥ 1`, i.e. `M_r ≥ 2`, true as `M_r ≥ 2^{40}`) ⇒ `τ_r ≤ 128·2Λ^σΛ² + 1 ≤ 257Λ^{σ+2}`; `M_r ≤ d_r²` for `d_r ≥ D_* ≥ 2^{2^{256}}` (Γ1(a) at `μ = log log D_*`, and `D_* ≤ d_r` from `Valid`) ⇒ `Λ_r ≤ 2λ_r` ⇒ `257Λ^{102} ≤ 257·2^{102}λ^{102} < 2^{111}λ^{102}`; `P_r = ⌈λ^{103}⌉ ≥ λ^{103}` ⇒ `τ_r/P_r ≤ 2^{111}/λ_r`; a pre-part has `|Z^0| ≥ P_r` ⇒ `θ^GC = ⌈|Z^0|λ^{−1/2}⌉ ≥ P_rλ^{−1/2} ≥ λ^{102.5}`; `τ_r < 2^{111}λ^{102} < λ^{102.5}` since `λ_r ≥ log D_* ≥ 2^{256} > 2^{222}`. Only Γ1(a) and the definitions are used; the junk regime `λ ≤ 0` is unreachable (`Gamma1core D → 2 < D`, indeed `D ≥ 2^{2^{256}}`). The input is true and not stronger than what the manuscript proves. |
| 7 | `IsTauRun` has no `s < τ` clause; `IsTauSplitTree` has no `s_a ≥ 0` | more trees ⇒ statements stronger | fine: an internal node has `m ≥ 2` hence `n_0 ≥ 2` and `τ ≥ 128 s > s` (the TeX's own remark); a witness forces `0 ≤ s` (`0 ≤ |F| ≤ s|U|`, `|U| ≥ 1`) |
| 8 | `SEPMonoStatement` without `WF`; `ThinCutEdgeStatement` without `u ∈ V(H_0)`; `ELStatement` for all `l > r`; `L14TermStatement` (T1) for all `K` with `2 ≤ |K| ≤ n_0` | stronger | true (all proved) |
| 9 | `ε` fixed to `epsC = 2^{−5}` | as the TeX ("Throughout, ε = 2^{−5}") | fine |
| 10 | `n_0 ≥ 1` in `OVStatement`, `0 ≤ s` in the `τ`-rule statements, `D_* ≤ d_1` in `TowerCStatement` | kept although unused | literal to the TeX; harmless |
| 11 | Rounds `r ∈ Finset.Icc 1 run.R`; per-address wrappers read only at `a ∈ prePartAddrs`; `run.tauRun` never read by a Spec | CONVENTIONS | fine |

Non-vacuity (re-checked by type-checking `EGTest/ProbeP3A.lean`): a `τ`-run at the smallest
allowed `τ = 512` with three splits and two deletions (`L14*` hypotheses); a `τ`-split tree; a
non-idle `τ`-split (`H_out = {0}`) on which the thin-cut bound `⌈τ⌉−1 = 1` is *attained*;
`OVHyp ε 1` with two splits; an `s = 0` recursion; a valid run with three pre-parts;
`Gamma1core ∧ Valid` jointly; a round-local (not valid) GC-part exercising every round-level
conclusion of (iii). No conclusion is trivially true where the TeX has content; the literal
lem14tau (c) is refutable (§5), so the hypotheses do constrain the conclusions. Carried caveat
(agreed with both reviews): no toy instance has `N''_a ≠ ∅` under `OVHyp`/`IsTauRun` (needs
`|U'| ≳ 32 log²m`), so the quantitative content of OV (a)/(b) and 14^τ (b) is verified by proof
alone (`EG.ov`, `EG.l14OV`, 0 sorry); likewise no *valid* run with a GC-part exists at toy size.

Proof-route observations (not weakenings; all kernel-checked proofs of the unchanged Specs):
thin cut and SEP (iii) are proved from `STree.TauLabels` alone (as the manuscript remarks); OV (a)
by a per-vertex potential induction with `c_OV ≥ 17/41`; GC (iii)'s `G_{r+1}` clause directly from
(R5)(3) (`Round.assign_ne_none_of_not_isLight`) instead of via Lemma EL; Lemma EL from
`Round.assign_ne_none_of_mem_partVerts` ((R5) steps (2)/(3)), which needs the home order to list
every pre-part (`mem_homeOrder_of_valid`, from `Round.Valid`).

## 4. Refutation-target coverage

- TRIAGE §4: "P-3: CONC-L(iv) per-ancestor bound". This is s6 material (part 2 of P-3:
  propOrigin → CONC → CONC-L(iv)) and is **not** in P3A; P3A does not claim it. Status of part 2
  at HEAD (`work/p2b/P3B.md`): stage 1 only; `ConcLPerAncestorStatement` is stated and
  re-derived on paper, `EG.concLPerAncestor` is not yet proved (no such theorem under `EG/`).
  **The probe's refutation target is therefore not yet covered by a proved statement**; this is
  a fact about the state of P3B, not a defect of P3A.
- Hazards of the P3A nodes (`nodes_s2a.json`/`nodes_s2b.json`) of class `risk`, and the proved
  statement that discharges each: SEP-TREE-INFRA, SEP-LEAF-IDENTITY (address model, leaves
  counted by address): `EG.sep0`, `EG.sepI`–`EG.sepIII`; OV-CONST-546 (the `5.46` needs the sharp
  OV (a) and `c_OV ≥ 0.414508`, `12/29` fails): `EG.ov` proves the sharp form, `EG.l14OV` proves
  `5.46` via `17/41`; LEM14-TERMINATION: `EG.l14Term` ((T1) strict size decrease of both children,
  (T2) `tauBuild`). Note-class but risk-relevant: HB-STOPRULE (both directions in `IsTauRun`;
  `EG.l14Global` uses "leaf ⇒ expander", `EG.l14Term` (T2) needs "non-expander ⇒ split");
  GC-III-WHICH-PART (Spec claims `assign ≠ none` and `E(X^0) ⊆ E_r(Y)` only; `EG.gc`);
  EL-HOMEORDER-COMPLETE (`Round.Valid` requires `homeOrder.toFinset = prePartAddrs`; used).
- Hand-off to part 2: `L14ThinStatement` (c),(d), `L14OVStatement`, `GCStatement` (ii),(iii),
  `OVInstanceStatement`, `ELStatement` are the statements propOrigin/CONC/CONC-L will consume;
  all are proved with 0 sorry. `GCThetaStatement` (lemGC (iv)) is a one-line corollary of the
  input `EG.towerC` and carries no P3A content.

## 5. Math findings (own evidence, classified)

**L14-C-TAU0 — class T1 (confirmed independently).** s2:lem14tau assumes `s ≥ 1` and
`τ ≥ 128 s log² n_0`; at `n_0 = 1` this reads `τ ≥ 0`, so `τ = 0` is admitted. Take `H_0` = one
vertex, `s = 1`, `τ = 0`. The one-vertex graph is an `(ε,1)`-expander (no `U` with
`1 ≤ |U| ≤ 2/3`), so the `τ`-run is the single leaf, nothing is deleted, and (c) claims
`0 ≤ ⌈0⌉ − 1 = −1` (and "`= τ − 1` for integer `τ`" claims `0 ≤ −1`). The proof's sentence "If
`n_0 = 1` the root is an `(ε,s)`-expander and everything is trivial" is right for (a), (b), (d)
and wrong for (c). My own Lean witness (scratch `P3AAudit.lean`, written from the Spec shape
without reusing the EGTest lemma): `¬ (∀ V H s τ t, 1 ≤ s → 128 s log² n_0 ≤ τ → IsTauRun → ∀ L
∈ leaves, ∀ h, (count : ℤ) ≤ ⌈τ⌉ − 1)` on `FGraph.ofEdges univ ∅` over `Fin 1`, `t = nil`,
compiles; I also re-type-checked `EGTest.ProbeP3A.lem14tau_c_literal_false`. The statement is
true for every `τ > 0` (Lemma lemThinCut itself assumes `τ > 0`); every application has
`τ = τ_l = ⌈128 s_l Λ_l²⌉ ≥ 128`. Classification T1: true after a one-clause wording fix, no
downstream impact; not T0 (a statement edge case, not an encoding choice); not T2 (nothing to
repair in a proof). Manuscript action: add "(for `τ > 0`)" to lem14tau (c), or "Let `n_0 ≥ 2`" to
the lemma. Repair adopted in `L14ThinStatement`: `0 < τ` on the two bounds only, which is the
stronger of the two possible repairs. The author's and both reviewers' T1 classification agrees.

**T0 note (encoding), same repair.** In Lean the hypothesis also admits `τ = 0` at `n_0 = 0`
(`Real.logb 2 0 = 0`); a graph without vertices is an expander, the run is one leaf, and the same
witness applies. Covered by the `0 < τ` repair; no manuscript action beyond the T1 note. The ℕ
form `k − 1` is not false at `τ = 0` (truncated subtraction), which is why the Spec needs `0 < τ`
on it only for faithfulness to the TeX's integer arithmetic, not for truth.

**Reviewer-2 observations (no finding).** (i) lem14tau (a)'s `|F_0|/τ` is meaningless at `τ = 0`;
but `τ = 0` forces `n_0 ≤ 1`, where there is no split, so "at every split" is vacuously right
(Lean's `x/0 = 0` is never reached). (ii) lemGC (iii)'s citation of Lemma EL is valid but not
needed (the clause follows from (R5)(3)); a proof citing more than it needs is not a gap. Class:
none for both.

**Author's process notes (no finding).** `GCDefStatement` is a tautology of `isLight`
(faithful: the TeX's (i) is definitional); the `WF` conjunct of `IsTauRun` is implied by its label
clause (machine-checked in `EGTest/ProbeP3A.lean`), so "it is a split recursion" is a consequence,
not a silent assumption. Class: T0 bookkeeping at most; no manuscript action.

**Nothing else.** I re-derived from the TeX, independently of the reviews: the witness Fact;
Facts (a)–(c) and (eqSplit); SEP (0)–(iii) (in (iii) a deletion node of `hu'` is an ancestor of
`Leaf_u` containing `h` whose path child does not contain `h`, hence it is `ν*`); thin cut cases
A/B (`h ∉ U'∪N''` ⇒ `h ∉ H_in` ⇒ `deg_{F_1}(h) < τ`; `h ∈ U' = U∖H_out` ⇒ `deg_{F_0}(h) < τ`;
`F'' ⊆ F_1 ⊆ F_0`); OV (a) (charging ancestors of a leaf copy satisfy `|ν^{(i)}| ≤ |ν^{(i+1)}_1| ≤
(3/4)|ν^{(i+1)}|`, sum ≤ `1/log²M + 1/(c_OV log M)`, `1 + 1/c_OV = 3.409 ≤ 3.42`), (b), (c) and
the instance (`|U∪N| < (1+ε)(2/3)m ≤ 3m/4`, `1/(1−3.42/32) = 1.1196 ≤ 1.12`); lem14tau's one-split
counting (`Σ_{v∈U} deg_{F_0}(v) = |F_0|`, `|F_1| = |F_0| − a` because each `F_0` edge has exactly
one end in `U`, `τ(|H_out|+|H_in|) ≤ |F_0| ≤ s|U|`, `1/128 = ε/4`, `|N''| = |N| + |H_out| + |H_in|`
disjointly, `n_1 ≤ (1 + 1.25/32)(2/3)m = 0.693m ≤ 0.698m`, `log₂ 0.698 = −0.518 < −2/5`), the
induction inequalities (8) (`6ε/log m ≤ 3/16 < 3/5`) and (9) (`7L² − 3.6L − 3.2 ≥ 0.2` at `L = 1`,
increasing; `3ε = 3/32 < 1/10`), (b)'s constants (`3.42·1.6 = 5.472 ≤ 5.5`, `32/26.5 = 1.2075 ≤
1.21`, `1.6(1 + 1/c_OV) = 5.4551 ≤ 5.46`); lemGC (ii)–(iv) and lemEL; lemTower (c) under Γ1(a)
alone (§3 item 6). No statement of the chain looked false; no step of a manuscript proof in the
chain is wrong except the "everything is trivial" sentence of L14-C-TAU0.

## 6. Issues (none blocking)

- **p1 (process, integrator).** The 25 P3A statements are `PENDING` in `LOCK.json` (234 pending
  constants in total at HEAD), so `scripts/lock.py check` does not yet detect a change to them or
  to the Defs they depend on beyond the HB Defs already locked. The freeze is enforced for them by
  the edit-deny rule only. The current bytes (identical to HEAD and to the reviewed versions) are
  the right ones to lock.
- **p2 (process, orchestrator).** `EG.towerC` ([s2:lemTower] (c)) is the unit's only `sorry` and
  a stronger-than-TeX declared input (`Gamma1core` only). It is true (§3 item 6), so nothing is at
  risk, but the s2 tower unit must be confirmed as its owner and must prove *this* statement
  (import `EG/Spec/HB/TowerC.lean`, do not restate (c)), as `P3A.md`, the stub docstring and
  `EG/Spec/HB/TowerB.lean` already say. Until then lemGC (iv) is proved only modulo this input.
- **p3 (process, orchestrator).** Neither `EG.lean` nor `EGTest.lean` imports any P3A module
  (8 Spec, 8 Proof, 7 Lib modules; `EGTest.ProbeP3A`), so CI builds none of them and the
  L14-C-TAU0 witness, the non-vacuity checks and the `WF`-redundancy check are verified by hand
  only (I did: rc=0). Add the imports listed in `P3A.md` ("Root imports for the orchestrator").
- **p4 (process, part 2).** The P-3 refutation target (CONC-L(iv) per-ancestor bound) is still a
  stage-2 obligation of P3B (`EG.concLPerAncestor`); it should not be reported as covered by P-3
  until that theorem exists with the stub frontier scanned.
- **c1 (cosmetic, locked file).** The module docstring of `EG/Spec/HB/EL.lean` still calls
  `ELStatement` a declared input with stub `EG.edgeLaminarity`; it is proved. Documentation only
  (`EG/Proof/HB/EL.lean` records the change); for the integrator's next pass on locked files.
- Out of scope but observed: `lock.py check` reports `CONVENTIONS.md` as a changed locked file
  (hash lag; the working tree equals HEAD for it). Also the working tree has an uncommitted change
  to `EG/Defs/Gamma/Full.lean` (another unit; not imported by any P3A Spec, which use
  `EG.Defs.Gamma.Core`).

## 7. Answers to the author's open questions (audit view)

1. L14-C-TAU0: keep `0 < τ` on the two bounds of (c); send the T1 note to the manuscript. (The
   alternative `2 ≤ H.card` on the whole lemma would be a weaker statement.)
2. Declared inputs: EL is settled (proved, 0 sorry). TowerC stays an input owned by the tower
   unit; its Spec file is to be imported, not restated (p2).
3. Recording lemGC (i)'s first clause as a Defs design constraint is acceptable; I verified it on
   `Round.lean`.
4. GC-part non-vacuity: the round-local `GCPartTest` is an adequate substitute; a valid run with
   a GC-part needs galactic `d` and is not worth constructing. The clause is proved (`EG.gc`).
