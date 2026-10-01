# P3A: clean-room review, round 1 (Specs of probe P-3, part 1)

Reviewer: clean-room Spec reviewer, round 1 (re-run, 2026-09-29). No Lean file in the repo was
edited. This file replaces the earlier round-1 review; that version is in git history (commit
41e8a4e), and I did not read it before writing this one. Scratch checks are in the session scratchpad
(`P3ARev.lean`, outside the repo); they compile with `lake env lean` with 0 errors. The proof being
formalized is a CANDIDATE proof, reviewed only by AI.

**Verdict: APPROVE.** Every Spec is faithful to `s2.tex` v6.1, with one stated T1 repair
(L14-C-TAU0), which I confirmed independently. There are no vacuous hypotheses and no hidden
probe nodes among the declared inputs, and the lint is clean. The remaining issues are 1 minor
(process) and 4 cosmetic.

Files reviewed (all locked; read in full):
- `EG/Spec/HB/{TauRules,SEP,ThinCut,Overlap,Lemma14Tau,GC,EL,TowerC}.lean`;
- `EG/Proof/HB/{EL,TowerC}.lean` (stubs);
- the Defs these files use: `EG/Defs/HB/{Witness,SplitTree,Round,Run}.lean`, the `FGraph` basics in
  `EG/Defs/Graph.lean` and `EG/Defs/Expander.lean`, and `EG/Defs/Gamma/Core.lean`.

No new Defs (`EG/Defs/Probe/` has no P3A folder).

TeX read: s2.tex l.1–700 (defWitness … defHBtp), lemEL (l.821), propDegRec (l.922),
lemTower with its proof (l.1144–1280), lemGC (l.1282), and s1 condGamma (l.1594).

## 1. Fidelity (back-translation, TeX comparison)

Notation: `ε = epsC = 2^{-5}`, `log = logb 2`, `m = |H|`, `n_0 = |H_0|`.

### defWitness / defTauRules / eqSplit (`TauRules.lean`)

| Spec | Back-translation | TeX | OK? |
|---|---|---|---|
| `WitnessExistsStatement` | `s ≥ 0`, `H` not an `(ε,s)`-expander ⇒ `m ≥ 2` and some witness `(U,F)` exists | "Then `m≥2` … a witness exists" | yes |
| `WitnessFactStatement` | `s ≥ 0`, `(U,F)` a witness, `N = Nbr_{H−F}(U)` ⇒ `F_0 ⊆ F`, `Nbr_{H−F_0}(U) = N`, and `(U,F_0)` is a witness | Fact | yes |
| `TauEqSplitStatement` | every `e ∈ F''` is `xy` with `x∈U'` and `y ∈ V∖(U'∪N'')`, `e ∉ (U'∪N'')^{(2)}`, and `e` meets `U'`; `G_1 = H[U'∪N'']`, `G_2 = H[V∖U'] − E(H[N''])` | (eqSplit) paragraph | yes |
| `TauFactAStatement` | `U'∩N''=∅`, `U'∪N'=U∪N`, `F''⊆F_1⊆F_0⊆F`, plus `U',N''⊆V(H)` | Fact (a) + implicit subsets | yes (added conjuncts are true and needed by SEP) |
| `TauFactBStatement` | three pairwise-disjoint edge sets with union `E(H)`; `V(G_1)=U'∪N''`, `V(G_2)=V∖U'`; where each vertex goes | Fact (b) | yes |
| `TauFactCStatement` | `(U,F_0)` is a witness, `N_0 = N`, and all nine objects coincide | Fact (c); first sentence definitional (Defs take `(H,U,N,τ)`) | yes |

Context checks:
- The context `0 ≤ s`, `IsWitness`, `s < τ`, `N = witN` is literally the TeX context ("τ > s be real").
- `IsWitness` matches the TeX witness conjunct for conjunct, with `U ⊆ V(H)` and `F ⊆ E(H)`.
- `witF0` takes `N`, so Fact (c)'s dependence on `(U,N)` only is definitional, as the TeX says.
- `tauHout`/`tauHin` use `τ ≤ deg` (real comparison) = "`deg ≥ τ`".
- `nbrSet U` excludes `U` (= `Nbr`).

### lemSEP (`SEP.lean`)

- **(0) `SEP0Statement`.** Under `t.WF H` (disjoint `U'_ν, N''_ν ⊆ V(H_ν)`):
  - at every internal `a`, the edge trichotomy, where each vertex goes, and `|ν_1|+|ν_2| = |ν|+|N''_ν|`;
  - every vertex of a node lies in a leaf below it;
  - `S = |H_0| + Σ_ν |N''_ν|`.

  Faithful. Leaves are addresses, so distinct leaves with equal vertex sets are counted
  separately ("distinct leaf nodes are distinct leaves").
- **(0′) `SEPMonoStatement`.** Implicit monotonicity; stated without WF, which makes it stronger and still true (`induce`/`deleteEdges` are subgraphs).
- **(i) `SEPiStatement`.**
  - "Exactly one leaf or exactly one deletion node" becomes the count `= 1`, plus "the leaf contains both ends".
  - For a deletion node, it states:
    - the edge is in every prefix and in neither child, which is equivalent to "`ν` is the first node on the path …";
    - `x ∈ U'`, `y ∈ V(H_ν)∖(U'∪N'')`, each going to exactly one child, and to different children.
  - Faithful.
- **(ii) `SEPiiStatement`.**
  - For `u ∈ V(H_0)∖Dup`, there is a leaf `L ∋ u`, unique among leaf addresses.
  - The nodes containing `u` are exactly the prefixes of `L`.
  - `u ∉ N''_a` on the path.
  - Faithful.
- **(iii) `SEPiiiStatement`.**
  - `u, h ∈ V(H_0)`, `u ∉ Dup`, `u ∈ L`, `h ∉ V(L)`.
  - `ν*` is a prefix of `L` containing `h`, and every prefix of `L` containing `h` is no longer than `ν*` ("deepest").
  - Conclusion: every deleted `hu'` with `u' ∈ V(L)∖Dup` lies in `F''_{ν*}`.
  - Faithful. `ν*` is automatically a node (a prefix of a leaf address).

### lemThinCut (`ThinCut.lean`)

- Hypotheses: `τ > 0` and `IsTauSplitTree epsC τ` (WF, and at every internal node a witness with some `s_ν < τ` whose τ-rule sets are the label). This is the TeX hypothesis verbatim.
  - `s_ν` is not required to be `≥ 0`, but this costs nothing: a witness forces `0 ≤ s`, since `|F| ≤ s|U|` with `|U| ≥ 1`. Checked in Lean: first `example` of the scratch file.
- `ThinCutStatement`: for every leaf `L` and every `h : V`, the count `#{e ∈ deleted : e = hu, u ∈ V(L)∖Dup}` satisfies:
  - `≤ ⌈τ⌉ − 1` in ℤ;
  - `≤ k − 1` if `τ = k ∈ ℕ` (then `k ≥ 1`, so the ℕ-subtraction is exact);
  - `= 0` if `h ∈ V(L)`.

  Faithful.
- `ThinCutEdgeStatement`: for `u ∉ Dup` and `u ∈ e ∈ E(H_0)`, either `e` is deleted, or `e ∈ E(L)` for a leaf `L ∋ u` that is the only leaf containing `u`. Faithful ("the unique leaf containing `u`" is stated together with its uniqueness).

### lemOVgeneric (`Overlap.lean`)

- `OVStatement`. Hypotheses: `c > 0`, `3.42cε < 1`, `n_0 ≥ 1` (kept, although it is unused), and `OVHyp epsC c`. Here `OVHyp` is WF plus, at every internal node, `m ≥ 2`, `|ν_1| ≤ 3m/4` and `|N''| ≤ cε|U'|/log²m`. This is the TeX literally.
  - (a): the sharp chain, with both links, for real `M ≥ 2`.
  - The identity `Σ_{v∈V(H_0)} dup_{≥M}(v) = Δ_{≥M}` (the sum over `V(H_0)` loses nothing, since `N''_ν ⊆ V(H_0)` under WF).
  - (b): per vertex, plus the consequence in additive form (this avoids ℕ-subtraction).
  - (c).
  - `Δ_{≥M}`, `dup_{≥M}` and `S` are all indexed by address.

  Faithful. Real `M` is more general than the applications (`M = 2`, `P_r`).
- `OVInstanceStatement`. For an `s=0` recursion (`IsS0Rec`: WF, and every label is `(U, Nbr_{H_a}(U))` for a parameter-0 witness):
  - per node: `F = ∅`, `witN = N`, both children in the B-M form, the identity of the two B-M forms of child 2, `F''_a = ∅`, and for every `τ > 0`: `F_0 = ∅`, `H_out = H_in = ∅`, `U' = U`, `N'' = N`;
  - globally: `IsTauSplitTree` for every `τ > 0`, `OVHyp ε 1`, and `S ≤ n_0/(1−3.42ε) ≤ 1.12 n_0`.

  Faithful. The "(exactly the recursion of [BM])" sentence is commentary.

### lem14tau (`Lemma14Tau.lean`)

Common hypotheses:
- `s : ℕ` with `s ≥ 1`;
- `128 s log²n_0 ≤ τ`;
- `IsTauRun epsC s τ`: WF, both directions of "leaf ⇔ `(ε,s)`-expander", and every label is the τ-rule pair of some parameter-`s` witness. "For every choice of witnesses" = every such tree.

The WF conjunct of `IsTauRun` is implied by the label clause (Fact (a) at `H_a`). So it does not shrink the class of runs, and "it is a split recursion" is not silently assumed.

- **`L14SplitStatement`** (the local part of (a)). For every internal `a` and **every** witness whose τ-rules give the label: each link of both chains, `|U'| ≥ 127/128·|U|`, `|U'| > 0`, `U ⊆ U'∪N''`, `n_1 ≤ 0.698m < 3m/4`, `n_2 = m−|U'| < m`.
  - Quantifying over every witness consistent with the label is stronger than "the chosen witness", and is true, because the counting argument applies to each witness.
  - Arithmetic re-checked: `ε + 1/128 = 5/128 = 1.25ε`; `(2/3)(1+1.25/32) = 0.693 ≤ 0.698`.
- **`L14TermStatement`.**
  - (T1): any τ-rule split of any `K` with `2 ≤ |K| ≤ n_0` has children of sizes in `[1,|K|)`. This is true: `|U'| ≥ 1`, `|U'| ≤ 2|K|/3`, `n_1 ≤ 0.698|K|`.
  - (T2): every address-dependent witness rule yields a τ-run.
  - Together they are a faithful and slightly stronger rendering of "The recursion terminates … for every choice of witnesses".
- **`L14GlobalStatement`**: `|deleted| ≤ 4 s n_0 log n_0`; the count-form partition; leaves are `(ε,s)`-expanders; `S ≤ 2n_0 − 2n_0/(2+log n_0)`. Faithful. Checked at `n_0 ∈ {0,1}`: both sides are consistent (`t = nil`).
- **`L14OVStatement`**: (b) with the implicit `m ≥ 2`, `OVHyp ε 1.6`, `S ≤ n_0/(1−5.5ε) ≤ 1.21n_0`, and `Δ_{≥M} ≤ 5.46εS/log M`.
  - Constants re-checked: `3.42·1.6 = 5.472 ≤ 5.5`; `32/26.5 = 1.2075`; `1.6(1+1/log₂(4/3)) = 5.4551 ≤ 5.46`.
- **`L14ThinStatement`**: (c) with `0 < τ` on the two bounds (the T1 repair), and (d). Faithful apart from the repair, which is minimal (see §5).

### lemGC (`GC.lean`), with the Round/Run Defs

- **`GCDefStatement`.** Under (L1)∧(L2), light ⇔ (GC); if not (L1)∧(L2), then not light. This is (i), second clause.
  - I checked the first clause (definitional) against `Round.lean`: `prePartAddrs`, `X0`, `Z0`, `DupStar`, `mu`, `D`, `home` and `guests` never mention `isGC`/`isLight`.
- **`GCStatement`.**
  - (ii): `e_{X^0}({x}, Z^0∖S) < θ^GC` for light `a` and every guest `x`. Here `eBetween {x} B` equals the neighbour count used by `Round.isGC`, because `x ∉ B` and `X^0` is loopless.
  - (iii), for a GC-part:
    - `a ∈ Std_r`;
    - `V(Y) = Z^0`;
    - every edge of `G'_r` inside `Z^0` is assigned;
    - `E(X^0) ⊆ E_r(a)`;
    - no edge of `G_{r+1}` lies inside `Z^0`;
    - `S ⊆ D_r ⊆ Dup*_r`.

  Faithful, including the parenthetical. "Assigned" is to *some* part, as the TeX says. There is no Γ hypothesis; the TeX's standing assumption is not needed for (ii) and (iii), so the statement is stronger.
- **`GCThetaStatement`**: under `Gamma1core D_*` and a valid run, `τ_r < θ^GC_r(Z^0)` for every round-`r` pre-part (ℕ comparison). Faithful to (iv); see cosmetic c1 on its hypotheses.

### Declared inputs (`EL.lean`, `TowerC.lean`)

- **`ELStatement`**: for every ancestor `Y` and every `l > r(Y)`, no edge of `G_l` lies inside `V(Y)`.
  - Matches lemEL. The extension to `l > R+1` is harmless, because `G_l` is stationary there (checked from `Run.graph`).
- **`TowerCStatement`**: under `Gamma1core`, a valid run and `D_* ≤ d_1`, for `r ∈ [1,R]`:
  - `τ_r ≤ 257Λ_r^{σ+2} ≤ 2^{σ+11}λ_r^{σ+2}`;
  - `τ_r/P_r ≤ 2^{σ+11}/λ_r`;
  - `P_rλ_r^{-1/2} ≤ θ^GC_r` and `τ_r < P_rλ_r^{-1/2}`.

  Matches (c) literally (σ+2 = 102 and σ+11 = 111 as natural exponents; `λ^{-1/2}` as rpow).

## 2. Vacuity

- **Hypotheses are satisfiable.** `EGTest/ProbeP3A.lean` covers:
  - a τ-run with three splits at the smallest allowed `τ = 512`;
  - a non-idle τ-rule split tree (`H_out ≠ ∅`, one deleted edge, `Dup = {0}`) with the thin-cut bound attained (`1 = ⌈2⌉−1`);
  - `OVHyp ε 1` with two splits;
  - an `s=0` recursion;
  - a valid run with three pre-parts;
  - `Gamma1core ∧ Valid` jointly;
  - the round-level forms of the GC-part clause.
- **Quantitative content is never exercised.** In every toy instance `N'' = ∅` and `Δ_{≥M} = 0`, because `|N''| ≤ cε|U'|/log²m < 1` unless `|U'| ≳ 32 log²m`. The hypotheses still do not force `N'' = ∅`: at `m ≈ 10^3` the bound exceeds 1. So OV (a)/(b) and 14^τ (b) are not vacuous, only untestable by `decide`.
- **No conclusion is trivially true.** Checks:
  - the thin-cut count reaches its bound in `NonIdleTau`;
  - the literal 14^τ (c) is refutable (L14-C-TAU0), so the hypotheses do constrain the conclusion;
  - `GCThetaStatement` is not implied by the Defs alone (junk `P = 0` gives `θ^GC = 0`).
- **Independent scratch checks** (scratchpad `P3ARev.lean`, compiled, 0 errors):
  1. `IsWitness H ε s U F → 0 ≤ s`, so the unconstrained `s` in `IsTauSplitTree` is harmless.
  2. A fresh Lean refutation of the literal 14^τ (c) at `H_0` = one vertex, `s = 1`, `τ = 0`, `t = nil`. I built the `IsTauRun` proof from scratch rather than reusing the EGTest lemma. The ℤ-form count `0 ≤ ⌈0⌉−1 = −1` fails.
  3. Remark: the ℕ form (`τ = k`) is *not* false at `τ = 0`, because `0 − 1 = 0` in ℕ.

## 3. Declared inputs

| Input | Used by the manuscript proof? | Stated as in the TeX? | A probe node in disguise? |
|---|---|---|---|
| `ELStatement` ([s2:lemEL]) | yes: lemGC (iii), "By Lemma EL …" | yes | no (lemEL is not in the P3A list; nodes_s2b) |
| `TowerCStatement` ([s2:lemTower] (c)) | yes: lemGC (iv) "is Lemma Tower(c)" | yes, with `Gamma1core` for the standing assumption | no |

- B-M Lemma 25, Cap and Lemma 15 are not used by this chain. That is correct: lemCap enters only through the τ-run hypothesis of a *round*, which is not in P3A.
- s1:citLem14 is attribution only: s2 re-proves the argument in full.
- s1:citDef11 is the Def `IsExpander`.
- I checked that `TowerCStatement` under `Gamma1core` alone is what the TeX proof of (c) supports:
  - `s_r ≤ 2Λ^σ`;
  - `Λ_r ≤ 2λ_r` (propDegRec, via Γ1(a),(b));
  - `P_r ≥ λ^{103}`;
  - `|Z^0| ≥ P_r`;
  - `λ^{1/2} ≥ 2^{128} > 2^{111}` (Γ1(a)).

  Γ2–Γ4 are not needed, so the input is not stronger than what the manuscript proves.

## 4. Hygiene

- `python3 -I scripts/lint.py`: `lint (development): 0 findings`.
- `sorry` appears in the P3A Spec/Proof/Lib files only in the two stubs `EG.edgeLaminarity` and `EG.towerC`. Both are of the prescribed form `/-- [DECLARED INPUT] [label] … -/ theorem … := by sorry`.
- Every Spec docstring starts with the manuscript label and quotes the TeX. The files are modules with `@[expose] public section`, the statements live in `EG.Spec`, and each quantifies `∀ (V : Type u) [DecidableEq V]`.
- Built oleans exist for all eight Spec modules and the Proof modules. The root files are untouched.

## 5. Issues

- **m1 (minor, process). `ELStatement` is a declared input, but the P3A proofs no longer use it.** P3A.md, proof round 1, says `EG.gc` proves the `G_{r+1}` clause directly from (R5).
  - The declaration is legitimate: the manuscript proof does cite EL.
  - But the unit now carries an unused `sorry` stub.
  - Fix: either move ownership of the stub to the s2 structure unit (with the Spec unchanged), or prove it in P3A. The proof is the same (R5) case analysis that `EG/Lib/HB/GC.lean` already contains, about 80 lines.
- **c1 (cosmetic). `GCThetaStatement` omits `D_* ≤ d_1` and assumes only `Gamma1core`.**
  - Both are harmless. `Valid` with `r ∈ [1,R]` gives `D_* ≤ d_r`, and in particular `d_1 ≥ D_*`, because `R ≥ 1`.
  - The TeX's standing assumption Γ1–Γ4 is stronger than `Gamma1core`, and (iv) needs only Γ1(a),(b) (§3). So the Spec is stronger than the TeX, and true.
  - Fix: no change; possibly add a docstring sentence saying so.
- **c2 (cosmetic). `IsTauRun`'s WF conjunct is redundant.** It follows from the label clause and TauFactA.
  - Worth a sentence in the Lemma14Tau module docstring: "it is a split recursion" is then a consequence, not an assumption.
  - The Defs are locked; no change is needed.
- **c3 (cosmetic). `L14TermStatement` (T1) quantifies over *all* graphs `K` with `2 ≤ |K| ≤ n_0`,** not only node graphs of the run. This is stronger and true, and is recorded in P3A.md "Deviations" 2. No change.
- **c4 (cosmetic, test coverage). No test makes `N''_ν ≠ ∅` under `OVHyp`/`IsTauRun`** (§2). This cannot be fixed by `decide` at the sizes it needs. It is acceptable because the statements are proved; flagged only so that the audit knows the quantitative content is checked by proof alone.

## 6. Math findings (manuscript)

- **L14-C-TAU0 (T1), confirmed.**
  - The hypothesis `τ ≥ 128 s log²n_0` allows `τ = 0` when `n_0 = 1`. Lean also allows it at `n_0 = 0`, since `logb 2 0 = 0`.
  - The τ-run is then one leaf with count 0, and (c) claims `0 ≤ ⌈0⌉ − 1 = −1`.
  - The proof's "If `n_0 = 1` … everything is trivial" misses this item.
  - The repair `0 < τ` is minimal (it is Lemma thin cut's own hypothesis). It holds in every application (`τ_l ≥ 128`).
  - Manuscript fix: add "if `τ > 0`" to (c), or assume `n_0 ≥ 2`.
- No other doubt. I re-derived the following and found them correct:
  - SEP (i)–(iii): the "deepest ancestor" argument of (iii);
  - both thin-cut cases (Case A through `H_in`, Case B through `H_out`);
  - OV (a): the chain charge with ratio `4/3`, and `1 + 1/c_OV = 3.4094 ≤ 3.42`;
  - OV (c) and the instance (`(33/32)(2/3) < 3/4`, `1.1197 ≤ 1.12`);
  - 14^τ (a), the per-split counting: `τ(|H_out|+|H_in|) ≤ |F_0|`, `0.6979 ≤ 0.698`, `log₂0.698 = −0.5187 < −2/5`;
  - the two induction inequalities (8) and (9): `6ε/log m ≤ 3/16 < 3/5`, `3ε = 3/32 < 1/10`, `7L²−3.6L−3.2 ≥ 0.2` at `L = 1`;
  - 14^τ (b) constants;
  - lemGC (iii) via EL, or directly via (R5);
  - lemTower (c) arithmetic: `257·4 < 2^{11}`, `λ^{102.5} > 2^{111}λ^{102}`.
