# P3B: clean-room review, round 2 (Specs of probe P-3, part 2)

Reviewer: clean-room Spec reviewer, round 2 (2026-09-29). I did not edit any Lean file in the repo.
My scratch checks are in the session scratchpad
(`/tmp/claude-0/-home-user-Erdos-Proof/ab92a43f-e615-5aab-870d-cceae4796e61/scratchpad/P3BReview2.lean`),
outside the repo; `lake env lean` compiles them with 0 errors (one unused-variable warning, which
is itself informative, see §2). The proof being formalized is a CANDIDATE proof, reviewed only by
AI; nothing here says the conjecture is solved.

**Verdict: APPROVE** (0 major, 0 minor, 4 cosmetic; no math finding of class T1–T3; two T0
confirmations).

- Every Spec and both new Defs files back-translate to `s2.tex` / `s6.tex` v6.1 (§1). Every
  deviation is either a strengthening that I re-derived as true from the locked Defs, or the
  standing assumption Γ made explicit.
- No hypotheses are contradictory; the only trivially true conjuncts are the ones the TeX itself
  makes definitional ("standalone ⇒ no (α)") or the exclusivity halves of "exactly one" (§2).
- The declared inputs are used by the manuscript proofs, are stated as in the TeX, and hide no
  probe node (§3). `python3 -I scripts/lint.py`: 0 findings (§4).
- **Refutation target (CONC-L (iv) per-ancestor bound):** re-derived independently against the
  locked Defs; it holds in the strengthened Lean form (every ancestor, every `l`, no Γ) (§5).
- Round-1 fixes (M1, C1–C4) are in place and correct (§7).

Files read in full: `EG/Defs/Probe/P3B/{Origin,TowerFns}.lean`; `EG/Spec/HB/{Origin,TowerA,
OVRunK,LacunaryGeom}.lean`; `EG/Spec/Chain/{ConcTower,CONC,CONCL}.lean`; the stubs
`EG/Proof/HB/{TowerA,OVRunK,LacunaryGeom}.lean` and `EG/Proof/Chain/ConcTower.lean`;
`EGTest/ProbeP3B.lean`; the locked Defs `EG/Defs/HB/{SplitTree,Round,Run}.lean`,
`EG/Defs/Chain/{Design,Constants}.lean`, `EG/Defs/Log.lean`, `EG/Defs/Gamma/Core.lean`,
`FGraph.eBetween`/`edgesBetween`, `IsExpander`; the P3A Specs `EG/Spec/HB/{ThinCut,GC,TowerC}.lean`
and the pre-existing `EG/Spec/HB/{Overlap,TowerB,TowerBLate}.lean` (no overlap with the new
inputs: `Overlap.lean` is lemOVgeneric, not propOV); `work/p2b/{P3B,P3B.review1,P3A}.md`;
blueprints s2b (propOV, lemLacunary, lemTower, propOrigin), s6a (thmCONC), s6b (thmCONCL);
TRIAGE §2.3, §2.6, §2.9, §4; `work/p2d/{hb,design}.md` (relevant parts).

TeX read: `s2.tex` defHBtp (R0)–(R5) (l.503–598), defAncestors (l.600–633), lemCap (l.635–660),
lemEL (l.821–836), lemThinCut (l.220–245), propOV statement (l.839–864), propDegRec statement
(l.922–944), lemLacunary (i) (l.1035–1039), lemTower statement and proof of (a) (l.1144–1215),
lemGC (l.1282–1300), propOrigin with proof (l.1320–1410); `s6.tex` l.234–388 (defDesign, the `log*`
facts, (eqTowerHalf)/(eqTowerEnd) with proof, thmCONC and thmCONCL with proofs).

## 1. Fidelity (back-translation vs TeX)

Notation: a valid run `run.Valid G D`; rounds `[1,R]`; a pre-part is an address
`a ∈ prePartAddrs G r`; `Y^0 = Z0`, `S_Y = guests`, `X^0_Y = X0`, `Dup*_r = DupStar`; `log = logb 2`,
`log* = logStar`, `k_* = log* D`, `n = G.card`; Γ = `Gamma1core D`. `𝒫 = pieceOf r a` (the leaf of
the `s = 0` tree on the path `a`).

### New Defs (`EG/Defs/Probe/P3B/`)

| Def | Back-translation | TeX | OK |
|---|---|---|---|
| `Run.OriginBeta r a u x` | `x ∉ Y^0 ∧ s(u,x) ∈ deleted(τ-run of 𝒫, rooted at the piece graph)` | "(β) `x ∉ Y^0`, and `ux` was deleted by the `τ`-run of `𝒫`" | yes; blueprint OR-TYPE-DEF form |
| `Run.OriginAlpha r a u x` | `Y light ∧ x ∈ S_Y ∧ s(u,x) ∈ E(X^0_Y)` | "(α) `Y` is light, `x ∈ S_Y`, and `ux ∈ E(X^0_Y)`" | yes |
| `towA/towB/towC d` | `(2 log* d + 2)/log d`, `(2 log* d + 1)/log log d`, `(2 log* d + 1)/(log d)^{1/2}` (rpow `1/2`; `a / b ^ c` parses as `a/(b^c)`) | display before (eqTowerHalf) | yes |

Junk reads: `OriginBeta` reads `tauRun r (pieceOf r a)` only at pre-part addresses; every pre-part
is `q ++ b` with `q` a big piece (`Round.prePartAddrs` filters leaves of `twoLevel` by `|X0| ≥ P`,
and a small piece is its own leaf with `|X0| < P`), so `tauRun` is read only where `Round.Valid`
constrains it. This includes the junk case `P_r = 0` (`d_r ≤ 1`), where every piece is big. Both
predicates are total and the Specs read them under the stated hypotheses only.

### ORIGIN^τ (`EG/Spec/HB/Origin.lean`)

- **`OriginTypesStatement`.** Every valid run, `r ∈ [1,R]`, pre-part `a`, `u ∈ Y^0 \ Dup*_r`:
  (1) `𝒫` is a piece; (2) a piece contains `u` iff it is `𝒫`; (3) a leaf `b` of the two-level
  recursion contains `u` (`u ∈ Z0 r b`) iff `b = a`; (4) `Y^0 ⊆ V(𝒫)`; (5) for every `l > r` and
  every `x` with `ux ∈ E(G_l)`: (β ∧ `x ∈ V(𝒫)` ∧ ¬α) ∨ (α ∧ ¬β ∧ `ux` not deleted by the τ-run
  of `𝒫`); (6) standalone ⇒ no (α) edge of any `G_l`, `l > r`.
  - TeX (a) verbatim, plus the parentheticals "(so `Y^0 ⊆ V(𝒫)`)", "(so `x ∈ V(𝒫)`)", "not
    deleted", and "the same classification applies to `G_l`". Faithful.
  - Deviation: no Γ (TeX standing assumption). Re-derived as true for every valid run: the proof
    uses only WF of the two-level recursion (`Valid.wf_twoLevel`), SEP (0)/(i)/(ii), "`s = 0`
    splits delete nothing" (`N'' = Nbr(U)` ⇒ `F'' = ∅`), `D_r ⊆ Dup*_r`, and (R5)(1) through
    `Round.assign` step (1). None needs a condition on `D_*`.
  - `l` ranges over all `l > r` including `l > R + 1` (`G_l` stationary); harmless.
- **`OriginThinStatement`.** `∀ h, ∀ l > r`: `#{u ∈ Y^0 \ Dup*_r : hu ∈ E(G_l) ∧ hu is (β) with
  core end u} ≤ τ_r − 1`. TeX (b) literally. The ℕ-subtraction is exact: I proved
  `1 ≤ tauOf d` for **every** real `d` in scratch (`M ≥ 2^{40} ⇒ Λ ≥ 40 ⇒ s ≥ 1 ⇒ τ ≥ 128·1600`),
  so `≤ τ_r − 1` is `< τ_r` (the blueprint's OR-TAU-NAT form); see C1 on the missing Lib lemma.
  True without Γ: thin cut on the τ-run of `𝒫` needs `IsTauSplitTree ε τ_r` from `IsTauRun ε s_r
  τ_r`, i.e. `(s_r : ℝ) < τ_r`, which holds for every `d`; `Dup(τ-run) ⊆ Dup*_r`
  (`tauRun_dup_subset_DupStar`); `u ↦ s(h,u)` injective.
- **`OriginGuestCapStatement`.** Light `a`, guest `x`, `l > r`: `#{u ∈ Y^0 \ Dup*_r : ux ∈ E(G_l)
  ∧ α} < θ^GC_r(Y^0)`. TeX final paragraph, middle clause (edges ↔ core ends, injective). True for
  every valid run: `u ∉ D_r ⊇ S_Y`, so `u ∈ N_{X^0}(x) ∩ (Y^0 \ S_Y)`, bounded by `isGC` (part of
  `isLight`).
- (c) is (K3): pointer to `OVK3Statement` (blueprint OR-C-POINTER). Agreed.

### `log*` and tower facts (`EG/Spec/Chain/ConcTower.lean`)

| Spec | Back-translation | OK |
|---|---|---|
| `LogStarFactsStatement` | `x ≥ 1`: `log* x ≤ k ↔ x ≤ 𝖳_k`; `x > 1`: `log* x = 1 + log*(log x)`; `x ≥ 1`: `log* x ≤ 1 + log x` | yes (proved, `EG.logStarFacts`) |
| `KStarStatement` | Γ ⇒ `2^8 ≤ loglog D`, `16 < loglog D`, `𝖳_5 < D`, `6 ≤ log* D` | yes (`𝖳_5 = 2^{65536}`; `log* D ≥ 6 ⇔ D > 𝖳_5`) |
| `TowerHalfStatement` | Γ, valid run, `r ∈ [1,R)`: `𝖺(d_r) ≤ 𝖺(d_{r+1})/2`, same for `𝖻`, `𝖼` | yes; `r < R ⇒ R ≥ 2 ⇒ d_1 ≥ D` (so the input `TowerA` applies) |
| `TowerEndStatement` | Γ, real `d ≥ D`: `𝖺(d) ≤ (2k+4)/log D`, `𝖻(d) ≤ (2k+3)/loglog D`, `𝖼(d) ≤ (2k+3)/(log D)^{1/2}` | yes |

I re-derived both TeX proofs independently (all steps, including the three monotonicities for
`t ≥ 4` by derivative sign, `2^{y/(2A)} ≥ 16y²` from `y ≥ 2^{14}Av³`, `y ≥ 2Av(7+2v)`,
`t(2t+7) ≤ 9t² ≤ 2^t`, `t(2t+5)² ≤ 49t³ ≤ 2^t` from Γ1(b), and both cases of (eqTowerEnd)). Correct.

### Theorem CONC (`EG/Spec/Chain/CONC.lean`)

| Spec | Back-translation | OK |
|---|---|---|
| `ConcIStatement` | valid run, `a ∈ Std_r`, `l ≥ r+1`, `h : V`: `#{u ∈ Y^0∖Dup*_r : hu ∈ E(G_l)} ≤ τ_r − 1` | yes (no δ: (i) does not read it; no Γ: from ORIGIN (a),(b)) |
| `ConcIIStatement` | valid run, δ, `a ∈ Std_r`, every `l`: `m_{Y,l} ≤ τ_r − 1 + d*_{Y,l}` | yes (no Γ; re-derived: ports `∉ Dup*` by (i), ports `∈ Dup*` distinct and counted by `d*`) |
| `ConcIIIStatement` | Γ, valid, δ: `Σ_{l∈[1,R]} Σ_{Y∈stdParts} m_{Y,l} ≤ 2^{σ+14} n k/log D + 100 ε n k/(C' loglog D)` | yes |
| `ConcTauSumStatement` | Γ, valid: `Σ_{Y∈ancestors} Σ_{l∈[r(Y)+2,R]} (τ_{r(Y)} − 1) ≤ 2^{σ+14} n k/log D` | yes (the all-ancestor form CONC-L (iv) uses; CONC (iii)'s standalone sum is a sub-sum) |
| `ConcDStarSumStatement` | Γ, valid, δ: `Σ_{l∈[1,R]} Σ_{Y∈ancestors} d*_{Y,l} ≤ 80 ε n k/(C' loglog D)` | yes |

- Index sets: `m_{Y,l} = 0` unless `r(Y)+2 ≤ l ≤ R` (for `l ≤ 2` no classed ports since
  `anc l x` needs `Y.1 + 2 ≤ l` with `Y.1 ≥ 1`; for `l ≥ 3` `IsDesignation` forces `r+2 ≤ l`; for
  `l > R`, `Std_l = ∅`). `#Icc(r+2,R) = R−r−1`, the TeX's count.
- Constants re-checked: `1.37·16/3 = 7.31 < 8`; `2k+4 ≤ 8k/3` and `2k+3 ≤ 2.5k` for `k ≥ 6`;
  `log P_r ≥ C' log λ_r` from `P_r = ⌈λ^{C'}⌉`; `32·2.5 = 80 ≤ 100`.
- (iv) meta, no statement. Agreed.

### Theorem CONC-L (`EG/Spec/Chain/CONCL.lean`)

| Spec | Back-translation | OK |
|---|---|---|
| `ConcLIStatement` | light `a`, `l ≥ r+1`, `h ∉ S_Y`: `#{u ∈ (Y^0∖S_Y)∖Dup*_r : hu ∈ E(G_l)} ≤ τ_r−1`; if also `h ∈ Y^0∖S_Y` the set is `∅` | yes (no Γ) |
| `ConcLIIStatement` | `h ∈ S_Y`: each such `hu ∈ E(X^0_Y)`; count `≤ e_{X^0_Y}({h}, Y^0∖S_Y)` | yes; `eBetween A B = #E(A,B)` with `{h}`, `Y` disjoint as the conventions require |
| `ConcLIIIStatement` | δ, light `a`, `l ≥ r+1`: `m ≤ max(τ−1, α) + d*` | yes (no Γ) |
| `ConcLAlphaStatement` | Γ, δ, light `a`, `l ≥ r+1`: `α_{Y,l} < θ^GC_r(Y^0)` | yes (Γ = standing assumption; T0-CONCL-ALPHA) |
| `ConcLPerAncestorStatement` | valid, δ, every `Y ∈ ancestors`, every `l`: light ⇒ `m ≤ (τ−1)+(θ−1)+d*`; else `m ≤ τ−1+d*` | yes (stronger: every `l`, no Γ; §5) |
| `ConcLGCSumStatement` | Γ, valid: `Σ_{Y∈lightParts} Σ_{l∈[r+2,R]} θ^GC ≤ 4n(2k+2)/(log D)^{1/2}` | yes |
| `ConcLSumStatement` | Γ, valid, δ: `Σ_{l∈[1,R]} Σ_{Y∈ancestors} m ≤ ε_CONC(D)·n` | yes (`epsCONC` is the displayed formula, checked against the locked Def) |
| `EpsCONCTendstoStatement` | `Tendsto epsCONC atTop (𝓝 0)` | yes |

- `alphaY` reads `ancVerts Y = Z0 \ guests` for light `Y` (`Round.partVerts`), `Dup*_{r(Y)}`, and
  the witnessing `Z_u` as `∃ a ∈ Std_l, u ∈ Q_a ∧ δ l u = Y ∧ s(x,u) ∈ E_l(a)`: literal.
- θ^GC-sum re-checked: `θ ≤ |Y^0|λ^{-1/2} + 1`; `1.37n/P_r ≤ 0.01 n λ^{-1/2}` needs
  `P_r ≥ 137 λ^{1/2}`, true from `P_r ≥ λ^{103}`, `λ ≥ 2^{256}`; `R−r−1 ≤ 2log* d_r + 1`;
  `2.76(2k+3) ≤ 4(2k+2)` for `k ≥ 1`. Correct.

### Declared inputs

| Spec | Back-translation | OK |
|---|---|---|
| `TowerAStatement` | Γ, valid, `D ≤ d_1`: `d_{r+1}^{1/A} ≤ λ_r` (`r∈[1,R]`); `d_{r+2} ≤ λ_r` (`1≤r`, `r+1≤R`); `(R:ℤ)−r ≤ 2log* d_r − 1` and `≤ 2log* d_r + 2` (`r∈[1,R]`); `λ_{l−2} ≤ λ_r` (`1≤r`, `r+2≤l≤R+2`) | yes; lemTower (a) verbatim |
| `OVK1Statement` | `Gamma2a`, valid; `r∈[1,R]`: `Σ_a|Z^0| ≤ 1.37n`, `|Std_r| ≤ 1.37n/P_r`, `#{Y∈anc : r(Y)=r} ≤ 1.37n/P_r`; every `l`: `ν_l ≤ 1.37n Σ_{r∈[1,R], r+2≤l} 1/P_r` | yes; scratch: `#{Y∈anc : r(Y)=r} = #prePartAddrs r` (for every `r`) |
| `OVK3Statement` | `Gamma2a`, valid, `r∈[1,R]`: `Σ_{a fails L1}|Z^0| ≤ 30.4εn/log P_r`; `Σ_a|Z^0∩Dup*_r| ≤ 16εn/log P_r` | yes |
| `LacunaryGeomStatement` | `R ≥ 1`, `X ≥ 0` on `[1,R]`, `X_r ≤ X_{r+1}/2` on `[1,R)`: `ΣX ≤ 2X_R`, `Σ(R−r+1)X_r ≤ 4X_R` | yes (`R ≥ 1` implicit in "`X_1,…,X_R`") |

I read the TeX proof of lemTower (a) (l.1183–1200): the `R − r ≤ 2k − 1` bound comes from the
induction `d_{r+2i} ≤ log^{[i]} d_r` for `i ≤ k = log* d_r`, using `log^{[i]} d_r > 1` for `i < k`
and `log^{[k]} d_r ≤ 1` — exactly the semantics of the Lean `logStar` (`sInf {k | logIter k x ≤ 1}`).
The input is stated as the TeX has it and its hypotheses (Γ1core, `d_1 ≥ D_*`) cover what its proof
uses (propDegRec: Γ1(a),(b), lemCap(ii) ⇐ Γ2a ⇐ Γ1core; Γ1(c); propStructure(iii)).

## 2. Vacuity

- **Hypotheses satisfiable.** As `EGTest/ProbeP3B.lean` shows: `run1` on `K3` (valid, round 1, a
  light pre-part, `u ∉ Dup*`), every `δ` a designation; `Gamma1core D` + the run without rounds +
  a designation for the Γ-statements; `TowerEnd`/`KStar` at `d = D`; Lacunary at `X_r = 2^r`. I
  found no contradictory combination (`Valid` contains no Γ; Γ constrains only `D`).
- **Conclusions not trivial**, except: (a) "standalone ⇒ no (α)" (definitional, kept for fidelity,
  documented); (b) the exclusivity halves `¬α` in the (β) branch and `¬β` in the (α) branch of
  `OriginTypesStatement` are each implied by the branch's first conjunct (scratch check (6):
  `α → ¬β` via `S_Y ⊆ Y^0`). This is exactly the TeX's "the types are exclusive (`x ∉ Y^0` in (β),
  `x ∈ S_Y ⊆ Y^0` in (α))", so it is faithful, not a defect. `KStarStatement`'s `16 < loglog D`
  is implied by `2^8 ≤ loglog D` (the TeX chain).
- **Degenerate witnesses only** (Γ-statements with `R = 0`; ORIGIN/CONC with no (β)-edge, guest or
  class). Intrinsic for the Γ-statements; round-1 M1's sign checks are in the test file and I
  re-read them. See C3 for guests.
- **Scratch checks** (all compile): (1) `α ≤ θ−1 → m ≤ max(τ−1,α)+d → m ≤ (τ−1)+(θ−1)+d` and
  `α < θ → α ≤ θ−1` in ℕ; (2) `guests = ∅ → alphaY = 0`; (3) `#((ancestors).filter (·.1 = r)) =
  #(prePartAddrs r)` for every `r` (the `r ∈ [1,R]` hypothesis is unused: `prePartAddrs` is
  guarded); (4) `(0:ℝ)^(-(1/2)) = 0`, `thetaGC 1 5 = 0`, and `λ^(-(1/2)) = 0` for `λ < 0`
  (`Real.rpow_def_of_neg`, `cos(−π/2) = 0`); (5) `1 ≤ tauOf d` for every real `d`; (6) `α → ¬β`.

## 3. Declared inputs

- **Used by the manuscript proofs:** `TowerA` — τ-sum ("`R−r ≤ 2log* d_r + 2`"), d*- and θ-sums
  ("`R−r−1 ≤ 2log* d_r + 1`"), (eqTowerHalf) ("`x ≥ d_{r+1}^{1/A}` by Lemma tower (a)"); `TowerC`
  (P3A stub) — "`τ_r/P_r ≤ 2^{σ+11}/λ_r`"; `OVK1` — "`|Std_r| ≤ 1.37n/P_r`", "ancestors of round
  `r` ≤ 1.37n/P_r", "`Σ|Z^0| ≤ 1.37n`" in the θ-sum; `OVK3` — the d*-term; `LacunaryGeom` — every
  tower sum. The ν_l clause of `OVK1` and the unused clauses of `TowerA` are stated for the
  future full Specs (the docstrings say "import, do not restate"); they are TeX-literal.
- **No probe node is hidden.** TRIAGE §4 P-3 lists propOrigin (a),(b), CONC (i)–(iii), CONC-L (iv)
  with the shared sums and the tower facts as the probe nodes; all have Specs and are stage-2
  obligations. propOV, lemTower and lemLacunary are not in the chain.
- **Hypothesis sufficiency** (a `sorry`'d stub with too few hypotheses would be a false axiom):
  `TowerA` (Γ1core + `d_1 ≥ D`) — checked above; `OVK1`/`OVK3` (`Gamma2a`) — the proof needs
  Lemma 14^τ(b) for every τ-run via lemCap(ii) (`|𝒫| ≤ M_r`, from Lemma 25 at `m ≥ 2^{40}`,
  `T ≥ 2^{117}`) and `P_r ≥ 2`; both follow from `D ≥ 2^{117}` (blueprint OV-IMPLICIT-DSTAR);
  `LacunaryGeom` — pure arithmetic, true.
- Hypotheses added to inputs (`Gamma1core`, `Gamma2a`) only weaken the stubs, and the uses derive
  `Gamma2a` from `Gamma1core` (`Gamma1core.gamma2a`).

## 4. Hygiene

- `python3 -I scripts/lint.py`: `lint (development): 0 findings`.
- Every statement is `def …Statement : Prop` with a docstring starting with the label and quoting
  the TeX; the four stubs have the `[DECLARED INPUT] [label]` form and are the only `sorry`s.
- New Defs under `EG/Defs/Probe/P3B/` as `module` / `@[expose] public section`. `git status` shows
  no locked file modified by this unit (the modified files are other units' work).
- `open Classical in` is used exactly where a filter predicate is not decidable
  (`OriginBeta`/`OriginAlpha`, `isL1`).

## 5. Refutation target: the CONC-L (iv) per-ancestor bound

Independent re-derivation against the locked Defs (`classDeg`, `mY`, `dStar`, `alphaY`,
`IsDesignation`, `anc`, `partVerts`, `E`, `assign`). Fix `Y = (r,a) ∈ ancestors`, `l`, `δ`, `h`.

1. `classDeg Y l h` counts edges `e ∈ ⋃_{Z∈Std_l} E_l(Z)` with `∃ u ∈ Q_Z, e = s(h,u) ∧ δ l u = Y`.
   Each edge at `h` determines `u` (loopless), so `classDeg ≤ #{u : ∃ Z ∈ Std_l, u ∈ Q_Z ∧ δ l u = Y
   ∧ s(h,u) ∈ E_l(Z)}`. For `l ≤ 2`, `Q_Z = ∅`; for `l ≥ 3`, `δ l u ∈ anc l u` gives `r + 2 ≤ l`
   and `u ∈ V(Y)`. So `m_{Y,l} = 0` unless `r + 2 ≤ l ≤ R`, and then every counted edge is in
   `E_l(Z) ⊆ E(G'_l) ⊆ E(G_l) ⊆ E(G_{r+1})`.
2. Ports `u ∈ Dup*_r`: distinct `u`, each a classed port of round `l` with `δ l u = Y` and
   `u ∈ Dup*_{Y.1}`: `≤ dStar Y l`.
3. Ports `u ∉ Dup*_r`: `u ∈ V(Y) ⊆ Y^0`, so ORIGIN (a) classifies `hu`.
   - `Y` standalone (GC-parts included; `¬isLight`): no (α) (definitional), so all such edges are
     (β) and ORIGIN (b) gives `≤ τ_r − 1`. Hence `m ≤ τ_r − 1 + d*` (= CONC (ii)).
   - `Y` light, `V(Y) = Y^0 \ S_Y`. Exactly one of: `h ∉ Y^0` (all (β), `≤ τ_r − 1`); `h ∈ Y`
     (neither type: none); `h ∈ S_Y` (each such `u` is a witness of the `alphaY` set at `x = h`,
     with the same `Z`, so `≤ α_{Y,l}`).
4. `α ≤ θ^GC − 1` in ℕ for every valid run: if `S_Y = ∅`, `α = 0` (scratch (2)); otherwise for
   each `x ∈ S_Y` the α-set's edges are (α) by ORIGIN (a) (`x ∈ S_Y ⊆ Y^0` excludes (β)), hence
   `X^0_Y`-edges from `x` into `Y^0 \ S_Y`, and `isGC` (part of `isLight`) gives `< θ^GC`; the
   `sup` over `S_Y` is then `< θ^GC`, so `≤ θ^GC − 1`. (If `θ^GC = 0`, `isGC` forces `S_Y = ∅`.)
5. So `m ≤ max(τ−1, α) + d* ≤ (τ−1) + (θ−1) + d*` (scratch (1)). **No counterexample; the bound
   holds in the strengthened form (every `l`, no Γ).** It remains the stage-2 obligation
   `EG.concLPerAncestor`.

Failure points probed: a port `u ∈ S_Y` (excluded by `V(Y)` and by `u ∉ D_r ⊇ S_Y`); an edge at
`u` neither in a leaf nor deleted (SEP (ii) on the WF two-level recursion, `u ∉ Dup*_r`); a
first-level deletion (`s = 0` splits delete nothing); thin cut needing `Dup` of the τ-run
(`Dup(τ-run) ⊆ Dup*_r`); `h ∉ V(𝒫)` (then no (β) edge at all); `h ∈ Dup*_r` (irrelevant to the
case split on `h`); `θ^GC − 1` at `θ^GC = 0` (then `S_Y = ∅`, `α = 0`). None opens a gap.

## 6. Issues

- **C1 (cosmetic, documentation).** `work/p2b/P3B.md` (hazards H4, H5) cites a Lib lemma
  `one_le_tauOf` ("`τ_r ≥ 1` for every `d`"); no such lemma exists in `EG/` (`grep` over `EG`,
  `EGTest`: no hit). The fact is true and short (my scratch proof: `2^{40} ≤ MOf d` ⇒
  `40 ≤ LamOf d` ⇒ `1 ≤ sOf d` ⇒ `1 ≤ tauOf d`, ~25 lines with `Nat.le_ceil`,
  `Real.logb_le_logb_of_le`, `one_le_pow₀`, `Nat.ceil_eq_zero`). The exactness of every
  `τ_r − 1` in the Specs rests on it, so stage 2 must prove it; the design note should say
  "to be proved" rather than name it as existing. No Spec change.
- **C2 (cosmetic, wording).** `EG/Defs/Probe/P3B/TowerFns.lean` still labels the three Defs
  "`[s6:thmCONC] (preamble …)`", while round-1 C3 reworded `ConcTower.lean` to "(s6, text before
  s6:thmCONC, not part of the theorem …)". Make the Defs file consistent so nobody reads `𝖺, 𝖻, 𝖼`
  as part of the theorem.
- **C3 (cosmetic, non-vacuity).** The hypotheses of `OriginGuestCapStatement` (a light part with
  a guest `x ∈ S_Y`) and of `ConcLIIStatement` (`h ∈ S_Y`) have no witness in `EGTest/ProbeP3B.lean`
  (`run1` has no guests). The design note's reason ("a τ-run split needs a non-`(ε, s_r)`-expander
  with `s_r ≥ 40^{100}`") rules out (β)-edges at toy size, but a guest needs only a **first-level**
  `s = 0` split (two pieces sharing `Nbr(U)`, both of size `≥ P_r`, with `P_r = 1` for
  `d ∈ (1,2]`), which that argument does not exclude; `EGTest/HB.lean`'s `StandaloneTest` has
  guests but is explicitly "not a valid round". Optional for stage 2: try a valid one-round run
  on a small non-`(ε,0)`-expander `G'_1` (e.g. a disconnected graph) to witness a guest; if no
  valid `s = 0` witness exists at that size, record the reason.
- **C4 (cosmetic, design note).** T0-CONCL-ALPHA says `θ^GC = 0` "when `λ_r = 0` (e.g. `d_r = 1`)".
  In Lean `λ^{-1/2} = 0` for every `λ ≤ 0` (`Real.rpow_def_of_neg` with `cos(−π/2) = 0`; scratch
  (4)), i.e. for every `d_r ≤ 1`, not only `d_r = 1`. The conclusion (carry `Gamma1core` on
  `ConcLAlphaStatement`) is unchanged; "not exhibited on a valid run" still stands.

## 7. Round-1 fixes verified

- M1: the sign checks are in `EGTest/ProbeP3B.lean` ("Sign checks of the right-hand sides under
  Γ1"); each RHS of `ConcTauSum`, `ConcDStarSum`, `ConcIII`, `ConcLGCSum`, `ConcLSum`
  (`epsCONC_pos`) and `TowerEnd`, and `towA/B/C d` for `d ≥ D`, is proved `> 0`. Compiles.
- C1: docstring remark on the definitional standalone clause present in `Origin.lean` (module and
  statement docstrings).
- C2: the (α) branch now carries `s(u,x) ∉ deleted(τ-run of 𝒫)`; true (SEP (i) on the τ-run,
  whose leaf graph at the suffix address is `X^0_Y`), documented, nothing downstream reads it.
- C3: `LogStarFactsStatement`/`KStarStatement`/`EG.logStarFacts` say "(s6, text before
  s6:thmCONC, not part of the theorem …)". (The Defs file was not updated: C2 above.)
- C4: T0-CONCL-ALPHA now says "can fail" and states that no valid run was exhibited.

## 8. Answers to the open questions (reviewer's view, unchanged from round 1)

1. Lacunary (i) as a declared input: acceptable; assigning it to P3B stage 2 removes a stub.
2. ORIGIN (c) as a pointer to `OVK3Statement`: acceptable.
3. Shared sums over all ancestors: acceptable (the TeX says CONC-L reuses them "verbatim").
4. `ConcLAlphaStatement` with `Gamma1core`: acceptable; the per-ancestor bound the sum consumes
   needs no Γ, so a Γ-free variant is optional.
5. Ownership docstrings on the input Specs: adequate.

## 9. Math findings (manuscript)

None of class T1–T3. T0 confirmations:
- **T0-CONCL-ALPHA** (confirmed, sharpened): the Lean claim `α_{Y,l} < θ^GC_r(Y^0)` can fail
  only through the junk `θ^GC = 0`, which happens exactly when `λ_r ≤ 0` (`d_r ≤ 1`), unreachable
  under the standing assumption; the Spec carries `Gamma1core`.
- **T0-CONCL-EL** (confirmed): CONC-L (i)'s "no such `u` if `h ∈ Y`" follows from ORIGIN (a)'s
  exclusivity; Lemma EL is provenance.
- ORIGIN (a),(b), CONC (i),(ii), CONC-L (i)–(iii) and the per-ancestor bound hold with no
  condition on `D_*`; the manuscript's parenthetical appeal to lemCap (ii) in ORIGIN (a) is not
  needed for (a),(b).
All computations of (eqTowerHalf), (eqTowerEnd), CONC (iii) and CONC-L (iv) re-derived; correct.
