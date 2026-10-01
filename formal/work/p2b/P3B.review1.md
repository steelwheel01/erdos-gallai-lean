# P3B: clean-room review, round 1 (Specs of probe P-3, part 2): re-run 2026-09-30

Reviewer: clean-room Spec reviewer (round 1, re-run of 2026-09-30). I edited no Lean file in the repo.
My scratch checks are in `/tmp/p3brev/Scratch.lean`, outside the repo; `lake env lean` compiles them
with 0 errors. The proof being formalized is a CANDIDATE proof, reviewed only by AI. Nothing here says
that the conjecture is solved.

(This file replaces the earlier round-1 review of 2026-09-29. Its items M1, C1–C4 are cited in
`P3B.md` "Fix round 1" and are still available in git history. I formed my verdict independently,
before reading that review.)

**Verdict: APPROVE.** 0 major, 0 minor, 4 cosmetic. No math finding of class T1–T3. One T0 note is
confirmed in Lean (T0-CONCL-ALPHA).

## Files and TeX read in full

- New Defs: `EG/Defs/Probe/P3B/{Origin,TowerFns}.lean`.
- Specs:
  - `EG/Spec/HB/{Origin,TowerA,OVRunK,LacunaryGeom}.lean`;
  - `EG/Spec/Chain/{ConcTower,CONC,CONCL}.lean`.
- Stubs and proofs:
  - `EG/Proof/HB/{TowerA,OVRunK,LacunaryGeom}.lean`: exactly one `sorry` per declared input;
  - `EG/Proof/Chain/ConcTower.lean`: no `sorry`.
- Locked Defs used in the back-translation:
  - `EG/Defs/HB/{SplitTree,Round,Run}.lean`;
  - `EG/Defs/Chain/{Design,Constants}.lean`;
  - `EG/Defs/{Log,Gamma/Core}.lean`;
  - `FGraph.{nbrs,nbrSet,edgesBetween,eBetween}`.
- Other units' Specs:
  - `EG/Spec/HB/TowerC.lean`, the existing input;
  - `EG/Spec/HB/TowerBLate.lean`, checked for clashes with (K1). There are none.
- TeX, `s2.tex`:
  - lemGC, propOrigin and its proof (l.1282–1412);
  - lemThinCut (l.220–260) and defTauRules (l.71–90);
  - propOV (l.839–860), lemCap (l.635–651) and propDegRec (l.922–946);
  - propStructure header (l.722–742);
  - lemLacunary (l.1035–1050), lemTower and the proof of (a)–(e) (l.1144–1280);
  - the standing assumption (l.24–29).
- TeX, `s6.tex` l.234–388: defDesign, the `log*` facts, (eqTowerHalf) and (eqTowerEnd) with their
  proof, thmCONC and thmCONCL with their proofs.
- Also read: TRIAGE §2.6 and §4 row P-3, and the blueprints s2b (OV-*, TOW-*) and s6a/s6b (CONC-*, CONCL-*).

## 1. Fidelity: back-translation of every Spec and new Def, compared with the TeX

Notation:
- a valid run is `run.Valid G D`;
- rounds are `[1,R]`, and a pre-part is an address `a ∈ prePartAddrs G r`;
- `Y^0 = Z0`, `S_Y = guests`, `X^0_Y = X0`, `Dup*_r = DupStar`;
- `log = logb 2`, `log* = logStar`, `n = G.card`;
- Γ = `Gamma1core D`.

### New Defs

- **`Run.OriginBeta r a u x`**
  - Lean: `x ∉ Y^0` and `s(u,x) ∈ deleted` of the tree `tauRun r (pieceOf r a)`, rooted at the piece
    graph `piece G r (pieceOf r a)`.
  - TeX (β): "`x ∉ Y^0`, and `ux` was deleted by the `τ`-run of `𝒫`". Faithful.
  - The tree is read at `pieceOf r a`. For a pre-part `a` that piece is always **big**:
    - a pre-part is a leaf of `twoLevel` with at least `P_r` vertices;
    - below a small piece the graft is `.nil`, so the leaf would be the piece itself, with fewer than
      `P_r` vertices.
  - So `tauRun` is read only where `Round.Valid` constrains it and where `twoLevel` grafts it, as
    CONVENTIONS requires. No junk-tree hazard.
- **`Run.OriginAlpha r a u x`**
  - Lean: `isLight ∧ x ∈ S_Y ∧ s(u,x) ∈ E(X0)`. This is the literal (α).
- **`towA`, `towB`, `towC`** are `(2log*d+2)/log d`, `(2log*d+1)/log log d` and `(2log*d+1)/(log d)^{1/2}`.
  - Scratch check: `towC d = … / (Real.logb 2 d) ^ ((1:ℝ)/2)` holds by `rfl`. The exponent applies to
    `log d`, not to `d`. The same holds for `epsCONC`.

### ORIGIN^τ (`EG/Spec/HB/Origin.lean`)

- **`OriginTypesStatement`**
  - Lean: for a valid run, `r ∈ [1,R]`, `a` a pre-part and `u ∈ Y^0 \ Dup*_r`, all of the following hold:
    1. `pieceOf r a` is a piece;
    2. a piece contains `u` iff it is `pieceOf r a`;
    3. a leaf `b` of `twoLevel` contains `u` iff `b = a`;
    4. `Y^0 ⊆ V(𝒫)`;
    5. for every `l > r` and every edge `ux ∈ E(G_l)`, exactly one of two cases holds:
       - (β), `x ∈ V(𝒫)` and ¬(α);
       - (α), ¬(β) and `ux` not deleted by the `τ`-run of `𝒫`;
    6. if `Y` is not light, no such edge is (α).
  - This matches TeX (a) sentence by sentence. The additions are strengthenings, each of which I
    re-derived:
    - "exactly one" is encoded as an exclusive disjunction;
    - the two parentheticals ("so `x ∈ V(𝒫)`", "not deleted") are stated;
    - the claim is made for every `l > r`, not only `l = r+1`.
- **`OriginThinStatement`**
  - Lean: for every `h ∈ V` and `l > r`, `#{u ∈ Y^0\Dup*_r : hu ∈ E(G_l) ∧ (β)(u,h)} ≤ τ_r − 1`.
  - Literal TeX (b), with `ℕ`-subtraction. It is exact because `τ_r ≥ 1` for every `d`.
- **`OriginGuestCapStatement`**
  - Lean: for a light `Y`, a guest `x` and `l > r`, `#{u ∈ Y^0\Dup*_r : ux ∈ E(G_l) ∧ (α)(u,x)} < θ^GC_r(Y^0)`.
  - This is the middle clause of the final paragraph. The count is over vertices `u`; at a fixed `x`
    it equals the number of edges.
- ORIGIN (c) is not restated; it is the input `OVK3Statement`. This is acceptable because TeX (c)
  reads literally "(c) is (K3) of Proposition propOV".

### `log*` and tower facts (`EG/Spec/Chain/ConcTower.lean`)

- **`LogStarFactsStatement`**: the three facts, literally. It is proved with 0 sorry.
- **`KStarStatement`**: under Γ, `log log D ≥ 2^8`, `> 16`, `𝖳_5 < D` and `6 ≤ log* D`. Literal.
- **`TowerHalfStatement`**: under Γ, a valid run and `r ∈ [1,R)`, the three halving inequalities.
  - Literal, with the standing assumption made explicit.
  - `r < R` forces `R ≥ 2`, so `d_1 ≥ D` follows from `Valid`.
- **`TowerEndStatement`**: under Γ and for every real `d ≥ D`, the three bounds. Literal.
  - The constants `2k*+4` and `2k*+3` match.

### CONC (`EG/Spec/Chain/CONC.lean`)

- **(i)**: `∀ r, ∀ a ∈ Std_r, ∀ l ≥ r+1, ∀ h`: `#{u ∈ Y^0\Dup*_r : hu ∈ E(G_l)} ≤ τ_r−1`. Literal.
  - It has no δ, which is correct because (i) does not read δ.
  - It has no Γ, which is a strengthening. It is true because a standalone `Y` has no (α) edges and (b) applies.
- **(ii)**: `∀ δ` designation, `∀ a ∈ Std_r`, `∀ l`: `m ≤ τ_r−1+d*`. Literal. No Γ; I re-derived it.
- **(iii)**: under Γ, `Σ_{l∈[1,R]} Σ_{Y∈stdParts} m ≤ 2^{σ+14} n k*/log D + 100 ε n k*/(C' log log D)`.
  - Literal constants.
  - The index set is lossless: `m_{Y,l} = 0` for `l ∉ [r+2,R]`.
- **`ConcTauSumStatement`**: `Σ_{Y∈ancestors} Σ_{l∈[r+2,R]} (τ_r−1) ≤ 2^{σ+14} n k*/log D`.
  - This is the "verbatim" computation for all ancestors.
  - `#[r+2,R] = R−r−1`, the count the TeX uses.
- **`ConcDStarSumStatement`**: `Σ_{l∈[1,R]} Σ_{Y∈ancestors} d* ≤ 80 ε n k*/(C' log log D)`. Literal, and it covers all ancestors.

### CONC-L (`EG/Spec/Chain/CONCL.lean`)

- **(i), (ii), (iii)**: literal for a light part `Y = Y^0\S_Y` of round `r`, `l ≥ r+1` and `h`.
  - `e_{X^0_Y}(h,Y)` is `eBetween {h} (Y^0\S_Y)`. The two sets are disjoint because `h ∈ S_Y`, as
    CONVENTIONS require.
  - None of the three carries Γ. I re-derived each without it.
- **`ConcLAlphaStatement`**: `α < θ^GC` under Γ. See the T0 note in §5.
- **`ConcLPerAncestorStatement`** (the refutation target): for every ancestor `Y`, every `l ∈ ℕ` and every δ:
  - light `Y`: `m ≤ (τ−1)+(θ^GC−1)+d*`;
  - otherwise: `m ≤ τ−1+d*`.
  - This is literally the display in the proof of (iv), and it is strengthened in two ways: it holds
    for all `l`, and it has no Γ.
  - "GC-parts are standalone" is definitional: `¬isLight`.
- **`ConcLGCSumStatement`**: `Σ_{Y light} Σ_{l∈[r+2,R]} θ^GC ≤ 4n(2k*+2)/(log D)^{1/2}`. Literal.
- **`ConcLSumStatement`**: `Σ_{l∈[1,R]} Σ_{Y∈ancestors} m ≤ ε_CONC(D)·n` under Γ. Literal.
  - `epsCONC` matches the display, and its parse was checked by `rfl`.
- **`EpsCONCTendstoStatement`**: `Tendsto epsCONC atTop (𝓝 0)`. Literal.

### Checked in every Spec

- Every sum over ancestors is indexed by `PartId` addresses, so pre-parts with equal vertex sets are
  counted separately.
- The bound `τ−1` is in `ℕ`, and `τ ≥ 1` for every `d` (`M ≥ 2^{40}` gives `Λ ≥ 40`, so
  `s ≥ 40^{100}` and `τ ≥ 128·1600·s`).
- All logarithms are to base 2, and every exponent `1/2` is `Real.rpow`.
- The Γ-sum statements need no `n ≥ N_0` (TRIAGE §2.6). Their `d_1 ≥ D_*` is implied by `Valid` when
  `R ≥ 1`; when `R = 0` the sums are empty.

## 2. Vacuity

- No Spec has contradictory hypotheses.
- `EGTest/ProbeP3B.lean` re-checked: `scripts/check.sh` gives rc=0, 0 errors and 0 sorry. It witnesses
  the following:
  - the hypotheses of ORIGIN, CONC (i)/(ii) and CONC-L (i)–(iii), plus the per-ancestor bound, on a
    valid one-round run;
  - `Gamma1core ∧ Valid ∧ IsDesignation` together;
  - `Gamma1core D ∧ D ≤ d`;
  - positive right-hand sides of every Γ-sum.
- No conclusion is trivially true, with one exception:
  - "standalone ⇒ no (α)" is definitional, and the TeX sentence is equally definitional.
  - The remaining conclusions are real bounds on `mY`, `α` and edge counts that the definitions do not
    force.
- Residual limit (cosmetic C4): the case `S_Y ≠ ∅` and runs with `R ≥ 1` under Γ are not exhibited.
  - Under Γ this is intrinsic: `d_1 ≥ 2^{2^{256}}`.
  - Without Γ, a run with a guest is small but was not built.

## 3. Declared inputs

Each input is used by the manuscript proof, is stated as in the TeX and hides no probe node. The probe
nodes are those of TRIAGE §4 row P-3: ORIGIN (a),(b), CONC, CONC-L (iv), the sums and the tower facts.

| Input | Used in TeX at | Statement vs TeX |
|---|---|---|
| `TowerAStatement`, lemTower (a) | τ-term `R−r ≤ 2log*d_r+2`; d\*/θ-terms `R−r−1 ≤ 2log*d_r+1`; (eqTowerHalf) `x ≥ d_{r+1}^{1/A}` | All five clauses. The `R−r` clauses are in `ℤ`; the index ranges are exact. Hypotheses: Γ, `Valid`, `d_1 ≥ D` (the lemma header), no `N_0`. propDegRec/lemCap need only Γ2(a) ⇐ Γ; propStructure (iii) is definitional in the model. |
| `TowerCStatement`, lemTower (c), from P3A | `τ_r/P_r ≤ 2^{σ+11}/λ_r` | Unchanged (P3A). |
| `OVK1Statement`, propOV (K1) | #ancestors of round `r` ≤ `1.37n/P_r`; `Σ|Z^0| ≤ 1.37n` (θ-term) | Literal. `ν_l` over `r ∈ [1,R]`, `r+2 ≤ l`. Hypothesis `Gamma2a` (see C1). |
| `OVK3Statement`, propOV (K3) | `Σ_Y |Y^0∩Dup*_r| ≤ 16εn/log P_r` (d\*-term); ORIGIN (c) | Literal. Hypothesis `Gamma2a`. |
| `LacunaryGeomStatement`, lemLacunary (i) | `Σ_r 𝖺(d_r) ≤ 2𝖺(d_R)`, and the same for `𝖻`, `𝖼` | Literal, with `R ≥ 1`. It is true: `X_r ≤ 2^{-(R-r)}X_R`, `Σ 2^{-j} = 2` and `Σ (j+1)2^{-j} = 4`. |

- No input is a node of the probe chain.
- lemGC (ii), thin cut and SEP are proved by P3A and are not inputs.
- lemEL is not needed: ORIGIN (a) gives the `h ∈ Y` case.

## 4. Hygiene

- `python3 -I scripts/lint.py` gives **0 findings**.
- Every Spec file is a module with an `@[expose] public section`.
- Every docstring starts with its manuscript label and quotes the TeX.
- Every stub is tagged `[DECLARED INPUT]` with exactly one `sorry`.
- The new Defs are under `EG/Defs/Probe/P3B/`.

## 5. Refutation target: the CONC-L (iv) per-ancestor bound

I re-derived the bound independently from the locked Defs. Fix a light ancestor `Y = (r,a)`, a round
`l`, a vertex `h` and a designation δ.

- **Where the ports lie.** Take `l ≥ 3`; for `l ≤ 2` the set `Q_Z` is empty. By `IsDesignation`, a port
  `u` counted in `classDeg` has `Y ∈ anc_l(u)`. Therefore:
  - `r+2 ≤ l`;
  - `u ∈ V(Y) = Y^0\S_Y`;
  - `hu ∈ E_l(Z) ⊆ E(G'_l) ⊆ E(G_l) ⊆ E(G_{r+1})`, by the recursion of `graph`.
- **Ports in `Dup*_r`.** They are counted in `d*`, and `u ↦ hu` is injective at a fixed `h`.
- **Ports outside `Dup*_r`, via ORIGIN (a).** The following facts hold in the Lean model:
  - s=0 splits delete nothing: `N'' = Nbr(U)`, so `E(U, V\(U∪N'')) = ∅`.
  - Every edge of a node is in exactly one child or is deleted.
  - `D_r ⊆ Dup*_r`.
  - Consequently every edge `ux` of `G'_r` lies in `X^0_Y` or is deleted on the path to `a`.
  - (R5)(1) assigns every `X^0_Y` edge except the guest–core edges of a light `Y`.
- **Which case applies to `h`.**
  - `h ∉ Y^0`: the edge is (β), and thin cut bounds the count by `τ−1`. Thin cut needs `s_ν < τ`,
    which holds for every `d`, and `Y^0\Dup*_r ⊆ V(leaf)\Dup(τ-run)`.
  - `h ∈ Y`: impossible.
  - `h ∈ S_Y`: the count is at most `α ≤ θ^GC − 1`. When `S_Y ≠ ∅` this is (GC), which is part of
    `isLight`; when `S_Y = ∅`, `α = 0`.
- Standalone `Y` is CONC (ii).
- **The bound holds.** I found no counterexample and no failing step.
- **The summation of (iv).** I re-checked every step and all of them hold:
  - the constants `1.37·16/3 < 8`, `2k+4 ≤ 8k/3` and `2k+3 ≤ 2.5k` for `k ≥ 6`;
  - `1.37 + 1.37λ^{1/2}/P_r ≤ 1.38` and `2.76(2k+3) ≤ 4(2k+2)`;
  - the monotonicity of the three `t`-functions on `t ≥ 4`;
  - `2^{y/(2A)} ≥ 16y²` and `y ≥ 2Av(7+2v)`;
  - both cases of (eqTowerEnd), including `t(2t+6) ≤ 2^t` and `t(2t+5)² ≤ 2^t`.

**T0-CONCL-ALPHA confirmed.** Scratch lemmas, checked by `lake env lean`:
- `EG.HB.thetaGC 1 5 = 0`, because `λ = 0`;
- `EG.HB.thetaGC (1/2) 5 = 0`, because `λ = −1` and `Real.rpow_def_of_neg` gives `cos(−π/2) = 0`.

So `α < θ^GC` fails in Lean for a light `Y` with `S_Y = ∅` whenever `d_r ≤ 1`. Carrying Γ in
`ConcLAlphaStatement` is therefore correct. The per-ancestor bound avoids the problem, since it uses
`θ^GC − 1` and holds without Γ.

## 6. Issues (all cosmetic)

- **C1 (cosmetic). The (K1)/(K3) inputs carry `Gamma2a` only.** The manuscript's standing assumption
  is Γ1–Γ4.
  - This follows TRIAGE §2.6 and blueprint OV-IMPLICIT-DSTAR, which analyses the proof: Γ2(a) is
    needed for Lemma 14^τ(b) through lemCap(ii).
  - But a `sorry`'d input that is stronger than necessary is the risky direction. Every consumer in
    P3B has `Gamma1core`.
  - No change is required. The owner of propOV must prove it with `Gamma2a`, or report and switch to
    `Gamma1core`.
- **C2 (cosmetic). `TowerAStatement` also states clauses that P3B does not use:** `d_{r+2} ≤ λ_r`,
  `λ`-monotonicity and the `−1` form.
  - These clauses are true and literal, and they are included so that the owner can import them.
  - They only enlarge the unproved surface until the owner proves (a).
- **C3 (cosmetic). This file replaces the earlier review of the same name.** `P3B.md` "Fix round 1"
  cites that review's items M1, C1–C4. The orchestrator may keep the old text under another name.
- **C4 (cosmetic, carried over, optional).** No valid run with a guest witnesses the hypotheses of
  `OriginGuestCapStatement`, `ConcLIIStatement` or `ConcLAlpha` with `S_Y ≠ ∅`. The hypotheses are not
  contradictory, as argued in §2.

## 7. Math findings on the manuscript

- None of class T1–T3.
- **T0 (known, confirmed): T0-CONCL-ALPHA**, as in §5.
- **Provenance only:**
  - The proof of CONC-L (i) cites Lemma EL for `h ∈ Y`; ORIGIN (a)'s exclusivity already gives it.
  - The proof of ORIGIN (a) cites lemCap (ii) parenthetically; it is not needed.
  - Neither point affects any statement.
