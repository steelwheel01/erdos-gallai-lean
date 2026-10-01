module

public import EG.Defs.HB.Run
public import EG.Defs.Vortex
public import EG.Defs.Expander
public import EG.Defs.Prob.FinDist

/-!
# Stage-1 lending data: the two-stage colouring COL-JV and the JS labels (manuscript s3:defCOL)

PROTECTED FILE (`EG/Defs/**`): changes need the approval procedure in `APPROVALS/README.md`.

Manuscript v6.1, `s3.tex`, Definition [s3:defCOL] and the event list of Lemma [s3:lemCOL].
Design note: `formal/work/p2d/stage1.md`. Namespace `EG.Stage1`; TRIAGE §2.7 (component (1a),
(1c) of the stage-1 law) and §3 item 15.

Manuscript text ([s3:defCOL], opening): "For every ancestor `Y` of round `r`, with `V(Y)`, `H_Y`,
`ε_Y`, `s_Y` and `L_Y = log|V(Y)|` as in Definition [s2:defAncestors], the random data (i)–(iv)
below are drawn. The data of distinct ancestors are independent. … Formally, every edge `e` of
`H_Y` carries three independent uniform random variables (a fair bit, a lent index and an own
label), and the labels of (iv) are independent of all edge variables."

Data model (TRIAGE §2.7; blueprint s3b node `s3:defCOL`):
* an ancestor is a `PartId = (r, a)` (round, pre-part address), `V(Y) = run.ancVerts G Y`,
  `H_Y = run.ancGraph G Y` (vertex set `V(Y)`, `EG.HB.Run.ancGraph_verts`);
* the colouring of `Y` is a function on the **fixed** edge set `E(H_Y)`: every edge carries a
  triple `(bit, idx, own) : Bool × Option LentTag × Fin (kown G run Y)` (`EdgeLabel`), with law
  `edgeLaw` = Bernoulli(1/2) ⊗ `idxLaw` ⊗ uniform. `bit = false` means `e ∈ Own_Y`, `bit = true`
  means `e ∈ Lend_Y`; `idx` is the lent index (read only on `Lend_Y`), `own` the own label (read
  only on `Own_Y`). Given the bits, the indices of the edges of `Lend_Y` are a uniform
  `k_lend`-colouring of `Lend_Y` and the own labels of the edges of `Own_Y` a uniform
  `k_own`-colouring of `Own_Y` (the "given `Lend_Y`" bullet of the definition; API lemma);
* `idx` is uniform on the tagged union `lentIdx G run Y = I^U ⊔ I^JS ⊔ I^JV` (constructor tags
  `LentTag.U/JS/JV`), and the point mass at `none` if that union is empty (`r ≥ R - 1`, where
  `k_lend = 0` and "`Lend_Y` has no classes"; TRIAGE COL-EMPTY-INDEX);
* `kown G run Y = 4 J_Y + 1` with `J_Y = Vortex.pvJ |V(Y)| = ⌊log₂(L_Y/8)⌋₊` is defined for
  **every** ancestor and is `≥ 1` (`pvJ` is a `Nat.floor`, junk `0` for tiny `Y`), so
  `Fin (kown G run Y)` is never empty (instance `kown.neZero`). For standalone `Y` the own label
  is drawn but never read ("For standalone `Y`, `Own_Y` is not subdivided at stage 1"); it is an
  extra independent coordinate and changes no law the manuscript uses;
* the JS labels of `Y` are a function on the sites `jsSites G run Y = {(l, y) : r+2 ≤ l ≤ R,
  y ∈ V(Y)}` with values `Option ℕ` (`none` = `∗`), law `jsLabelLaw` (weights `M_l^{-4}` on
  `some j`, `j < K^JS_l = M_l^2`, and `1 - M_l^{-2}` on `none`; exact because `M_l ∈ ℕ`);
* the per-ancestor outcome is `COLOut G run Y = Colouring × JSLabels` with law
  `colLaw G run Y = (pi edgeLaw).prod (pi jsLabelLaw)`; the joint law of all ancestors (and of
  zones and pools) is `EG.Stage1.law` (`EG/Defs/Stage1/Law.lean`).

Classes are colour classes of `H_Y` (graphs with vertex set `V(Y)`), written out as
`H_Y.restrictEdges (FinDist.selectSet E(H_Y) (fun e => decide (κ e = i)))`, which is by `rfl`
the `EG.FGraph.colourClass H_Y κ i` of `EG.Lib.Found.ColourClass` (lemmas `Own_eq_colourClass`
etc. in `EG.Lib.Stage1.COL`).

Argument order: every definition of the namespace `EG.Stage1` takes `G run` first (as
`EG.Stage1.Outcome G run` / `EG.Stage1.law G run` of TRIAGE §2.7), then the ancestor `Y`.
Round offsets are written `Y.1 + 2 ≤ l`, never with `ℕ`-subtraction; slots, phases and JS
classes are `0`-based (`σ < T^sl_Y`, `c : Fin 4`, `0 ≤ j < K^JS_l`).

Events of Lemma COL ([s3:lemCOL]): `COLa`, `COLb`, `COLc`, `COLe`, `COLg` (predicates of an
outcome; `COLe` is deterministic). The consumer-exclusivity part of COL(g) is a design rule for
the constructions of s4–s6, not a property of the data (blueprint COL-CONSUMERS-NOT-A-PROPERTY).
-/

@[expose] public section

namespace EG.Stage1

open EG.HB

/-! ### Lent index tags -/

/-- [s3:defCOL] (ii) "Consider the three index families `I^U(Y) := {(l,c,σ) : …}`,
`I^JS(Y) := {(l,j) : …}`, `I^JV(Y) := {l : …}`. These families are regarded as pairwise
disjoint (their indices carry the tags U, JS, JV)": a tagged lent index. `U l c σ` is the
U-index `(l, c, σ)` (phase `c ∈ [4]` as `Fin 4`, slot `σ ∈ [T^sl_Y]` as `0 ≤ σ < T^sl_Y`),
`JS l j` the JS-index `(l, j)`, `JV l` the JV-index `l`. -/
inductive LentTag
  | U (l : ℕ) (c : Fin 4) (σ : ℕ)
  | JS (l j : ℕ)
  | JV (l : ℕ)
  deriving DecidableEq

variable {V : Type*} [DecidableEq V] (G : FGraph V) (run : Run V)

/-- The rounds `l` with `r + 2 ≤ l ≤ R` (the range of `l` in every index family of an ancestor of
round `r` in [s3:defCOL]). Empty iff `r ≥ R - 1`, i.e. `R < r + 2`. -/
def lateRounds (r : ℕ) : Finset ℕ := Finset.Icc (r + 2) run.R

/-! ### Parameters -/

/-- [s3:defCOL] (ii) "`K^JS_l := M_l^2`" (a natural number since `M_l ∈ ℕ`, v6.1 (R2)). -/
noncomputable def KJS (l : ℕ) : ℕ := run.M G l ^ 2

/-- [s3:defCOL] (iv) "`ρ_l := M_l^{-4}`". -/
noncomputable def rhoJS (l : ℕ) : ℝ := (run.M G l : ℝ) ^ (-4 : ℤ)

/-- [s3:defCOL] (Derived quantities) "Also put `t^JS_l := 2M_l + 2`". -/
noncomputable def tJS (l : ℕ) : ℕ := 2 * run.M G l + 2

/-- [s3:defCOL] (ii) "`T^sl_Y := ⌈L_Y^2⌉`" (`L_Y = log₂|V(Y)|`, `EG.HB.Run.LY`). -/
noncomputable def Tslot (Y : PartId) : ℕ := ⌈run.LY G Y ^ 2⌉₊

open Classical in
/-- [s3:defCOL] (ii) "`I^U(Y) := {(l,c,σ) : r+2 ≤ l ≤ R, c ∈ [4], σ ∈ [T^sl_Y]}` if `Y` is
light, … `I^U(Y) := ∅` if `Y` is standalone" (tagged `U`; `c` and `σ` are `0`-based). -/
noncomputable def IU (Y : PartId) : Finset LentTag :=
  if run.isLight G Y.1 Y.2 then
    ((lateRounds run Y.1) ×ˢ (Finset.univ : Finset (Fin 4)) ×ˢ Finset.range (Tslot G run Y)).image
      (fun p => LentTag.U p.1 p.2.1 p.2.2)
  else ∅

/-- [s3:defCOL] (ii) "`I^JS(Y) := {(l,j) : r+2 ≤ l ≤ R, 0 ≤ j < K^JS_l}`" (tagged `JS`). -/
noncomputable def IJS (Y : PartId) : Finset LentTag :=
  (lateRounds run Y.1).biUnion (fun l => (Finset.range (KJS G run l)).image (LentTag.JS l))

/-- [s3:defCOL] (ii) "`I^JV(Y) := {l : r+2 ≤ l ≤ R}`" (tagged `JV`). -/
def IJV (Y : PartId) : Finset LentTag := (lateRounds run Y.1).image LentTag.JV

/-- [s3:defCOL] (ii) the tagged union `I^U(Y) ⊔ I^JS(Y) ⊔ I^JV(Y)` from which "every edge of
`Lend_Y` independently receives an index chosen uniformly" (if `r ≤ R - 2`; it is empty iff
`r ≥ R - 1`: "If `r ≥ R-1`, all three families are empty"). -/
noncomputable def lentIdx (Y : PartId) : Finset LentTag := IU G run Y ∪ IJS G run Y ∪ IJV run Y

/-- [s3:defCOL] (ii) "Put `k_lend(Y) := |I^U(Y)| + |I^JS(Y)| + |I^JV(Y)|`" (equal to
`(lentIdx G run Y).card` since the tagged families are disjoint: `klend_eq_card_lentIdx`). -/
noncomputable def klend (Y : PartId) : ℕ :=
  (IU G run Y).card + (IJS G run Y).card + (IJV run Y).card

/-- [s3:defCOL] (iii) "Put `J_Y := ⌊log(L_Y/8)⌋`": the same term as `J = ⌊log₂(L/8)⌋` of
[s4:lemPV] (`EG.Vortex.pvJ`) at `N = |V(Y)|` (TRIAGE §2.7, PV-OWNCLASS-INDEX). -/
noncomputable def JY (Y : PartId) : ℕ := Vortex.pvJ (run.ancVerts G Y).card

/-- [s3:defCOL] (iii) "and `k_own := 4J_Y + 1`". Defined for every ancestor (for standalone `Y`
the own label is drawn and never read); `≥ 1` always (TRIAGE §2.7). -/
noncomputable def kown (Y : PartId) : ℕ := 4 * JY G run Y + 1

instance kown.neZero (Y : PartId) : NeZero (kown G run Y) := ⟨Nat.succ_ne_zero _⟩

/-- [s3:defCOL] (Derived quantities) "For `k_lend(Y) ≥ 1` put `p_Y := 1/(2k_lend(Y))`" (junk `0`
if `k_lend(Y) = 0`, i.e. `r ≥ R - 1`; every use has `r ≤ R - 2`). -/
noncomputable def pY (Y : PartId) : ℝ := 1 / (2 * (klend G run Y : ℝ))

/-- [s3:defCOL] (Derived quantities) "For a light ancestor `Y` of round `r` put
`t_Y := ⌈λ_r^{1.6}⌉`, the U-multiplicity parameter of `Y`" (`λ_r = run.lam G r`; `Real.rpow`
with the exact rational exponent `1.6`). Defined for every `Y`; used for light `Y` only. -/
noncomputable def tY (Y : PartId) : ℕ := ⌈run.lam G Y.1 ^ (1.6 : ℝ)⌉₊

/-! ### Own-label names -/

/-- The bijection between the named own classes and the own labels, for `J` steps:
`R_{j,c}` (`0 ≤ j < J`, `c ∈ [4]` as `Fin 4`) ↦ label `4j + c`, and `M` (`none`) ↦ label `4J`. -/
def ownIdxOf (J : ℕ) : Option (Fin J × Fin 4) ≃ Fin (4 * J + 1) where
  toFun
    | none => ⟨4 * J, by omega⟩
    | some (j, c) => ⟨4 * j.1 + c.1, by omega⟩
  invFun k :=
    if h : k.1 < 4 * J then some (⟨k.1 / 4, by omega⟩, ⟨k.1 % 4, Nat.mod_lt _ (by omega)⟩)
    else none
  left_inv := by
    rintro (_ | ⟨j, c⟩)
    · simp
    · have hlt : 4 * j.1 + c.1 < 4 * J := by omega
      simp only [hlt, dite_true, Option.some.injEq, Prod.mk.injEq]
      constructor
      · ext; simp only; omega
      · ext; simp only; omega
  right_inv := by
    intro k
    by_cases h : k.1 < 4 * J
    · simp only [h, dite_true]
      ext; simp only; omega
    · simp only [h, dite_false]
      ext; simp only; omega

/-- [s3:defCOL] (iii) "This yields the own classes `R_{j,c}` (`0 ≤ j < J_Y`, `c ∈ [4]`) and `M`
of `Y`": the bijection `Option (Fin (pvJ N) × Fin 4) ≃ Fin (4·pvJ N + 1)` (`none` ↦ `M`) at
`N = |V(Y)|` (TRIAGE §2.7; the PV Spec's index type is the same, since `J_Y = pvJ |V(Y)|`). -/
noncomputable def ownIdx (N : ℕ) : Option (Fin (Vortex.pvJ N) × Fin 4) ≃ Fin (4 * Vortex.pvJ N + 1) :=
  ownIdxOf (Vortex.pvJ N)

/-! ### Outcome types -/

/-- The label triple of one edge of `H_Y`: (fair bit, lent index, own label) ([s3:defCOL]
"every edge `e` of `H_Y` carries three independent uniform random variables (a fair bit, a lent
index and an own label)"). -/
abbrev EdgeLabel (Y : PartId) : Type := Bool × Option LentTag × Fin (kown G run Y)

/-- A stage-1 colouring of `Y` (component (1a) for `Y`): a label triple for every edge of the
fixed edge set `E(H_Y)`. -/
abbrev Colouring (Y : PartId) : Type _ := ↥(run.ancGraph G Y).edges → EdgeLabel G run Y

/-- [s3:defCOL] (iv) "For every `r+2 ≤ l ≤ R` and every `y ∈ V(Y)`, independently, draw a label
`lab_{Y,l}(y)`": the sites `(l, y)` of the JS labels of `Y`. -/
noncomputable def jsSites (Y : PartId) : Finset (ℕ × V) :=
  lateRounds run Y.1 ×ˢ run.ancVerts G Y

/-- The JS labels of `Y` (component (1c) for `Y`): `lab_{Y,l}(y) ∈ {∗} ∪ {0, …, K^JS_l - 1}`
at every site, with `none` for `∗`. -/
abbrev JSLabels (Y : PartId) : Type _ := ↥(jsSites G run Y) → Option ℕ

/-- The stage-1 lending data of the ancestor `Y` ([s3:defCOL] (i)–(iv)): its colouring and its JS
labels. -/
abbrev COLOut (Y : PartId) : Type _ := Colouring G run Y × JSLabels G run Y

/-! ### Laws -/

/-- [s3:defCOL] (i) "Every edge of `H_Y` independently lies in `Own_Y` or in `Lend_Y`, with
probability `1/2` each": the fair bit (`false` = own, `true` = lend). -/
noncomputable def bitLaw : FinDist Bool := FinDist.bernoulli (1 / 2) (by norm_num) (by norm_num)

/-- [s3:defCOL] (ii) "every edge of `Lend_Y` independently receives an index chosen uniformly
from `I^U(Y) ⊔ I^JS(Y) ⊔ I^JV(Y)`": the law of the lent index of one edge, uniform on
`lentIdx G run Y`; the point mass at `none` if `lentIdx G run Y = ∅` ("If `r ≥ R-1`, all three
families are empty, `k_lend(Y) = 0`, and `Lend_Y` has no classes"). -/
noncomputable def idxLaw (Y : PartId) : FinDist (Option LentTag) :=
  if h : (lentIdx G run Y).Nonempty then
    haveI : Nonempty ↥(lentIdx G run Y) := h.to_subtype
    (FinDist.uniform ↥(lentIdx G run Y)).map (fun i => some i.1)
  else FinDist.dirac none

/-- [s3:defCOL] (iii) "Every edge of `Own_Y` independently receives one of `k_own` labels, chosen
uniformly": the law of the own label of one edge. -/
noncomputable def ownLaw (Y : PartId) : FinDist (Fin (kown G run Y)) :=
  FinDist.uniform (Fin (kown G run Y))

/-- [s3:defCOL] "Formally, every edge `e` of `H_Y` carries three independent uniform random
variables (a fair bit, a lent index and an own label)": the law of the triple of one edge. -/
noncomputable def edgeLaw (Y : PartId) : FinDist (EdgeLabel G run Y) :=
  bitLaw.prod ((idxLaw G run Y).prod (ownLaw G run Y))

/-- The weights of the JS label law with `M = M_l`: `some j ↦ M^{-4}` for `j < M^2`,
`none ↦ 1 - M^{-2}`, `0` otherwise ([s3:defCOL] (iv)). -/
noncomputable def jsWeight (M : ℕ) : Option ℕ → ℝ
  | none => 1 - (M : ℝ) ^ (-2 : ℤ)
  | some j => if j < M ^ 2 then (M : ℝ) ^ (-4 : ℤ) else 0

theorem jsWeight_nonneg (M : ℕ) (o : Option ℕ) : 0 ≤ jsWeight M o := by
  cases o with
  | none =>
    simp only [jsWeight, sub_nonneg]
    rcases Nat.eq_zero_or_pos M with h | h
    · subst h; simp
    · have h1 : (1 : ℝ) ≤ M := by exact_mod_cast h
      exact zpow_le_one_of_nonpos₀ h1 (by norm_num)
  | some j =>
    simp only [jsWeight]
    split_ifs
    · positivity
    · exact le_refl 0

/-- The support of the JS label law with `M = M_l`: `∗` and `0, …, M^2 - 1`. -/
def jsSupport (M : ℕ) : Finset (Option ℕ) := insert none ((Finset.range (M ^ 2)).image some)

theorem jsWeight_eq_zero (M : ℕ) (o : Option ℕ) (ho : o ∉ jsSupport M) : jsWeight M o = 0 := by
  cases o with
  | none => simp [jsSupport] at ho
  | some j =>
    simp only [jsSupport, Finset.mem_insert, reduceCtorEq, Finset.mem_image, Finset.mem_range,
      Option.some.injEq, exists_eq_right, false_or] at ho
    simp [jsWeight, ho]

theorem jsWeight_sum (M : ℕ) : ∑ o ∈ jsSupport M, jsWeight M o = 1 := by
  rw [jsSupport, Finset.sum_insert (by simp), Finset.sum_image (by simp)]
  have : ∀ j ∈ Finset.range (M ^ 2), jsWeight M (some j) = (M : ℝ) ^ (-4 : ℤ) := by
    intro j hj
    simp [jsWeight, Finset.mem_range.1 hj]
  rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  simp only [jsWeight]
  rcases Nat.eq_zero_or_pos M with h | h
  · subst h; simp
  · have hM : (M : ℝ) ≠ 0 := by exact_mod_cast h.ne'
    push_cast
    rw [show (-4 : ℤ) = -2 + -2 by norm_num, zpow_add₀ hM,
      show ((M : ℝ) ^ 2) = (M : ℝ) ^ (2 : ℤ) by norm_cast, ← mul_assoc,
      ← zpow_add₀ hM]
    norm_num

/-- [s3:defCOL] (iv) "draw a label `lab_{Y,l}(y) ∈ {∗} ∪ {0,1,…,K^JS_l - 1}` with
`P(lab_{Y,l}(y) = j) = ρ_l := M_l^{-4}` for each `j`, so that `P(lab_{Y,l}(y) = ∗) = 1 - M_l^{-2}`"
(`none` = `∗`; `K^JS_l = M_l^2`, `ρ_l = M_l^{-4}`). Nonnegative weights summing to `1` for every
natural `M_l` ("The label distribution in (iv) is well defined because `K^JS_l ρ_l = M_l^{-2} ≤ 1`"),
so no guard is needed. -/
noncomputable def jsLabelLaw (l : ℕ) : FinDist (Option ℕ) :=
  FinDist.ofFinset (jsSupport (run.M G l)) (jsWeight (run.M G l)) (jsWeight_nonneg _)
    (jsWeight_eq_zero _) (jsWeight_sum _)

/-- Component (1a) for the ancestor `Y`: independent triples on the edges of `H_Y` ([s3:defCOL]
"colours of distinct edges are independent"). -/
noncomputable def colouringLaw (Y : PartId) : FinDist (Colouring G run Y) :=
  FinDist.pi fun _ => edgeLaw G run Y

/-- Component (1c) for the ancestor `Y`: independent JS labels at the sites `(l, y)`, the label
at `(l, y)` with law `jsLabelLaw G run l`. -/
noncomputable def jsLaw (Y : PartId) : FinDist (JSLabels G run Y) :=
  FinDist.pi fun s => jsLabelLaw G run s.1.1

/-- [s3:defCOL] the law of the stage-1 lending data of the ancestor `Y`: the colouring and the JS
labels, independent ("the labels of (iv) are independent of all edge variables"). -/
noncomputable def colLaw (Y : PartId) : FinDist (COLOut G run Y) :=
  (colouringLaw G run Y).prod (jsLaw G run Y)

/-! ### Classes (graphs with vertex set `V(Y)`) -/

variable (Y : PartId)

/-- [s3:defCOL] (i) `Own_Y`: the edges of `H_Y` with bit `false`, as a graph on `V(Y)`
(= `colourClass H_Y (fun e => (c e).1) false`). -/
noncomputable def Own (c : Colouring G run Y) : FGraph V :=
  (run.ancGraph G Y).restrictEdges
    (FinDist.selectSet (run.ancGraph G Y).edges fun e => decide ((c e).1 = false))

/-- [s3:defCOL] (i) `Lend_Y`: the edges of `H_Y` with bit `true`, as a graph on `V(Y)`
(= `colourClass H_Y (fun e => (c e).1) true`). -/
noncomputable def Lend (c : Colouring G run Y) : FGraph V :=
  (run.ancGraph G Y).restrictEdges
    (FinDist.selectSet (run.ancGraph G Y).edges fun e => decide ((c e).1 = true))

/-- [s3:defCOL] (ii) "The edges with index `(l,c,σ) ∈ I^U(Y)` form the U-lent class
`LU_{Y,l,c,σ}`. The edges with index `(l,j) ∈ I^JS(Y)` form the JS-lent class `LJS_{Y,l,j}`. The
edges with index `l ∈ I^JV(Y)` form the JV-lent class `LJV_{Y,l}`. Every class is regarded as a
graph with vertex set `V(Y)`": the lent class of the index `i` (edges of `Lend_Y` with index
`i`; `= colourClass H_Y (fun e => ((c e).1, (c e).2.1)) (true, some i)`). -/
noncomputable def lentClass (c : Colouring G run Y) (i : LentTag) : FGraph V :=
  (run.ancGraph G Y).restrictEdges
    (FinDist.selectSet (run.ancGraph G Y).edges fun e => decide (((c e).1, (c e).2.1) = (true, some i)))

/-- [s3:defCOL] (ii) the U-lent class `LU_{Y,l,c,σ}`. -/
noncomputable def LU (c : Colouring G run Y) (l : ℕ) (ph : Fin 4) (σ : ℕ) : FGraph V :=
  lentClass G run Y c (LentTag.U l ph σ)

/-- [s3:defCOL] (ii) the JS-lent class `LJS_{Y,l,j}`. -/
noncomputable def LJS (c : Colouring G run Y) (l j : ℕ) : FGraph V :=
  lentClass G run Y c (LentTag.JS l j)

/-- [s3:defCOL] (ii) the JV-lent class `LJV_{Y,l}`. -/
noncomputable def LJV (c : Colouring G run Y) (l : ℕ) : FGraph V :=
  lentClass G run Y c (LentTag.JV l)

/-- [s3:defCOL] (iii) the own class of the own label `o` (edges of `Own_Y` with own label `o`,
as a graph on `V(Y)`; `= colourClass H_Y (fun e => ((c e).1, (c e).2.2)) (false, o)`). -/
noncomputable def ownClass (c : Colouring G run Y) (o : Fin (kown G run Y)) : FGraph V :=
  (run.ancGraph G Y).restrictEdges
    (FinDist.selectSet (run.ancGraph G Y).edges fun e => decide (((c e).1, (c e).2.2) = (false, o)))

/-- [s3:defCOL] (iii) the own class `R_{j,c}` (`0 ≤ j < J_Y`, `c ∈ [4]`), via `ownIdx`. -/
noncomputable def ownR (c : Colouring G run Y) (j : Fin (JY G run Y)) (ph : Fin 4) : FGraph V :=
  ownClass G run Y c (ownIdx (run.ancVerts G Y).card (some (j, ph)))

/-- [s3:defCOL] (iii) the own class `M` (the reserve class of the P-vortex), via `ownIdx`. -/
noncomputable def ownM (c : Colouring G run Y) : FGraph V :=
  ownClass G run Y c (ownIdx (run.ancVerts G Y).card none)

/-- [s3:defCOL] (iv) "Put `T_j(Y,l) := {y ∈ V(Y) : lab_{Y,l}(y) = j}`". -/
noncomputable def Tj (lab : JSLabels G run Y) (l j : ℕ) : Finset V :=
  (run.ancVerts G Y).filter (fun y => ∃ h : (l, y) ∈ jsSites G run Y, lab ⟨(l, y), h⟩ = some j)

/-! ### The events of Lemma COL ([s3:lemCOL]) -/

/-- [s3:lemCOL] (a) "`Own_Y` and `Lend_Y` are `(ε_Y, s_Y/4)`-expanders on `V(Y)`. Every lent class,
as a graph on `V(Y)`, is an `(ε_Y, s_Y/(8k_lend(Y)))`-expander. If `Y` is light, every own class
`R_{j,c}`, `M`, as a graph on `V(Y)`, is a `(2^{-6}, s_r/(16k_own))`-expander."
"Every lent class" = the classes of the indices in `lentIdx G run Y` (none if `r ≥ R - 1`); "every
own class" = the classes of all `k_own` own labels (the `R_{j,c}` and `M`, through `ownIdx`).
For light `Y` (`ε_Y = 2^{-6}`, `s_Y = s_r/2`) this is the "COL(a)" of [s5:defStages]. -/
def COLa (ω : COLOut G run Y) : Prop :=
  (Own G run Y ω.1).IsExpander (run.ancEps G Y) (run.ancS G Y / 4) ∧
  (Lend G run Y ω.1).IsExpander (run.ancEps G Y) (run.ancS G Y / 4) ∧
  (∀ i ∈ lentIdx G run Y,
    (lentClass G run Y ω.1 i).IsExpander (run.ancEps G Y) (run.ancS G Y / (8 * klend G run Y))) ∧
  (run.isLight G Y.1 Y.2 → ∀ o : Fin (kown G run Y),
    (ownClass G run Y ω.1 o).IsExpander (2 ^ (-6 : ℤ)) ((run.s G Y.1 : ℝ) / (16 * kown G run Y)))

/-- [s3:lemCOL] (b) "For all `r+2 ≤ l ≤ R` and `0 ≤ j < K^JS_l`, the class `LJS_{Y,l,j}` is
`(2^{12}L_Y^4, t^JS_l)`-path connected through `T_j(Y,l)`." -/
def COLb (ω : COLOut G run Y) : Prop :=
  ∀ l ∈ lateRounds run Y.1, ∀ j < KJS G run l,
    (LJS G run Y ω.1 l j).IsPathConnected (2 ^ 12 * run.LY G Y ^ 4) (tJS G run l)
      (Tj G run Y ω.2 l j)

/-- [s3:lemCOL] (c) "every U-lent class `LU_{Y,l,c,σ}` is `(2^{12}L_Y^4, t_Y)`-path connected
through `V_{l,c,σ}`", for a family of vertex sets `Vs` indexed by the lent tags (only the
U-indices `i ∈ I^U(Y)` are read; `I^U(Y) = ∅` for standalone `Y`). -/
def COLc (ω : COLOut G run Y) (Vs : LentTag → Finset V) : Prop :=
  ∀ i ∈ IU G run Y,
    (lentClass G run Y ω.1 i).IsPathConnected (2 ^ 12 * run.LY G Y ^ 4) (tY G run Y) (Vs i)

open Classical in
/-- [s3:lemCOL] (e) "The own-device thresholds hold. If `Y` is standalone, then
`s_Y/4 ≥ 2^{150}L_Y^{42}` and `s_Y/4 ≥ 2^{146}L_Y^{38} log L_Y`. … If `Y` is light, then
`s_r/2 ≥ 2^{151}L_Y^{38} log L_Y` …. Moreover, on (a) every own class is a `(2^{-6},s')`-expander
with `s' := s_r/(16k_own) ≥ 2^{145}L_Y^{41}` and `2⌈L_Y^6⌉ ≤ s'`."
Only the (deterministic) inequalities; the consequences "on (a)" are `COLa` (blueprint
COL-E-DETERMINISTIC). `log = log₂`. -/
def COLe : Prop :=
  (¬ run.isLight G Y.1 Y.2 →
    (2 : ℝ) ^ 150 * run.LY G Y ^ 42 ≤ run.ancS G Y / 4 ∧
    (2 : ℝ) ^ 146 * run.LY G Y ^ 38 * Real.logb 2 (run.LY G Y) ≤ run.ancS G Y / 4) ∧
  (run.isLight G Y.1 Y.2 →
    (2 : ℝ) ^ 151 * run.LY G Y ^ 38 * Real.logb 2 (run.LY G Y) ≤ (run.s G Y.1 : ℝ) / 2 ∧
    (2 : ℝ) ^ 145 * run.LY G Y ^ 41 ≤ (run.s G Y.1 : ℝ) / (16 * kown G run Y) ∧
    2 * (⌈run.LY G Y ^ 6⌉₊ : ℝ) ≤ (run.s G Y.1 : ℝ) / (16 * kown G run Y))

/-- [s3:lemCOL] (g) "The own classes partition `Own_Y`, and if `r ≤ R-2`, the lent classes are
pairwise edge-disjoint and partition `Lend_Y`. … If `r ≥ R-1`, then `Lend_Y` has no classes"
(the partition facts; `Own_Y`, `Lend_Y` partition `E(H_Y)` by (i)). The consumer-exclusivity
sentence is a design rule of s4–s6, not a property of the data. The lent-class partition holds
on the support of `colLaw` (every edge of `Lend_Y` then has an index in `lentIdx`), so this is an
event, not an identity. -/
def COLg (ω : COLOut G run Y) : Prop :=
  Disjoint (Own G run Y ω.1).edges (Lend G run Y ω.1).edges ∧
  (Own G run Y ω.1).edges ∪ (Lend G run Y ω.1).edges = (run.ancGraph G Y).edges ∧
  (∀ o o' : Fin (kown G run Y), o ≠ o' →
    Disjoint (ownClass G run Y ω.1 o).edges (ownClass G run Y ω.1 o').edges) ∧
  (Finset.univ.biUnion fun o => (ownClass G run Y ω.1 o).edges) = (Own G run Y ω.1).edges ∧
  (Y.1 + 2 ≤ run.R →
    (∀ i ∈ lentIdx G run Y, ∀ i' ∈ lentIdx G run Y, i ≠ i' →
      Disjoint (lentClass G run Y ω.1 i).edges (lentClass G run Y ω.1 i').edges) ∧
    ((lentIdx G run Y).biUnion fun i => (lentClass G run Y ω.1 i).edges) =
      (Lend G run Y ω.1).edges) ∧
  (run.R < Y.1 + 2 → lentIdx G run Y = ∅)

end EG.Stage1
