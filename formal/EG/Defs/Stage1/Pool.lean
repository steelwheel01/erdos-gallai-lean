module

public import EG.Defs.HB.Run
public import EG.Defs.Prob.FinDist

/-!
# Stage 1d: round-split pool labels (manuscript s7:defPool)

PROTECTED FILE (`EG/Defs/**`): changes need the approval procedure in `APPROVALS/README.md`.

Manuscript v6.1, `s7.tex`, Definition [s7:defPool]. Design note: `formal/work/p2d/stage1.md`.
Namespace `EG.Stage1`; TRIAGE §2.7 (component (1d)), §3 item 17.

Manuscript text ([s7:defPool]): "Every vertex `v` of `G` independently draws a pool label
`plab(v) ∈ {⊥} ∪ {(l,r) : 3 ≤ l ≤ R, 1 ≤ r ≤ l-2}`, `P(plab(v) = (l,r)) = q_l π_{l,r}`, where
`q_l := M_l^{-2}` and `π_{l,r} := 2^{-(l-1-r)}`, and `P(plab(v) = ⊥) := 1 - Σ_{l,r} q_l π_{l,r}`.
This is a probability distribution: … `Σ_l q_l ≤ Σ_l M_l^{-1} ≤ 2/D_* < 1` by Lemma [s2:lemTower]
(b). Put `Pool_{l,r} := plab^{-1}(l,r)`, `Pool_l := ⋃_{r=1}^{l-2} Pool_{l,r}` (a disjoint union) …
For `w ∈ Pool_l` let `r(w)` denote the unique `r` with `w ∈ Pool_{l,r}`. The pool labels are
stage (1d) of the randomness schedule. They are independent of all other stage-1 data".

Data model (TRIAGE §2.7 "1d pool"; blueprint s7a POOL-LAW-NEEDS-GAMMA, POOL-ROUND-OFFSET):
* a label is `Option (ℕ × ℕ)` (`none` = `⊥`); the index set is
  `poolIdx run = {(l, r) : 3 ≤ l ≤ R, 1 ≤ r, r + 2 ≤ l}` (no `ℕ`-subtraction);
* `π_{l,r} = 2^{-(l-1-r)}` is an integer power (`zpow`) with the exponent `-((l:ℤ) - 1 - r)`;
* the law is a probability distribution only if `poolMass ≤ 1` (a theorem under Γ); the
  definition is total by a `dite` whose guard is exactly `poolMass G run ≤ 1`, with fallback
  `dirac none` (TRIAGE §2.7, §2.12);
* the labels are indexed by `↥G.verts` (TRIAGE §2.5); `plabOf G π v` reads the label of any
  `v : V` (`none` off `V(G)`).
Name clash note: the weight `ω_l(v)` of s7 is `poolWeight` in `EG.Quot` (TRIAGE §2.10); the
label weights here are `plabWeight`.
-/

@[expose] public section

namespace EG.Stage1

open EG.HB

variable {V : Type*} [DecidableEq V] (G : FGraph V) (run : Run V)

/-- [s7:defPool] the non-`⊥` pool labels "`(l,r)` with `3 ≤ l ≤ R`, `1 ≤ r ≤ l-2`" (written
`r + 2 ≤ l`). -/
def poolIdx : Finset (ℕ × ℕ) :=
  ((Finset.Icc 3 run.R) ×ˢ (Finset.Icc 1 run.R)).filter (fun p => p.2 + 2 ≤ p.1)

/-- [s7:defPool] "`q_l := M_l^{-2}`". -/
noncomputable def qPool (l : ℕ) : ℝ := (run.M G l : ℝ) ^ (-2 : ℤ)

/-- [s7:defPool] "`π_{l,r} := 2^{-(l-1-r)}`". -/
noncomputable def piPool (l r : ℕ) : ℝ := (2 : ℝ) ^ (-((l : ℤ) - 1 - (r : ℤ)))

/-- [s7:defPool] "`Σ_{l,r} q_l π_{l,r}`", the total probability of a non-`⊥` label. -/
noncomputable def poolMass : ℝ := ∑ p ∈ poolIdx run, qPool G run p.1 * piPool p.1 p.2

open Classical in
/-- The weights of the pool label law: `some (l, r) ↦ q_l π_{l,r}` on `poolIdx`,
`none ↦ 1 - Σ_{l,r} q_l π_{l,r}`, `0` otherwise ([s7:defPool]). -/
noncomputable def plabWeight : Option (ℕ × ℕ) → ℝ
  | none => 1 - poolMass G run
  | some p => if p ∈ poolIdx run then qPool G run p.1 * piPool p.1 p.2 else 0

/-- The support of the pool label law: `⊥` and `poolIdx`. -/
def plabSupport : Finset (Option (ℕ × ℕ)) := insert none ((poolIdx run).image some)

theorem qPool_nonneg (l : ℕ) : 0 ≤ qPool G run l := by
  unfold qPool
  rw [show (-2 : ℤ) = -((2 : ℕ) : ℤ) by norm_num, zpow_neg, zpow_natCast]
  positivity

theorem piPool_pos (l r : ℕ) : 0 < piPool l r := zpow_pos (by norm_num) _

theorem plabWeight_nonneg (h : poolMass G run ≤ 1) (o : Option (ℕ × ℕ)) :
    0 ≤ plabWeight G run o := by
  rcases o with _ | p
  · simp only [plabWeight]; linarith
  · simp only [plabWeight]
    split_ifs
    · exact mul_nonneg (qPool_nonneg G run _) (piPool_pos _ _).le
    · exact le_refl 0

theorem plabWeight_eq_zero (o : Option (ℕ × ℕ)) (ho : o ∉ plabSupport run) :
    plabWeight G run o = 0 := by
  rcases o with _ | p
  · simp [plabSupport] at ho
  · simp only [plabSupport, Finset.mem_insert, reduceCtorEq, Finset.mem_image,
      Option.some.injEq, exists_eq_right, false_or] at ho
    simp [plabWeight, ho]

theorem plabWeight_sum : ∑ o ∈ plabSupport run, plabWeight G run o = 1 := by
  classical
  rw [plabSupport, Finset.sum_insert (by simp), Finset.sum_image (by simp)]
  have : ∀ p ∈ poolIdx run, plabWeight G run (some p) = qPool G run p.1 * piPool p.1 p.2 := by
    intro p hp
    simp [plabWeight, hp]
  rw [Finset.sum_congr rfl this]
  simp only [plabWeight, poolMass]
  ring

/-- [s7:defPool] the law of the pool label of one vertex. Total by a `dite` whose guard is exactly
`Σ_{l,r} q_l π_{l,r} ≤ 1` (true for valid runs under Γ, [s7:defPool] "This is a probability
distribution"); fallback `dirac none` (TRIAGE §2.7). -/
noncomputable def poolLabelLaw : FinDist (Option (ℕ × ℕ)) :=
  if h : poolMass G run ≤ 1 then
    FinDist.ofFinset (plabSupport run) (plabWeight G run) (plabWeight_nonneg G run h)
      (plabWeight_eq_zero G run) (plabWeight_sum G run)
  else FinDist.dirac none

/-- [s7:defPool] component (1d) of stage 1: "Every vertex `v` of `G` independently draws a pool
label": the product over `V(G)` of `poolLabelLaw`. -/
noncomputable def poolLaw : FinDist (↥G.verts → Option (ℕ × ℕ)) :=
  FinDist.pi fun _ => poolLabelLaw G run

variable {G} in
/-- The pool label `plab(v)` of `v : V` in the outcome `π` of (1d) (`none` = `⊥` if `v ∉ V(G)`). -/
def plabOf (π : ↥G.verts → Option (ℕ × ℕ)) (v : V) : Option (ℕ × ℕ) :=
  if h : v ∈ G.verts then π ⟨v, h⟩ else none

/-- [s7:defPool] "`Pool_{l,r} := plab^{-1}(l,r)`". -/
def poolSet (π : ↥G.verts → Option (ℕ × ℕ)) (l r : ℕ) : Finset V :=
  G.verts.filter (fun v => plabOf π v = some (l, r))

/-- [s7:defPool] "`Pool_l := ⋃_{r=1}^{l-2} Pool_{l,r}` (a disjoint union)" (`1 ≤ r`, `r + 2 ≤ l`). -/
def poolL (π : ↥G.verts → Option (ℕ × ℕ)) (l : ℕ) : Finset V :=
  ((Finset.Icc 1 l).filter (fun r => r + 2 ≤ l)).biUnion (poolSet G π l)

variable {G} in
/-- [s7:defPool] "For `w ∈ Pool_l` let `r(w)` denote the unique `r` with `w ∈ Pool_{l,r}`": the
second coordinate of the pool label of `w` (junk `0` if `plab(w) = ⊥`; read only on `Pool_l`). -/
def poolRound (π : ↥G.verts → Option (ℕ × ℕ)) (w : V) : ℕ :=
  match plabOf π w with
  | some (_, r) => r
  | none => 0

end EG.Stage1
