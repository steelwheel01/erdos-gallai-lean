import EG.Lib.Found.Fnum
import EG.Lib.Found.NbrSetDeg
import EG.Lib.Found.Log
import EG.Lib.Found.Constants
import EG.Lib.Found.Gamma
import EG.Lib.Found.PathDecomp
import EG.Lib.Found.Components

/-! Unit tests for the P2-D small foundations (TRIAGE §3 items 1–6): `Obj.isEdge`,
`FGraph.nbrSetDeg`, `FGraph.IsWellExpanding`, `logIter`/`tower`/`logStar`, the absolute
constants, `Gamma1core`/`Gamma2a`, `IsPathDecomp`/`pathEndCount`/`IsPathCycleDecomp`, and the
edge-set components (`edgeVerts`, `edgeComps`, `compEdges`, `IsNonBridge`, `IsPendant`). -/

namespace EGTest.Defs2

open EG FGraph Real

/-! ## `Obj.isEdge` (Defs/Objects) -/

example : (Obj.edge s((0 : ℕ), 1)).isEdge = true := rfl
example : (Obj.cycle [(0 : ℕ), 1, 2]).isEdge = false := rfl
example : [Obj.edge s((0 : ℕ), 1), .cycle [0, 1, 2], .edge s(2, 3)].countP Obj.isEdge = 2 := rfl

/-! ## `N_{H,d}(U)` and well-expanding sets

`K` is the graph on `{0,1,2,3}` with edges `01, 02, 12, 13`: vertex `2` has two neighbours in
`U = {0,1}`, vertex `3` has one. -/

def K : FGraph ℕ := ofEdges {0, 1, 2, 3} {s(0, 1), s(0, 2), s(1, 2), s(1, 3)}

example : K.nbrSet {0, 1} = {2, 3} := by decide
example : K.nbrSetDeg {0, 1} (1 : ℕ) = {2, 3} := by rw [nbrSetDeg_natCast]; decide
example : K.nbrSetDeg {0, 1} (2 : ℕ) = {2} := by rw [nbrSetDeg_natCast]; decide
example : K.nbrSetDeg {0, 1} (3 : ℕ) = ∅ := by rw [nbrSetDeg_natCast]; decide
-- a real threshold: `d = 1.5` behaves as `⌈1.5⌉ = 2`
example : K.nbrSetDeg {0, 1} 1.5 = K.nbrSetDeg {0, 1} (2 : ℕ) := by
  ext v
  rw [mem_nbrSetDeg, mem_nbrSetDeg]
  have key : ∀ n : ℕ, ((1.5 : ℝ) ≤ n ↔ ((2 : ℕ) : ℝ) ≤ n) := by
    intro n
    constructor
    · intro h
      have : (1 : ℝ) < n := by linarith
      have : 1 < n := by exact_mod_cast this
      exact_mod_cast this
    · intro h; push_cast at h; linarith
  rw [key]
-- `U` itself is excluded, even when its vertices have neighbours in `U`
example : 0 ∉ K.nbrSetDeg {0, 1} (1 : ℕ) := by rw [nbrSetDeg_natCast]; decide

example : K.IsWellExpanding 1 {0, 1} := by
  rw [isWellExpanding_iff, show K.nbrSet {0, 1} = {2, 3} by decide]; norm_num
example : ¬ K.IsWellExpanding 2 {0, 1} := by
  rw [isWellExpanding_iff, show K.nbrSet {0, 1} = {2, 3} by decide]; norm_num
example : K.IsWellExpanding 100 ∅ := isWellExpanding_empty _ _

/-! ## Iterated logarithms, tower, `log*` -/

example : tower 1 = 2 := by rw [tower_succ, tower_zero]; norm_num
example : tower 2 = 4 := by
  rw [tower_succ, tower_succ, tower_zero]; norm_num
example : tower 3 = 16 := by
  rw [tower_succ, tower_succ, tower_succ, tower_zero]; norm_num
example : logIter 2 16 = 2 := by
  rw [logIter_succ', logIter_one]
  have h16 : (16 : ℝ) = 2 ^ (4 : ℕ) := by norm_num
  have h4 : (4 : ℝ) = 2 ^ (2 : ℕ) := by norm_num
  rw [h16, Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
  norm_num
  rw [h4, Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
  norm_num
example : logStar 1 = 0 := by simp
example : logStar (1 / 2) = 0 := by rw [logStar_eq_zero_iff]; norm_num
example : logStar (-5) = 0 := by rw [logStar_eq_zero_iff]; norm_num
example : logStar 2 = 1 := by
  have : (2 : ℝ) = tower 1 := by rw [tower_succ, tower_zero]; norm_num
  rw [this, logStar_tower]
example : logStar 16 = 3 := by
  have : (16 : ℝ) = tower 3 := by
    rw [tower_succ, tower_succ, tower_succ, tower_zero]; norm_num
  rw [this, logStar_tower]
-- just above a tower value, `log*` jumps
example : logStar 17 = 4 := by
  apply le_antisymm
  · rw [logStar_le_iff_le_tower]
    rw [tower_succ, tower_succ, tower_succ, tower_succ, tower_zero]; norm_num
  · rw [Nat.succ_le_iff, lt_logStar_iff_tower_lt]
    rw [tower_succ, tower_succ, tower_succ, tower_zero]; norm_num
example : logStar ((2 : ℝ) ^ (16 : ℝ)) = 4 := by
  rw [logStar_two_rpow (by norm_num)]
  have : (16 : ℝ) = tower 3 := by
    rw [tower_succ, tower_succ, tower_succ, tower_zero]; norm_num
  rw [this, logStar_tower]

/-- Growth of `log*` (review round 1). -/
example : (logStar 16 : ℝ) ≤ 2 + logb 2 (logb 2 16) := logStar_le_two_add_loglog (by norm_num)
example : (fun y : ℝ => (logStar y : ℝ)) =o[Filter.atTop] (fun y => logb 2 (logb 2 y)) :=
  logStar_isLittleO_loglog
/-- s6.tex:262 "`log* x ≤ 1 + log x` for all `x ≥ 1`" (review round 2), incl. the endpoint. -/
example : (logStar 1 : ℝ) ≤ 1 + logb 2 1 := logStar_le_one_add_logb le_rfl
example : (logStar 3 : ℝ) ≤ 1 + logb 2 3 := logStar_le_one_add_logb (by norm_num)

/-! ## Constants -/

example : epsC = 1 / 32 := epsC_eq
example : sigmaC = 100 ∧ Cp = 103 ∧ Aexp = 105 := ⟨rfl, rfl, rfl⟩
example : (2 : ℕ) ^ (sigmaC + 15) = 2 ^ 115 := rfl

/-! ## Γ1 (a)–(e) and Γ2 (a) -/

example : Gamma1a 256 := by unfold Gamma1a; norm_num
example : ¬ Gamma1a 255 := by unfold Gamma1a; norm_num
example : Gamma1d 256 := by
  unfold Gamma1d
  have h : (256 : ℝ) = 2 ^ (8 : ℕ) := by norm_num
  rw [h, Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
  norm_num
example : ¬ Gamma1Items 0 := fun h => by have := h.a; unfold Gamma1a at this; norm_num at this
-- the encodings: `1.6 = 8/5` exactly; natural-number exponents `3`, `46·A = 4830`, `36`
example : (1.6 : ℝ) = 8 / 5 := by norm_num
example (μ : ℝ) : Gamma1c μ ↔ 2 * 105 * logb 2 (105 * μ) ≤ 8 / 5 * μ := by
  unfold Gamma1c; norm_num
example (μ : ℝ) : Gamma1b μ ↔ (2 : ℝ) ^ (14 : ℕ) * 105 * μ ^ (3 : ℕ) ≤ (2 : ℝ) ^ μ := by
  unfold Gamma1b; norm_num
example (μ : ℝ) :
    Gamma1e μ ↔ (2 : ℝ) ^ (240 : ℕ) * (105 * μ) ^ (4830 : ℕ) ≤ ((2 : ℝ) ^ μ) ^ (36 : ℕ) := by
  unfold Gamma1e; rw [cast_Aexp, Aexp_eq]
example : Gamma2a (2 ^ 117) := le_rfl
example : ¬ Gamma2a 1 := by unfold Gamma2a; norm_num

/-- `D = 3` is not galactic: `log₂log₂3 < 1 < 2^8`, so item (a) fails on the ray. -/
example : ¬ Gamma1core 3 := by
  intro h
  have h8 := h.two_pow_eight_le_loglog
  have h1 : logb 2 3 < 2 := by
    rw [Real.logb_lt_iff_lt_rpow (by norm_num) (by norm_num)]; norm_num
  have h2 : logb 2 (logb 2 3) < 1 := by
    have hpos : 0 < logb 2 3 := Real.logb_pos (by norm_num) (by norm_num)
    rw [Real.logb_lt_iff_lt_rpow (by norm_num) hpos]; norm_num; exact h1
  linarith

/-- Positive check (review round 1): all five items hold at `μ = 2^{20}`, and on the whole ray
above it, so `Gamma1core` is satisfiable. -/
example : Gamma1Items (2 ^ 20) := gamma1Items_of_le le_rfl
example : Gamma1Items (2 ^ 20) ∧ Gamma1a (2 ^ 20) ∧ Gamma1e (2 ^ 20) :=
  ⟨gamma1Items_of_le le_rfl, (gamma1Items_of_le le_rfl).a, (gamma1Items_of_le le_rfl).e⟩
example : ∃ D : ℝ, Gamma1core D ∧ Gamma2a D :=
  ⟨_, gamma1core_two_rpow_two_rpow, gamma1core_two_rpow_two_rpow.gamma2a⟩
example : ∀ᶠ D in Filter.atTop, Gamma1core D := eventually_gamma1core

/-- Negative checks on the ray of (a) (review round 2): items (c) and (e) fail at `μ = 2^8`,
where (a) and (d) hold, so neither is implied by (a); the encoding has a genuine threshold
between `2^8` and `2^20`. (c): `log₂(105·256) ≥ 14` and `210·14 > 409.6`. -/
example : ¬ Gamma1c 256 := by
  unfold Gamma1c
  rw [cast_Aexp]
  intro h
  have h14 : (14 : ℝ) ≤ logb 2 ((105 : ℝ) * 256) := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by norm_num)]
    have : (2 : ℝ) ^ (14 : ℝ) = (2 : ℝ) ^ (14 : ℕ) := by rw [← Real.rpow_natCast]; norm_num
    rw [this]; norm_num
  norm_num at h h14
  linarith

/-- (e) at `μ = 2^8`: `36·256 = 9216 < 240 + 4830·14`. -/
example : ¬ Gamma1e 256 := by
  unfold Gamma1e
  rw [cast_Aexp, Aexp_eq]
  intro h
  have h1 : (2 : ℝ) ^ (240 : ℕ) * (2 ^ (14 : ℕ)) ^ (46 * 105) ≤
      (2 : ℝ) ^ 240 * ((105 : ℝ) * 256) ^ (46 * 105) := by
    gcongr; norm_num
  have h2 : ((2 : ℝ) ^ (256 : ℝ)) ^ 36 = (2 : ℝ) ^ (256 * 36 : ℕ) := by
    rw [show (256 : ℝ) = ((256 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, ← pow_mul]
  push_cast at h
  rw [h2] at h
  have := h1.trans h
  rw [← pow_mul, ← pow_add] at this
  have := (pow_le_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).1 this
  norm_num at this

/-- The s2:lemLacunary(iv) transfer (review round 2). -/
example (D x : ℝ) (h : Gamma1core D) (hx : logb 2 D ≤ x) : Gamma1Items (logb 2 x) :=
  h.items_logb_of_le hx

/-- Γ1 is upward closed and implies Γ2(a). -/
example (D D' : ℝ) (h : Gamma1core D) (hD : D ≤ D') : Gamma1core D' ∧ Gamma2a D' :=
  ⟨h.mono hD, (h.mono hD).gamma2a⟩

/-! ## Path decompositions -/

/-- The path `0 - 1 - 2` as one path. -/
example : IsPathDecomp ({s(0, 1), s(1, 2)} : Set (Sym2 ℕ)) [[0, 1, 2]] := by
  refine ⟨by decide, by decide, fun e => ?_⟩
  simp [walkEdges]

/-- … or as two paths. -/
example : IsPathDecomp ({s(0, 1), s(1, 2)} : Set (Sym2 ℕ)) [[0, 1], [2, 1]] := by
  refine ⟨by decide, by decide, fun e => ?_⟩
  simp only [walkEdges, List.tail_cons, List.flatMap_cons, List.flatMap_nil, List.zipWith_cons_cons,
    List.zipWith_nil_right, List.append_nil, List.singleton_append, List.mem_cons,
    List.not_mem_nil, or_false, Set.mem_insert_iff, Set.mem_singleton_iff]
  rw [Sym2.eq_swap (a := 2)]

example : pathEndCount [[(0 : ℕ), 1], [2, 1]] 1 = 2 := by decide
example : pathEndCount [[(0 : ℕ), 1, 2]] 1 = 0 := by decide
example : pathEndCount [[(0 : ℕ), 1, 2]] 2 = 1 := by decide

/-- A trivial one-vertex path is not allowed. -/
example : ¬ IsPathDecomp (∅ : Set (Sym2 ℕ)) [[0]] := fun h => by
  have := h.two_le_length (List.mem_singleton_self _); simp at this

/-- An edge used twice is not allowed. -/
example : ¬ IsPathDecomp ({s(0, 1)} : Set (Sym2 ℕ)) [[0, 1], [1, 0]] := fun h => by
  have := h.2.1; simp [walkEdges] at this

/-- A walk with a repeated vertex is not a path. -/
example : ¬ IsPathDecomp ({s(0, 1)} : Set (Sym2 ℕ)) [[0, 1, 0]] := fun h => by
  have := h.nodup (List.mem_singleton_self _); simp at this

/-- A loop has no path decomposition. -/
example (P : List (List ℕ)) : ¬ IsPathDecomp ({s(0, 0)} : Set (Sym2 ℕ)) P := fun h =>
  h.not_isDiag (Set.mem_singleton _) (Sym2.mk_isDiag_iff.2 rfl)

/-- The triangle as one cycle and no path (Lovász form). -/
example : IsPathCycleDecomp ({s(0, 1), s(1, 2), s(2, 0)} : Set (Sym2 ℕ)) [] [[0, 1, 2]] := by
  refine ⟨by simp, ?_, by decide, fun e => ?_⟩
  · intro c hc
    rw [List.mem_singleton] at hc
    subst hc
    exact ⟨by decide, by decide⟩
  · simp [cycleEdges]

/-! ## Components, bridges, pendant edges

`E = {01, 12, 20, 23, 45}`: a triangle with a pendant edge `23`, and a separate edge `45`. -/

def E : Finset (Sym2 ℕ) := {s(0, 1), s(1, 2), s(2, 0), s(2, 3), s(4, 5)}

example : edgeVerts E = {0, 1, 2, 3, 4, 5} := by decide

example : (edgeGraph E).Adj 0 1 ∧ ¬ (edgeGraph E).Adj 0 3 := by simp [E]

example : (edgeGraph E).connectedComponentMk 0 = (edgeGraph E).connectedComponentMk 3 := by
  rw [SimpleGraph.ConnectedComponent.eq]
  exact (SimpleGraph.Adj.reachable (by simp [E] : (edgeGraph E).Adj 0 2)).trans
    (SimpleGraph.Adj.reachable (by simp [E] : (edgeGraph E).Adj 2 3))

example : (edgeGraph E).connectedComponentMk 4 ∈ edgeComps E :=
  mem_edgeComps.2 ⟨4, by decide, rfl⟩

example : s(2, 3) ∈ compEdges E ((edgeGraph E).connectedComponentMk 0) := by
  have h := mem_compEdges_of_mem (E := E) (u := 2) (v := 3) (by decide) (by decide)
  have h02 : (edgeGraph E).connectedComponentMk 2 = (edgeGraph E).connectedComponentMk 0 :=
    SimpleGraph.ConnectedComponent.eq.2
      (SimpleGraph.Adj.reachable (by simp [E] : (edgeGraph E).Adj 2 0))
  rwa [h02] at h

/-- `23` is pendant (vertex `3` has degree 1); `01` is not (degrees 2 and 2). -/
example : IsPendant E s(2, 3) := ⟨by decide, 3, Sym2.mem_mk_right _ _, by decide⟩
example : ¬ IsPendant E s(0, 1) := by
  rintro ⟨-, v, hv, hdeg⟩
  rcases Sym2.mem_iff.1 hv with rfl | rfl <;> revert hdeg <;> decide

/-- `01` is a non-bridge: `0 - 2 - 1` avoids it. -/
example : IsNonBridge E s(0, 1) := by
  rw [isNonBridge_mk_iff]
  refine ⟨by decide, ?_⟩
  have h02 : ((edgeGraph E).deleteEdges {s(0, 1)}).Adj 0 2 := by simp [E]
  have h21 : ((edgeGraph E).deleteEdges {s(0, 1)}).Adj 2 1 := by simp [E]
  exact h02.reachable.trans h21.reachable

/-- `23` is a bridge: after deleting it, `3` is isolated. -/
example : ¬ IsNonBridge E s(2, 3) := by
  rw [isNonBridge_mk_iff]
  rintro ⟨-, hr⟩
  rw [SimpleGraph.reachable_comm, SimpleGraph.reachable_iff_reflTransGen] at hr
  rcases Relation.ReflTransGen.cases_head hr with h | ⟨c, hc, -⟩
  · exact absurd h (by decide)
  · simp [E] at hc
    omega

/-! ### Component maps and component-local characterisations (review round 1) -/

def E' : Finset (Sym2 ℕ) := insert s(3, 4) E

theorem hEE' : E ⊆ E' := Finset.subset_insert _ _

/-- The component `{4,5}` of `E` (one edge) sits inside the component of `E'` containing it. -/
example : (compEdges E ((edgeGraph E).connectedComponentMk 4)).card ≤
    (compEdges E' ((edgeGraph E').connectedComponentMk 4)).card :=
  card_compEdges_le_compMap hEE' _

example : compMap hEE' ((edgeGraph E).connectedComponentMk 4) ∈ edgeComps E' :=
  compMap_mem_edgeComps hEE' (mem_edgeComps.2 ⟨4, by decide, rfl⟩)

/-- `01` is a non-bridge of its own component, and `23` is pendant in it. -/
example : IsNonBridge (compEdges E ((edgeGraph E).connectedComponentMk 0)) s(0, 1) := by
  have h01 : s(0, 1) ∈ compEdges E ((edgeGraph E).connectedComponentMk 0) :=
    mem_compEdges_of_mem (by decide) (by decide)
  rw [isNonBridge_compEdges_iff h01, isNonBridge_mk_iff]
  refine ⟨by decide, ?_⟩
  have h02 : ((edgeGraph E).deleteEdges {s(0, 1)}).Adj 0 2 := by simp [E]
  have h21 : ((edgeGraph E).deleteEdges {s(0, 1)}).Adj 2 1 := by simp [E]
  exact h02.reachable.trans h21.reachable

example : degE (compEdges E ((edgeGraph E).connectedComponentMk 3)) 3 = 1 := by
  rw [degE_compEdges rfl]; decide

end EGTest.Defs2
