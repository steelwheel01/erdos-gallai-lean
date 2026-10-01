module

public import EG.Lib.Chain.HccpAux
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-!
# HCC-P, Steps 2 and 3: balance and the potential `Ψ` (manuscript s6:lemHCCP)

Probe unit P2E (probe P-2, part 1), proof round 1.
* Step 2 (balance), in integer form: `∑_i exc_{O_i}(v) = exc(v)` (`sum_exc_O`; hubs are balanced,
  and a vertex outside `V(𝒦_i)` meets no arc of `O_i`), and the port indicator
  `∑_j [v ∈ LayP_j]` is `0` or `1` (`Valid.sum_layP_ind_le_one`);
* Step 3: the block index `blk` (`j` on layer `j` and on `T_j`) and the potential
  `Ψ(v) = 3j + pot_𝒦(v)` on a cluster of layer `j`, `Ψ(y) = 3j + 1 + tp_j(y)/(|T_j|+1)` on `T_j`,
  well defined by (D) (`Valid.blk_of_mem_verts`, `Valid.psi_of_mem_verts`, `Valid.blk_of_mem_T`,
  `Valid.psi_of_mem_T`); `pot_𝒦(v) = pc(v)/(|V(𝒦)|+1)` for a topological numbering `pc` of the
  admissible orientation, as in the manuscript ("take the position in a topological order divided
  by `|V(𝒦)|+1`");
* the arcs of `D_j` go from block `j` to block `j` or `j + 1 (mod k)` (`Valid.blk_pathArcs`).
-/

public section

namespace EG.Chain

namespace HccpData

variable {V : Type*} [DecidableEq V] (S : HccpData V)

open Classical in
/-- [s6:lemHCCP] (proof, Step 4) The block index: `j` for a vertex of a cluster of layer `j` or of
`T_j` (well defined by (D)); `0` elsewhere. -/
noncomputable def blk (v : V) : ℕ :=
  if h : ∃ i, v ∈ (S.K i).verts then (S.lay h.choose).val
  else if h' : ∃ j, v ∈ S.T j then h'.choose.val else 0

open Classical in
/-- [s6:lemHCCP] (proof, Step 3) "`Ψ(v) := 3j + pot_𝒦(v)` (`v ∈ V(𝒦)`, `𝒦 ∈ 𝒦_j`),
`Ψ(y) := 3j + 1 + tp_j(y)/(|T_j| + 1)` (`y ∈ T_j`)", with `pot_𝒦 = pc_𝒦/(|V(𝒦)|+1)`. -/
noncomputable def psi (pc : Fin S.N → V → ℕ) (tp : Fin S.k → V → ℕ) (v : V) : ℝ :=
  if h : ∃ i, v ∈ (S.K i).verts then
    3 * ((S.lay h.choose).val : ℝ) + (pc h.choose v : ℝ) / ((S.K h.choose).verts.card + 1)
  else if h' : ∃ j, v ∈ S.T j then
    3 * (h'.choose.val : ℝ) + 1 + (tp h'.choose v : ℝ) / ((S.T h'.choose).card + 1)
  else 0

variable {G : FGraph V} {S}

theorem Valid.choose_verts (hS : S.Valid G) {i : Fin S.N} {v : V} (hv : v ∈ (S.K i).verts)
    (h : ∃ i, v ∈ (S.K i).verts) : h.choose = i := by
  by_contra hne
  exact Finset.disjoint_left.1 (hS.D_KK _ _ hne) h.choose_spec hv

theorem Valid.not_exists_verts_of_mem_T (hS : S.Valid G) {j : Fin S.k} {v : V}
    (hv : v ∈ S.T j) : ¬ ∃ i, v ∈ (S.K i).verts := by
  rintro ⟨i, hi⟩
  exact Finset.disjoint_left.1 (hS.D_KT i j) hi hv

theorem Valid.choose_T (hS : S.Valid G) {j : Fin S.k} {v : V} (hv : v ∈ S.T j)
    (h : ∃ j, v ∈ S.T j) : h.choose = j := by
  by_contra hne
  exact Finset.disjoint_left.1 (hS.T_disj _ _ hne) h.choose_spec hv

theorem Valid.blk_of_mem_verts (hS : S.Valid G) {i : Fin S.N} {v : V}
    (hv : v ∈ (S.K i).verts) : S.blk v = (S.lay i).val := by
  have h : ∃ i, v ∈ (S.K i).verts := ⟨i, hv⟩
  unfold blk
  rw [dif_pos h, hS.choose_verts hv h]

theorem Valid.psi_of_mem_verts (hS : S.Valid G) (pc : Fin S.N → V → ℕ) (tp : Fin S.k → V → ℕ)
    {i : Fin S.N} {v : V} (hv : v ∈ (S.K i).verts) :
    S.psi pc tp v = 3 * ((S.lay i).val : ℝ) + (pc i v : ℝ) / ((S.K i).verts.card + 1) := by
  have h : ∃ i, v ∈ (S.K i).verts := ⟨i, hv⟩
  unfold psi
  rw [dif_pos h, hS.choose_verts hv h]

theorem Valid.blk_of_mem_T (hS : S.Valid G) {j : Fin S.k} {v : V} (hv : v ∈ S.T j) :
    S.blk v = j.val := by
  have h : ∃ j, v ∈ S.T j := ⟨j, hv⟩
  unfold blk
  rw [dif_neg (hS.not_exists_verts_of_mem_T hv), dif_pos h, hS.choose_T hv h]

theorem Valid.psi_of_mem_T (hS : S.Valid G) (pc : Fin S.N → V → ℕ) (tp : Fin S.k → V → ℕ)
    {j : Fin S.k} {v : V} (hv : v ∈ S.T j) :
    S.psi pc tp v = 3 * (j.val : ℝ) + 1 + (tp j v : ℝ) / ((S.T j).card + 1) := by
  have h : ∃ j, v ∈ S.T j := ⟨j, hv⟩
  unfold psi
  rw [dif_neg (hS.not_exists_verts_of_mem_T hv), dif_pos h, hS.choose_T hv h]

theorem mem_verts_of_mem_layP {j : Fin S.k} {v : V} (hv : v ∈ S.layP j) :
    ∃ i, S.lay i = j ∧ v ∈ (S.K i).verts := by
  obtain ⟨i, hi, hv⟩ := (S.mem_layP).1 hv
  exact ⟨i, hi, (S.K i).ports_subset_verts hv⟩

theorem Valid.blk_of_mem_layP (hS : S.Valid G) {j : Fin S.k} {v : V} (hv : v ∈ S.layP j) :
    S.blk v = j.val := by
  obtain ⟨i, rfl, hv'⟩ := mem_verts_of_mem_layP hv
  exact hS.blk_of_mem_verts hv'

/-- A quotient `x/(c+1)` with `1 ≤ x ≤ c` lies in `(0,1)`. -/
theorem div_succ_mem {x c : ℕ} (h1 : 1 ≤ x) (h2 : x ≤ c) :
    0 < (x : ℝ) / (c + 1) ∧ (x : ℝ) / (c + 1) < 1 := by
  have hc : (0 : ℝ) < c + 1 := by positivity
  refine ⟨div_pos (by exact_mod_cast h1) hc, (div_lt_one hc).2 ?_⟩
  have : (x : ℝ) ≤ c := by exact_mod_cast h2
  linarith

/-- On a cluster of layer `j`: `Ψ ∈ (3j, 3j+1)`. -/
theorem Valid.psi_bounds_verts (hS : S.Valid G) {pc : Fin S.N → V → ℕ} (tp : Fin S.k → V → ℕ)
    (hpc : ∀ i, ∀ v ∈ (S.K i).verts, 1 ≤ pc i v ∧ pc i v ≤ (S.K i).verts.card)
    {i : Fin S.N} {v : V} (hv : v ∈ (S.K i).verts) :
    3 * ((S.lay i).val : ℝ) < S.psi pc tp v ∧ S.psi pc tp v < 3 * ((S.lay i).val : ℝ) + 1 := by
  rw [hS.psi_of_mem_verts pc tp hv]
  have := div_succ_mem (hpc i v hv).1 (hpc i v hv).2
  constructor <;> linarith

/-- On `T_j`: `Ψ ∈ (3j+1, 3j+2)`. -/
theorem Valid.psi_bounds_T (hS : S.Valid G) (pc : Fin S.N → V → ℕ) {tp : Fin S.k → V → ℕ}
    (htp : ∀ j, ∀ v ∈ S.T j, 1 ≤ tp j v ∧ tp j v ≤ (S.T j).card) {j : Fin S.k} {v : V}
    (hv : v ∈ S.T j) :
    3 * (j.val : ℝ) + 1 < S.psi pc tp v ∧ S.psi pc tp v < 3 * (j.val : ℝ) + 2 := by
  rw [hS.psi_of_mem_T pc tp hv]
  have := div_succ_mem (htp j v hv).1 (htp j v hv).2
  constructor <;> linarith

/-- On `LayP_j`: `Ψ ∈ (3j, 3j+1)`. -/
theorem Valid.psi_bounds_layP (hS : S.Valid G) {pc : Fin S.N → V → ℕ} (tp : Fin S.k → V → ℕ)
    (hpc : ∀ i, ∀ v ∈ (S.K i).verts, 1 ≤ pc i v ∧ pc i v ≤ (S.K i).verts.card)
    {j : Fin S.k} {v : V} (hv : v ∈ S.layP j) :
    3 * (j.val : ℝ) < S.psi pc tp v ∧ S.psi pc tp v < 3 * (j.val : ℝ) + 1 := by
  obtain ⟨i, rfl, hv'⟩ := mem_verts_of_mem_layP hv
  exact hS.psi_bounds_verts tp hpc hv'

/-- The tail of an arc of `D_j` is in block `j`. -/
theorem Valid.blk_fst_pathArcs (hS : S.Valid G) {j : Fin S.k} {a : V × V}
    (ha : a ∈ S.pathArcs j) : S.blk a.1 = j.val := by
  rcases (hS.pathArcs_ends ha).1 with h | h
  · exact hS.blk_of_mem_T h
  · exact hS.blk_of_mem_layP h

/-- [s6:lemHCCP] (proof, Step 4) "Every arc of `F⃗ - 𝒲` either has both ends in the same block, or
is an arc of some `D'_j` ... from block `j` to block `j+1`": an arc of `D_j` raises the block
index by at most one. -/
theorem Valid.blk_pathArcs (hS : S.Valid G) {j : Fin S.k} {a : V × V}
    (ha : a ∈ S.pathArcs j) : S.blk a.2 ≤ S.blk a.1 + 1 := by
  rw [hS.blk_fst_pathArcs ha]
  rcases (hS.pathArcs_ends ha).2 with h | h
  · rw [hS.blk_of_mem_T h]; omega
  · rw [hS.blk_of_mem_layP h, succ_val]
    have := Nat.mod_le (j.val + 1) S.k
    omega

/-- A cluster arc stays in its block. -/
theorem Valid.blk_O (hS : S.Valid G) {i : Fin S.N} {a : V × V} (ha : a ∈ S.O i) :
    S.blk a.2 = S.blk a.1 := by
  rw [hS.blk_of_mem_verts (Cluster.snd_mem_verts_of_orient (hS.adm i).orient ha),
    hS.blk_of_mem_verts (Cluster.fst_mem_verts_of_orient (hS.adm i).orient ha)]

/-- A cluster arc increases `Ψ` ("Bead arcs increase `Ψ`"). -/
theorem Valid.psi_lt_O (hS : S.Valid G) {pc : Fin S.N → V → ℕ} (tp : Fin S.k → V → ℕ)
    (hpc : ∀ i, ∀ a ∈ S.O i, pc i a.1 < pc i a.2) {i : Fin S.N} {a : V × V} (ha : a ∈ S.O i) :
    S.psi pc tp a.1 < S.psi pc tp a.2 := by
  rw [hS.psi_of_mem_verts pc tp (Cluster.fst_mem_verts_of_orient (hS.adm i).orient ha),
    hS.psi_of_mem_verts pc tp (Cluster.snd_mem_verts_of_orient (hS.adm i).orient ha)]
  have hc : (0 : ℝ) < (S.K i).verts.card + 1 := by positivity
  have : (pc i a.1 : ℝ) < pc i a.2 := by exact_mod_cast hpc i a ha
  have := div_lt_div_of_pos_right this hc
  linarith

/-- [s6:lemHCCP] (proof, Step 3) The arcs of `D'_j ⊆ D_j` increase `Ψ`, except the arcs of
`D'_{k-1}` into `LayP_0`: "An arc of `D'_j` from `u ∈ LayP_j` to `y ∈ T_j` has
`Ψ(u) < 3j+1 < Ψ(y)`. An arc inside `T_j` increases `tp_j`. For `j ≤ k-2`, an arc of `D'_j` with
head `v ∈ LayP_{j+1}` has tail in `T_j ∪ LayP_j`, and `Ψ(tail) < 3j+2 < 3j+3 < Ψ(v)`." -/
theorem Valid.psi_lt_pathArcs (hS : S.Valid G) {pc : Fin S.N → V → ℕ} {tp : Fin S.k → V → ℕ}
    (hpc : ∀ i, ∀ v ∈ (S.K i).verts, 1 ≤ pc i v ∧ pc i v ≤ (S.K i).verts.card)
    (htp : ∀ j, ∀ v ∈ S.T j, 1 ≤ tp j v ∧ tp j v ≤ (S.T j).card)
    {j : Fin S.k} {a : V × V} (ha : a ∈ S.pathArcs j)
    (hTT : a.1 ∈ S.T j → a.2 ∈ S.T j → tp j a.1 < tp j a.2)
    (hW : a.2 ∈ S.layP (S.succ j) → j.val + 1 < S.k) :
    S.psi pc tp a.1 < S.psi pc tp a.2 := by
  have h1 : S.psi pc tp a.1 < 3 * (j.val : ℝ) + 2 := by
    rcases (hS.pathArcs_ends ha).1 with h | h
    · exact (hS.psi_bounds_T pc htp h).2
    · have := (hS.psi_bounds_layP tp hpc h).2; linarith
  by_cases h2 : a.2 ∈ S.layP (S.succ j)
  · have hj := hW h2
    have hs : (S.succ j).val = j.val + 1 := by rw [succ_val]; exact Nat.mod_eq_of_lt hj
    have := (hS.psi_bounds_layP tp hpc h2).1
    rw [hs] at this
    push_cast at this
    linarith
  · have h2T : a.2 ∈ S.T j := ((hS.pathArcs_ends ha).2).resolve_right h2
    rcases (hS.pathArcs_ends ha).1 with h | h
    · rw [hS.psi_of_mem_T pc tp h, hS.psi_of_mem_T pc tp h2T]
      have hc : (0 : ℝ) < (S.T j).card + 1 := by positivity
      have : (tp j a.1 : ℝ) < tp j a.2 := by exact_mod_cast hTT h h2T
      have := div_lt_div_of_pos_right this hc
      linarith
    · have := (hS.psi_bounds_layP tp hpc h).2
      have := (hS.psi_bounds_T pc htp h2T).1
      linarith

/-! ## Step 2: balance, in integer form -/

/-- A vertex outside `V(𝒦_i)` meets no arc of `O_i`. -/
theorem Valid.exc_O_eq_zero_of_not_mem (hS : S.Valid G) {i : Fin S.N} {v : V}
    (hv : v ∉ (S.K i).verts) : exc (S.O i) v = 0 := by
  have h1 : outDeg (S.O i) v = 0 := outDeg_eq_zero_iff.2 fun w hw =>
    hv (Cluster.fst_mem_verts_of_orient (hS.adm i).orient hw)
  have h2 : inDeg (S.O i) v = 0 := inDeg_eq_zero_iff.2 fun u hu =>
    hv (Cluster.snd_mem_verts_of_orient (hS.adm i).orient hu)
  unfold exc
  rw [h1, h2]
  rfl

/-- [s6:lemHCCP] (proof, Step 2) "Every hub is balanced ... A hub ... meets only arcs of its own
cluster, which are balanced at hubs by admissibility": `∑_i exc_{O_i}(v) = exc(v)` (the excess of
`v` as a port, `0` if `v` is no port). -/
theorem Valid.sum_exc_O (hS : S.Valid G) (v : V) : ∑ i, exc (S.O i) v = S.pexc v := by
  unfold pexc
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs with hp
  · rfl
  · by_cases hv : v ∈ (S.K i).verts
    · have hh : v ∈ (S.K i).hubs := ((S.K i).mem_verts.1 hv).resolve_right hp
      unfold exc
      rw [(hS.adm i).hub_bal v hh, sub_self]
    · exact hS.exc_O_eq_zero_of_not_mem hv

/-- The port indicator: `v` lies in at most one `LayP_j`. -/
theorem Valid.sum_layP_ind_le_one (hS : S.Valid G) (v : V) :
    ∑ j, (if v ∈ S.layP j then (1 : ℤ) else 0) ≤ 1 := by
  rw [Finset.sum_boole]
  have : (Finset.univ.filter (fun j => v ∈ S.layP j)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    by_contra hne
    exact Finset.disjoint_left.1 (S.layP_disjoint hS.D_KK hne) (Finset.mem_filter.1 ha).2
      (Finset.mem_filter.1 hb).2
  exact_mod_cast this

/-- A vertex in no `LayP_j` is no port, so its excess is `0`. -/
theorem pexc_eq_zero_of_forall_not_mem {v : V} (h : ∀ j, v ∉ S.layP j) : S.pexc v = 0 := by
  unfold pexc
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [if_neg]
  intro hp
  exact h (S.lay i) (S.ports_subset_layP i hp)

end HccpData

end EG.Chain
