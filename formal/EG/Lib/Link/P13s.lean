module

public import EG.Spec.Link.P13s
public import EG.Spec.Ext.BMProp12
public import EG.Lib.Found.Graph
public import EG.Lib.Found.NbrSetDeg

/-!
# Proposition 13* (manuscript s3:propP13s): the proof — P3-s3

Manuscript v6.1, `s3.tex`, proof of Proposition [s3:propP13s]. [BM, Proposition 12]
([s1:citProp12], `Spec.BMProp12Statement`) enters as a hypothesis; the stub
`EG/Proof/Todo/P13s.lean` supplies it.

The two maximal objects of the proof are taken of maximum cardinality (which gives the
maximality properties the TeX uses):
* a collection of vertex-disjoint `λ_*`-stars (`StarColl`), with the property "every
  `w ∈ W \ Cen` has at most `λ_*-1` neighbours in `G-F` in `V(G) \ (W ∪ Lvs)`"
  (`star_max_nbrs`);
* the bipartite graph `H` (`BipValid`: sides `W`, `X`, `H ⊆ G-F`, `d_H(x) = d_*` on `X`,
  `d_H(w) ≤ Δ_*` on `W`) in place of the greedy one, with the property used in Case 2: "a vertex
  `v ∉ W ∪ X` has fewer than `d_*` neighbours in `W` of `H`-degree below `Δ_*`"
  (`bip_max_prop`; for the greedy `H` this holds because degrees only increase).
-/

public section

namespace EG.P13sProof

open Finset

variable {V : Type*} [DecidableEq V]

/-! ### Stars -/

/-- A collection of vertex-disjoint stars with centres `C ⊆ W`, each with exactly `λ` leaves
`lv c ⊆ V(K) \ W` adjacent to `c` in `K`. -/
def StarColl (K : FGraph V) (W : Finset V) (lam : ℕ) (C : Finset V) (lv : V → Finset V) :
    Prop :=
  C ⊆ W ∧ (∀ c ∈ C, (lv c).card = lam ∧ lv c ⊆ K.verts \ W ∧ ∀ x ∈ lv c, K.Adj c x) ∧
    (C : Set V).PairwiseDisjoint lv

theorem exists_max_stars (K : FGraph V) (W : Finset V) (lam : ℕ) :
    ∃ C lv, StarColl K W lam C lv ∧
      ∀ C' lv', StarColl K W lam C' lv' → C'.card ≤ C.card := by
  classical
  let P : ℕ → Prop := fun k => ∃ C lv, StarColl K W lam C lv ∧ C.card = k
  have h0 : P 0 := ⟨∅, fun _ => ∅, ⟨Finset.empty_subset _, by simp, by simp⟩, rfl⟩
  obtain ⟨C, lv, hC, hCc⟩ := Nat.findGreatest_spec (P := P) (Nat.zero_le W.card) h0
  refine ⟨C, lv, hC, fun C' lv' hC' => ?_⟩
  rw [hCc]
  exact Nat.le_findGreatest (Finset.card_le_card hC'.1) ⟨C', lv', hC', rfl⟩

/-- "By maximality, every `w ∈ W \ Cen` has at most `λ_*-1` neighbours in `G-F` in
`V(G) \ (W ∪ Lvs)`." -/
theorem star_max_nbrs (K : FGraph V) (W : Finset V) (lam : ℕ) (C : Finset V)
    (lv : V → Finset V) (hC : StarColl K W lam C lv)
    (hmax : ∀ C' lv', StarColl K W lam C' lv' → C'.card ≤ C.card) :
    ∀ w ∈ W, w ∉ C → (K.nbrs w \ (W ∪ C.biUnion lv)).card < lam := by
  classical
  intro w hw hwC
  by_contra hlt
  push Not at hlt
  obtain ⟨S, hS, hSc⟩ := Finset.exists_subset_card_eq hlt
  set lv' := Function.update lv w S with hlv'
  have hlv'w : lv' w = S := by simp [hlv']
  have hlv'c : ∀ c ∈ C, lv' c = lv c := fun c hc => by
    have : c ≠ w := fun h => hwC (h ▸ hc)
    simp [hlv', this]
  have hval : StarColl K W lam (insert w C) lv' := by
    refine ⟨Finset.insert_subset hw hC.1, ?_, ?_⟩
    · intro c hc
      rcases Finset.mem_insert.1 hc with rfl | hc
      · rw [hlv'w]
        refine ⟨hSc, fun x hx => ?_, fun x hx => ?_⟩
        · have := hS hx
          rw [Finset.mem_sdiff, Finset.mem_union, not_or] at this
          exact Finset.mem_sdiff.2 ⟨K.nbrs_subset_verts _ this.1, this.2.1⟩
        · exact FGraph.mem_nbrs.1 (Finset.mem_sdiff.1 (hS hx)).1
      · rw [hlv'c c hc]; exact hC.2.1 c hc
    · intro a ha b hb hab
      rw [Finset.coe_insert] at ha hb
      rcases ha with rfl | ha <;> rcases hb with rfl | hb
      · exact absurd rfl hab
      · rw [Function.onFun, hlv'w, hlv'c b hb, Finset.disjoint_left]
        intro x hxS hxb
        have := hS hxS
        rw [Finset.mem_sdiff, Finset.mem_union, not_or] at this
        exact this.2.2 (Finset.mem_biUnion.2 ⟨b, hb, hxb⟩)
      · rw [Function.onFun, hlv'w, hlv'c a ha, Finset.disjoint_left]
        intro x hxa hxS
        have := hS hxS
        rw [Finset.mem_sdiff, Finset.mem_union, not_or] at this
        exact this.2.2 (Finset.mem_biUnion.2 ⟨a, ha, hxa⟩)
      · rw [Function.onFun, hlv'c a ha, hlv'c b hb]
        exact hC.2.2 ha hb hab
  have := hmax _ _ hval
  rw [Finset.card_insert_of_notMem hwC] at this
  omega

theorem card_leaves (K : FGraph V) (W : Finset V) (lam : ℕ) (C : Finset V)
    (lv : V → Finset V) (hC : StarColl K W lam C lv) : (C.biUnion lv).card = lam * C.card := by
  rw [Finset.card_biUnion (fun a ha b hb hab => hC.2.2 ha hb hab),
    Finset.sum_congr rfl (fun c hc => (hC.2.1 c hc).1), Finset.sum_const, smul_eq_mul,
    mul_comm]

/-! ### The bipartite graph -/

/-- A bipartite subgraph of `K` with sides `W` and `X ⊆ V(K) \ W` and edge set `E`, in which
every vertex of `X` has degree exactly `d` and every vertex of `W` degree at most `Δ`. -/
def BipValid (K : FGraph V) (W : Finset V) (d Δ : ℕ) (X : Finset V) (E : Finset (Sym2 V)) :
    Prop :=
  X ⊆ K.verts \ W ∧ E ⊆ K.edges ∧ (∀ e ∈ E, ∃ w ∈ W, ∃ x ∈ X, e = s(w, x)) ∧
    (∀ x ∈ X, degE E x = d) ∧ (∀ w ∈ W, degE E w ≤ Δ)

theorem exists_max_bip (K : FGraph V) (W : Finset V) (d Δ : ℕ) :
    ∃ X E, BipValid K W d Δ X E ∧ ∀ X' E', BipValid K W d Δ X' E' → X'.card ≤ X.card := by
  classical
  set T := (K.verts.powerset ×ˢ K.edges.powerset).filter (fun p => BipValid K W d Δ p.1 p.2)
    with hT
  have hne : T.Nonempty := ⟨(∅, ∅), by
    rw [hT, Finset.mem_filter, Finset.mem_product, Finset.mem_powerset, Finset.mem_powerset]
    refine ⟨⟨Finset.empty_subset _, Finset.empty_subset _⟩, Finset.empty_subset _,
      Finset.empty_subset _, by simp, by simp, fun w _ => ?_⟩
    simp [degE, edgesAt]⟩
  obtain ⟨⟨X, E⟩, hp, hmax⟩ := Finset.exists_max_image T (fun p => p.1.card) hne
  rw [hT, Finset.mem_filter] at hp
  refine ⟨X, E, hp.2, fun X' E' hv => ?_⟩
  have hmem : (X', E') ∈ T := by
    rw [hT, Finset.mem_filter, Finset.mem_product, Finset.mem_powerset, Finset.mem_powerset]
    exact ⟨⟨hv.1.trans Finset.sdiff_subset, hv.2.1⟩, hv⟩
  exact hmax _ hmem

/-- Degrees in the star `{s(w,v) : w ∈ S}` (`v ∉ S`). -/
theorem degE_star (S : Finset V) (v u : V) (hv : v ∉ S) :
    degE (S.image (fun w => s(w, v))) u = if u = v then S.card else if u ∈ S then 1 else 0 := by
  classical
  unfold degE
  split_ifs with h1 h2
  · subst h1
    have : edgesAt (S.image (fun w => s(w, u))) u = S.image (fun w => s(w, u)) := by
      ext e; simp only [FGraph.mem_edgesAt, Finset.mem_image]
      constructor
      · exact fun h => h.1
      · rintro ⟨w, hw, rfl⟩; exact ⟨⟨w, hw, rfl⟩, Sym2.mem_mk_right _ _⟩
    rw [this, Finset.card_image_of_injOn]
    intro a ha b hb hab
    simp only at hab
    rcases Sym2.eq_iff.1 hab with ⟨h, -⟩ | ⟨h, -⟩
    · exact h
    · exact absurd (h ▸ ha) hv
  · have : edgesAt (S.image (fun w => s(w, v))) u = {s(u, v)} := by
      ext e; simp only [FGraph.mem_edgesAt, Finset.mem_image, Finset.mem_singleton]
      constructor
      · rintro ⟨⟨w, hw, rfl⟩, hu⟩
        rcases Sym2.mem_iff.1 hu with rfl | rfl
        · rfl
        · exact absurd rfl h1
      · rintro rfl; exact ⟨⟨u, h2, rfl⟩, Sym2.mem_mk_left _ _⟩
    rw [this, Finset.card_singleton]
  · rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro e he
    rw [FGraph.mem_edgesAt, Finset.mem_image] at he
    obtain ⟨⟨w, hw, rfl⟩, hu⟩ := he
    rcases Sym2.mem_iff.1 hu with rfl | rfl
    · exact h2 hw
    · exact h1 rfl

theorem degE_union_of_disjoint {E N : Finset (Sym2 V)} (h : Disjoint E N) (u : V) :
    degE (E ∪ N) u = degE E u + degE N u := by
  unfold degE edgesAt
  rw [Finset.filter_union, Finset.card_union_of_disjoint (Finset.disjoint_filter_filter h)]

/-- The maximality property of `H` used in Case 2: a vertex `v ∈ V(K) \ W` outside `X` has fewer
than `d` neighbours in `W` of `H`-degree below `Δ`. -/
theorem bip_max_prop (K : FGraph V) (W : Finset V) (d Δ : ℕ) (X : Finset V)
    (E : Finset (Sym2 V)) (hB : BipValid K W d Δ X E)
    (hmax : ∀ X' E', BipValid K W d Δ X' E' → X'.card ≤ X.card) :
    ∀ v ∈ K.verts \ W, v ∉ X → ((K.nbrs v ∩ W).filter (fun w => degE E w < Δ)).card < d := by
  classical
  intro v hv hvX
  obtain ⟨hvV, hvW⟩ := Finset.mem_sdiff.1 hv
  by_contra hlt
  push Not at hlt
  obtain ⟨S, hS, hSc⟩ := Finset.exists_subset_card_eq hlt
  have hSW : ∀ w ∈ S, w ∈ W := fun w hw => (Finset.mem_inter.1 (Finset.mem_filter.1 (hS hw)).1).2
  have hSadj : ∀ w ∈ S, K.Adj v w := fun w hw =>
    FGraph.mem_nbrs.1 (Finset.mem_inter.1 (Finset.mem_filter.1 (hS hw)).1).1
  have hSdeg : ∀ w ∈ S, degE E w < Δ := fun w hw => (Finset.mem_filter.1 (hS hw)).2
  have hvS : v ∉ S := fun h => hvW (hSW v h)
  set N := S.image (fun w => s(w, v)) with hN
  -- no edge of `E` contains `v`
  have hEv : ∀ e ∈ E, v ∉ e := by
    intro e he hve
    obtain ⟨w, hw, x, hx, rfl⟩ := hB.2.2.1 e he
    rcases Sym2.mem_iff.1 hve with rfl | rfl
    · exact hvW hw
    · exact hvX hx
  have hdisj : Disjoint E N := by
    rw [Finset.disjoint_left]
    intro e heE heN
    obtain ⟨w, -, rfl⟩ := Finset.mem_image.1 heN
    exact hEv _ heE (Sym2.mem_mk_right _ _)
  have hval : BipValid K W d Δ (insert v X) (E ∪ N) := by
    refine ⟨Finset.insert_subset hv hB.1, Finset.union_subset hB.2.1 ?_, ?_, ?_, ?_⟩
    · intro e he
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 he
      have := hSadj w hw
      rw [FGraph.adj_iff, Sym2.eq_swap] at this
      exact this
    · intro e he
      rcases Finset.mem_union.1 he with he | he
      · obtain ⟨w, hw, x, hx, rfl⟩ := hB.2.2.1 e he
        exact ⟨w, hw, x, Finset.mem_insert_of_mem hx, rfl⟩
      · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 he
        exact ⟨w, hSW w hw, v, Finset.mem_insert_self _ _, rfl⟩
    · intro x hx
      rw [degE_union_of_disjoint hdisj, hN, degE_star S v x hvS]
      rcases Finset.mem_insert.1 hx with rfl | hx
      · rw [if_pos rfl, hSc]
        have : degE E x = 0 := by
          unfold degE
          rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
          intro e he
          rw [FGraph.mem_edgesAt] at he
          exact hEv e he.1 he.2
        omega
      · have hxv : x ≠ v := fun h => hvX (h ▸ hx)
        have hxS : x ∉ S := fun h => (Finset.mem_sdiff.1 (hB.1 hx)).2 (hSW x h)
        rw [if_neg hxv, if_neg hxS, hB.2.2.2.1 x hx, Nat.add_zero]
    · intro w hw
      rw [degE_union_of_disjoint hdisj, hN, degE_star S v w hvS]
      have hwv : w ≠ v := fun h => hvW (h ▸ hw)
      rw [if_neg hwv]
      split_ifs with hwS
      · have := hSdeg w hwS; omega
      · have := hB.2.2.2.2 w hw; omega
  have := hmax _ _ hval
  rw [Finset.card_insert_of_notMem hvX] at this
  omega

/-- The double count of the proof: `(Δ_*-λ_*+1)|Sat| ≤ e_H(Sat, X ∩ Lvs) ≤ d_*|Lvs|`, for a set
`Sat ⊆ W` of vertices of `H`-degree `Δ_*` each with at most `λ_*-1` `H`-neighbours outside
`Lvs`. -/
theorem sat_count (K : FGraph V) (W : Finset V) (d Δ lam : ℕ) (X : Finset V)
    (E : Finset (Sym2 V)) (hB : BipValid K W d Δ X E) (Lvs Sat : Finset V) (hSatW : Sat ⊆ W)
    (hdeg : ∀ w ∈ Sat, degE E w = Δ)
    (hout : ∀ w ∈ Sat, (X.filter (fun x => s(w, x) ∈ E ∧ x ∉ Lvs)).card ≤ lam - 1) :
    (Δ - (lam - 1)) * Sat.card ≤ d * Lvs.card := by
  classical
  -- `H`-neighbours of `w ∈ W`
  have hHn : ∀ w ∈ W, (X.filter (fun x => s(w, x) ∈ E)).card = degE E w := by
    intro w hw
    unfold degE
    symm
    refine Finset.card_bij (fun e he => Sym2.Mem.other (FGraph.mem_edgesAt.1 he).2) ?_ ?_ ?_
    · intro e he
      have he' := FGraph.mem_edgesAt.1 he
      obtain ⟨w', hw', x, hx, rfl⟩ := hB.2.2.1 e he'.1
      have hxW : x ∉ W := (Finset.mem_sdiff.1 (hB.1 hx)).2
      have hww' : w = w' := by
        rcases Sym2.mem_iff.1 he'.2 with h | h
        · exact h
        · exact absurd (h ▸ hw) hxW
      subst hww'
      have hoth : Sym2.Mem.other he'.2 = x := by
        have := Sym2.other_spec he'.2
        rw [Sym2.eq_iff] at this
        rcases this with ⟨-, h⟩ | ⟨h, -⟩
        · exact h
        · exact absurd (h ▸ hw) hxW
      rw [Finset.mem_filter, hoth]
      exact ⟨hx, he'.1⟩
    · intro e1 he1 e2 he2 h
      rw [← Sym2.other_spec (FGraph.mem_edgesAt.1 he1).2,
        ← Sym2.other_spec (FGraph.mem_edgesAt.1 he2).2, h]
    · intro x hx
      rw [Finset.mem_filter] at hx
      refine ⟨s(w, x), FGraph.mem_edgesAt.2 ⟨hx.2, Sym2.mem_mk_left _ _⟩, ?_⟩
      have hxW : x ∉ W := (Finset.mem_sdiff.1 (hB.1 hx.1)).2
      have := Sym2.other_spec (Sym2.mem_mk_left w x)
      rw [Sym2.eq_iff] at this
      rcases this with ⟨-, h⟩ | ⟨h, -⟩
      · exact h
      · exact absurd (h ▸ hw) hxW
  -- each `w ∈ Sat` has at least `Δ-(λ-1)` `H`-neighbours in `Lvs`
  have hper : ∀ w ∈ Sat, Δ - (lam - 1) ≤ (X.filter (fun x => s(w, x) ∈ E ∧ x ∈ Lvs)).card := by
    intro w hw
    have h1 := hHn w (hSatW hw)
    rw [hdeg w hw] at h1
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := X.filter (fun x => s(w, x) ∈ E)) (fun x => x ∈ Lvs)
    rw [Finset.filter_filter, Finset.filter_filter] at hsplit
    have h2 := hout w hw
    omega
  -- double count
  have hsum : ∑ w ∈ Sat, (X.filter (fun x => s(w, x) ∈ E ∧ x ∈ Lvs)).card ≤ d * Lvs.card := by
    have e0 : ∀ w, X.filter (fun x => s(w, x) ∈ E ∧ x ∈ Lvs) =
        (X ∩ Lvs).filter (fun x => s(w, x) ∈ E) := by
      intro w; ext x; simp only [Finset.mem_filter, Finset.mem_inter]; tauto
    have e1 : ∑ w ∈ Sat, (X.filter (fun x => s(w, x) ∈ E ∧ x ∈ Lvs)).card =
        ∑ x ∈ X ∩ Lvs, (Sat.filter (fun w => s(w, x) ∈ E)).card := by
      simp only [e0, Finset.card_filter]
      exact Finset.sum_comm
    rw [e1]
    have h2 : ∀ x ∈ X ∩ Lvs, (Sat.filter (fun w => s(w, x) ∈ E)).card ≤ d := by
      intro x hx
      have hxX := (Finset.mem_inter.1 hx).1
      have hxW : x ∉ W := (Finset.mem_sdiff.1 (hB.1 hxX)).2
      rw [← hB.2.2.2.1 x hxX]
      unfold degE
      refine Finset.card_le_card_of_injOn (fun w => s(w, x)) (fun w hw => ?_) (fun w hw w' hw' h => ?_)
      · exact FGraph.mem_edgesAt.2 ⟨(Finset.mem_filter.1 hw).2, Sym2.mem_mk_right _ _⟩
      · simp only at h
        rcases Sym2.eq_iff.1 h with ⟨h1, -⟩ | ⟨h1, -⟩
        · exact h1
        · exact absurd (h1 ▸ hSatW (Finset.mem_filter.1 hw).1) hxW
    calc ∑ x ∈ X ∩ Lvs, (Sat.filter (fun w => s(w, x) ∈ E)).card ≤ ∑ _x ∈ X ∩ Lvs, d :=
          Finset.sum_le_sum h2
      _ = d * (X ∩ Lvs).card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ d * Lvs.card := Nat.mul_le_mul_left _ (Finset.card_le_card Finset.inter_subset_right)
  calc (Δ - (lam - 1)) * Sat.card = ∑ _w ∈ Sat, (Δ - (lam - 1)) := by
        rw [Finset.sum_const, smul_eq_mul, mul_comm]
    _ ≤ ∑ w ∈ Sat, (X.filter (fun x => s(w, x) ∈ E ∧ x ∈ Lvs)).card := Finset.sum_le_sum hper
    _ ≤ d * Lvs.card := hsum

universe u

/-- [s3:propP13s] Proposition 13*, from [BM, Proposition 12]. -/
theorem p13s (h12 : Spec.BMProp12Statement.{u}) : Spec.P13sStatement.{u} := by
  intro V _ G ε' s₁ σ lam d Δ W F hG hn hε1 hε2 hWV hW1 hW23 hFE hFc hσ hlam hd hlamΔ hσL
    hDl hs₁
  classical
  set K := G.deleteEdges F with hKdef
  have hKv : K.verts = G.verts := rfl
  set L := Real.logb 2 (G.card : ℝ) with hLdef
  have hL1 : 1 ≤ L := by
    rw [hLdef, Real.le_logb_iff_rpow_le (by norm_num) (by exact_mod_cast (by omega : 0 < G.card))]
    simp only [Real.rpow_one]; exact_mod_cast hn
  have hL2 : 1 ≤ L ^ 2 := one_le_pow₀ hL1
  have hε : 0 < ε' := lt_of_lt_of_le (by positivity) hε1
  have hW0 : (1 : ℝ) ≤ W.card := by exact_mod_cast hW1
  have hlam1 : (1 : ℝ) ≤ lam := by exact_mod_cast hlam
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  -- `σ_* ≥ 24L^2/ε' ≥ 24`
  have h24 : (24 : ℝ) ≤ 24 * L ^ 2 / ε' := by
    rw [le_div_iff₀ hε]; linarith
  have hσ24 : (24 : ℝ) ≤ σ := h24.trans hσL
  have hσinv : 1 / σ ≤ ε' / (24 * L ^ 2) := by
    rw [div_le_div_iff₀ hσ (by positivity)]
    have := (div_le_iff₀ hε).1 hσL
    linarith
  -- the maximal star collection
  obtain ⟨C, lv, hC, hCmax⟩ := exists_max_stars K W lam
  by_cases ha : (W.card : ℝ) / σ ≤ C.card
  · left
    refine ⟨C, lv, hC.1, ha, fun c hc => ⟨(hC.2.1 c hc).1, ?_, (hC.2.1 c hc).2.2⟩, hC.2.2⟩
    rw [← hKv]; exact (hC.2.1 c hc).2.1
  right
  push Not at ha
  have hstar := star_max_nbrs K W lam C lv hC hCmax
  have hLvsc : (C.biUnion lv).card = lam * C.card := card_leaves K W lam C lv hC
  set Lvs := C.biUnion lv with hLvs
  -- the bipartite graph
  obtain ⟨X, E, hB, hBmax⟩ := exists_max_bip K W d Δ
  have hBprop := bip_max_prop K W d Δ X E hB hBmax
  set Sat := (W \ C).filter (fun w => degE E w = Δ) with hSat
  have hSatW : Sat ⊆ W := fun w hw => (Finset.mem_sdiff.1 (Finset.mem_filter.1 hw).1).1
  set Bl := C ∪ Sat with hBl
  have hBlW : Bl ⊆ W := Finset.union_subset hC.1 hSatW
  -- (s3:eqP13a)
  have hP13a : (((K.nbrSet (W \ C)).card : ℕ) : ℝ) ≤ (1 + lam) * C.card + (lam - 1) * W.card := by
    have hsub : K.nbrSet (W \ C) ⊆
        (C ∪ Lvs) ∪ (W \ C).biUnion (fun w => K.nbrs w \ (W ∪ Lvs)) := by
      intro x hx
      rw [FGraph.mem_nbrSet] at hx
      obtain ⟨hxV, hxWC, w, hw, hadj⟩ := hx
      rw [Finset.mem_union, Finset.mem_union]
      by_cases hxW : x ∈ W
      · left; left
        by_contra hxC
        exact hxWC (Finset.mem_sdiff.2 ⟨hxW, hxC⟩)
      · by_cases hxL : x ∈ Lvs
        · left; right; exact hxL
        · right
          refine Finset.mem_biUnion.2 ⟨w, hw, Finset.mem_sdiff.2 ⟨FGraph.mem_nbrs.2 hadj, ?_⟩⟩
          rw [Finset.mem_union]; tauto
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_union_le (C ∪ Lvs) ((W \ C).biUnion (fun w => K.nbrs w \ (W ∪ Lvs)))
    have h3 := Finset.card_union_le C Lvs
    have h4 : ((W \ C).biUnion (fun w => K.nbrs w \ (W ∪ Lvs))).card ≤ (W \ C).card * (lam - 1) := by
      refine Finset.card_biUnion_le.trans ?_
      calc ∑ w ∈ W \ C, (K.nbrs w \ (W ∪ Lvs)).card ≤ ∑ _w ∈ W \ C, (lam - 1) :=
            Finset.sum_le_sum fun w hw => by
              have := hstar w (Finset.mem_sdiff.1 hw).1 (Finset.mem_sdiff.1 hw).2; omega
        _ = (W \ C).card * (lam - 1) := by rw [Finset.sum_const, smul_eq_mul]
    have h5 : (W \ C).card ≤ W.card := Finset.card_le_card Finset.sdiff_subset
    have hN : (K.nbrSet (W \ C)).card ≤ C.card + lam * C.card + W.card * (lam - 1) := by
      have := Nat.mul_le_mul_right (lam - 1) h5
      omega
    have hc : ((lam - 1 : ℕ) : ℝ) = (lam : ℝ) - 1 := by rw [Nat.cast_sub hlam]; simp
    have : ((K.nbrSet (W \ C)).card : ℝ) ≤ C.card + lam * C.card + W.card * ((lam - 1 : ℕ) : ℝ) := by
      exact_mod_cast hN
    rw [hc] at this
    linarith
  -- saturated vertices: `(Δ_*-λ_*)|Sat| ≤ d_*|Lvs| < d_*λ_*|W|/σ_*`
  have hout : ∀ w ∈ Sat, (X.filter (fun x => s(w, x) ∈ E ∧ x ∉ Lvs)).card ≤ lam - 1 := by
    intro w hw
    have hwWC := (Finset.mem_filter.1 hw).1
    have h1 := hstar w (Finset.mem_sdiff.1 hwWC).1 (Finset.mem_sdiff.1 hwWC).2
    have hsub : X.filter (fun x => s(w, x) ∈ E ∧ x ∉ Lvs) ⊆ K.nbrs w \ (W ∪ Lvs) := by
      intro x hx
      obtain ⟨hxX, hxE, hxL⟩ := Finset.mem_filter.1 hx
      refine Finset.mem_sdiff.2 ⟨FGraph.mem_nbrs.2 (hB.2.1 hxE), ?_⟩
      rw [Finset.mem_union, not_or]
      exact ⟨(Finset.mem_sdiff.1 (hB.1 hxX)).2, hxL⟩
    have := Finset.card_le_card hsub
    omega
  have hsc := sat_count K W d Δ lam X E hB Lvs Sat hSatW (fun w hw => (Finset.mem_filter.1 hw).2)
    hout
  rw [hLvsc] at hsc
  have hscR : ((Δ : ℝ) - lam + 1) * Sat.card ≤ d * (lam * C.card) := by
    have e : ((Δ - (lam - 1) : ℕ) : ℝ) = (Δ : ℝ) - lam + 1 := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub hlam]; push_cast; ring
    rw [← e]; exact_mod_cast hsc
  have hS0 : (0 : ℝ) ≤ Sat.card := Nat.cast_nonneg _
  have hq0 : 0 < 8 * (d : ℝ) * lam * L ^ 2 / (ε' * σ) := by positivity
  have hSat : (Sat.card : ℝ) < ε' * W.card / (8 * L ^ 2) := by
    have h1 : 8 * (d : ℝ) * lam * L ^ 2 / (ε' * σ) * Sat.card < d * lam * W.card / σ := by
      have hC' : (d : ℝ) * (lam * C.card) < d * lam * W.card / σ := by
        have : (d : ℝ) * lam * C.card < d * lam * (W.card / σ) :=
          mul_lt_mul_of_pos_left ha (by positivity)
        calc (d : ℝ) * (lam * C.card) = d * lam * C.card := by ring
          _ < d * lam * (W.card / σ) := this
          _ = d * lam * W.card / σ := by ring
      have hq1 := mul_le_mul_of_nonneg_right hDl hS0
      have hq2 : ((Δ : ℝ) - lam) * Sat.card ≤ ((Δ : ℝ) - lam + 1) * Sat.card := by linarith
      linarith
    have h2 : 8 * (d : ℝ) * lam * L ^ 2 * Sat.card < ε' * (d * lam * W.card) := by
      have := mul_lt_mul_of_pos_right h1 (mul_pos hε hσ)
      have e1 : 8 * (d : ℝ) * lam * L ^ 2 / (ε' * σ) * Sat.card * (ε' * σ) =
          8 * (d : ℝ) * lam * L ^ 2 * Sat.card := by field_simp
      have e2 : (d : ℝ) * lam * W.card / σ * (ε' * σ) = ε' * (d * lam * W.card) := by
        field_simp
      linarith
    rw [lt_div_iff₀ (by positivity)]
    have hdl : (0 : ℝ) < d * lam := by positivity
    have e3 : (Sat.card : ℝ) * (8 * L ^ 2) * (d * lam) = 8 * (d : ℝ) * lam * L ^ 2 * Sat.card := by
      ring
    have e4 : ε' * W.card * (d * lam) = ε' * (d * lam * W.card) := by ring
    have : (Sat.card : ℝ) * (8 * L ^ 2) * (d * lam) < ε' * W.card * (d * lam) := by
      rw [e3, e4]; exact h2
    exact lt_of_mul_lt_mul_right this hdl.le
  -- (s3:eqP13b)
  have hCW : (C.card : ℝ) < ε' * W.card / (24 * L ^ 2) := by
    calc (C.card : ℝ) < W.card / σ := ha
      _ = W.card * (1 / σ) := by ring
      _ ≤ W.card * (ε' / (24 * L ^ 2)) := mul_le_mul_of_nonneg_left hσinv (by positivity)
      _ = ε' * W.card / (24 * L ^ 2) := by ring
  have hBlc : (Bl.card : ℝ) < ε' * W.card / (6 * L ^ 2) := by
    have h1 : (Bl.card : ℝ) ≤ C.card + Sat.card := by exact_mod_cast Finset.card_union_le C Sat
    have e : ε' * W.card / (24 * L ^ 2) + ε' * W.card / (8 * L ^ 2) = ε' * W.card / (6 * L ^ 2) := by
      field_simp; ring
    linarith
  have hεL : ε' / L ^ 2 ≤ 1 := by rw [div_le_one (by positivity)]; linarith
  have hBl6 : ε' * W.card / (6 * L ^ 2) ≤ W.card / 6 := by
    have : ε' * W.card / (6 * L ^ 2) = (ε' / L ^ 2) * (W.card / 6) := by field_simp
    rw [this]
    exact mul_le_of_le_one_left (by positivity) hεL
  -- `U := W \ Bl`
  set U := W \ Bl with hUdef
  have hUc : (U.card : ℝ) = W.card - Bl.card := by
    rw [hUdef, Finset.card_sdiff_of_subset hBlW, Nat.cast_sub (Finset.card_le_card hBlW)]
  have hU56 : 5 * (W.card : ℝ) / 6 < U.card := by rw [hUc]; linarith
  have hU1 : 1 ≤ U.card := by
    have : (0 : ℝ) < U.card := by linarith
    exact_mod_cast this
  have hUW : U ⊆ W := Finset.sdiff_subset
  have hUV : U ⊆ G.verts := hUW.trans hWV
  have hU23 : (U.card : ℝ) ≤ 2 * (G.card : ℝ) / 3 := by
    have : (U.card : ℝ) ≤ W.card := by exact_mod_cast Finset.card_le_card hUW
    linarith
  have hs0 : 0 ≤ s₁ := le_trans (by positivity) hs₁
  have hFU : (F.card : ℝ) ≤ s₁ * (U.card : ℝ) / 2 := by
    have h1 : (W.card : ℝ) / 2 ≤ U.card := by linarith
    have := mul_le_mul_of_nonneg_left h1 hs0
    linarith
  have hd0 : (0 : ℝ) < d := by linarith
  have hds : (d : ℝ) ≤ s₁ := by
    have := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ 8 * lam by linarith) hd0.le
    linarith
  rcases h12 V G ε' s₁ (d : ℝ) U F hG hUV hU1 hU23 hFE hFU hd0 hds with hc1 | hc2
  · -- Case 1: contradiction
    exfalso
    have hsub : K.nbrSet U ⊆ K.nbrSet (W \ C) ∪ Sat := by
      intro x hx
      rw [FGraph.mem_nbrSet] at hx
      obtain ⟨hxV, hxU, u, hu, hadj⟩ := hx
      have huWC : u ∈ W \ C := by
        rw [hUdef, Finset.mem_sdiff, hBl, Finset.mem_union, not_or] at hu
        exact Finset.mem_sdiff.2 ⟨hu.1, hu.2.1⟩
      rw [Finset.mem_union]
      by_cases hxWC : x ∈ W \ C
      · right
        rw [hUdef, Finset.mem_sdiff, not_and, not_not] at hxU
        have hxBl := hxU (Finset.mem_sdiff.1 hxWC).1
        rw [hBl, Finset.mem_union] at hxBl
        rcases hxBl with h | h
        · exact absurd h (Finset.mem_sdiff.1 hxWC).2
        · exact h
      · left
        rw [FGraph.mem_nbrSet]
        exact ⟨hxV, hxWC, u, huWC, hadj⟩
    have h1 : ((K.nbrSet U).card : ℝ) ≤ (K.nbrSet (W \ C)).card + Sat.card := by
      exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    have hSW : (Sat.card : ℝ) ≤ W.card := by exact_mod_cast Finset.card_le_card hSatW
    have h2 : s₁ * (U.card : ℝ) / (2 * d) ≥ 8 * lam * (5 * W.card / 6) / 2 := by
      rw [ge_iff_le, div_le_div_iff₀ (by norm_num) (by positivity)]
      have : 8 * (d : ℝ) * lam * (5 * W.card / 6) ≤ s₁ * U.card := by
        have hU0 : (0 : ℝ) ≤ 5 * W.card / 6 := by positivity
        have := mul_le_mul hs₁ hU56.le hU0 hs0
        linarith
      linarith only [this]
    have hCσ : (1 + (lam : ℝ)) * C.card ≤ (1 + lam) * W.card / 24 := by
      have : (C.card : ℝ) ≤ W.card / 24 := by
        have : W.card / σ ≤ W.card / 24 := div_le_div_of_nonneg_left (by positivity) (by norm_num) hσ24
        linarith
      have := mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ 1 + lam)
      linarith
    -- `(10λ/3)|W| ≤ |Nbr(U)| ≤ |Nbr(W∖Cen)| + |W| ≤ ((1+λ)/24 + λ)|W|`
    have : 8 * (lam : ℝ) * (5 * W.card / 6) / 2 ≤ (1 + lam) * W.card / 24 + lam * W.card := by
      linarith only [hc1, h2, h1, hSW, hP13a, hCσ]
    have hpos := mul_pos (by linarith : (0 : ℝ) < W.card) (by linarith : (0 : ℝ) < 55 * lam - 1)
    linarith only [this, hpos]
  · -- Case 2: part (b)
    have hsub : K.nbrSetDeg U d \ Bl ⊆ X := by
      intro v hv
      obtain ⟨hv1, hvBl⟩ := Finset.mem_sdiff.1 hv
      rw [FGraph.mem_nbrSetDeg] at hv1
      obtain ⟨hvV, hvU, hvd⟩ := hv1
      have hvW : v ∉ W := by
        intro hvW
        apply hvU
        exact Finset.mem_sdiff.2 ⟨hvW, hvBl⟩
      by_contra hvX
      have hlt := hBprop v (Finset.mem_sdiff.2 ⟨hvV, hvW⟩) hvX
      have hsub2 : K.nbrs v ∩ U ⊆ (K.nbrs v ∩ W).filter (fun w => degE E w < Δ) := by
        intro u hu
        obtain ⟨hu1, hu2⟩ := Finset.mem_inter.1 hu
        rw [hUdef, Finset.mem_sdiff, hBl, Finset.mem_union, not_or] at hu2
        refine Finset.mem_filter.2 ⟨Finset.mem_inter.2 ⟨hu1, hu2.1⟩, ?_⟩
        have hle := hB.2.2.2.2 u hu2.1
        have hne : degE E u ≠ Δ := fun h =>
          hu2.2.2 (Finset.mem_filter.2 ⟨Finset.mem_sdiff.2 ⟨hu2.1, hu2.2.1⟩, h⟩)
        omega
      have := Finset.card_le_card hsub2
      have hvd' : d ≤ (K.nbrs v ∩ U).card := by exact_mod_cast hvd
      omega
    have hX1 : ((K.nbrSetDeg U d).card : ℝ) ≤ X.card + Bl.card := by
      have h1 := Finset.card_le_card_sdiff_add_card (s := K.nbrSetDeg U d) (t := Bl)
      have h2 := Finset.card_le_card hsub
      exact_mod_cast h1.trans (Nat.add_le_add_right h2 _)
    have hXc : ε' * (W.card : ℝ) / (2 * L ^ 2) ≤ X.card := by
      have hUc' : ε' * (U.card : ℝ) / L ^ 2 = ε' * W.card / L ^ 2 - (ε' / L ^ 2) * Bl.card := by
        rw [hUc]; field_simp
      have hB0 : (0 : ℝ) ≤ Bl.card := Nat.cast_nonneg _
      have h3 : (ε' / L ^ 2) * Bl.card ≤ Bl.card := mul_le_of_le_one_left hB0 hεL
      have e4 : ε' * W.card / L ^ 2 - 2 * (ε' * W.card / (6 * L ^ 2)) =
          2 * (ε' * W.card / (2 * L ^ 2)) - ε' * W.card / (6 * L ^ 2) * 2 + 
            (ε' * W.card / (2 * L ^ 2)) - ε' * W.card / (2 * L ^ 2) := by ring
      have e5 : ε' * W.card / L ^ 2 - 2 * (ε' * W.card / (6 * L ^ 2)) - ε' * W.card / (2 * L ^ 2) =
          ε' * W.card / (6 * L ^ 2) := by field_simp; ring
      have h6 : 0 ≤ ε' * W.card / (6 * L ^ 2) := by positivity
      linarith
    -- the graph `H`
    let H : FGraph V :=
      { verts := W ∪ X
        edges := E
        edge_verts := fun e he v hv => by
          obtain ⟨w, hw, x, hx, rfl⟩ := hB.2.2.1 e he
          rw [Finset.mem_union]
          rcases Sym2.mem_iff.1 hv with rfl | rfl
          · exact Or.inl hw
          · exact Or.inr hx
        loopless := fun e he => K.loopless e (hB.2.1 he) }
    refine ⟨X, H, ?_, ⟨?_, hB.2.1⟩, rfl, ?_, hXc, fun x hx => ?_, fun w hw => ?_⟩
    · rw [← hKv]; exact hB.1
    · rw [hKv]
      exact Finset.union_subset hWV (fun x hx => (Finset.mem_sdiff.1 (hB.1 hx)).1)
    · intro e he
      rw [FGraph.mem_edgesBetween]
      obtain ⟨w, hw, x, hx, rfl⟩ := hB.2.2.1 e he
      exact ⟨(Finset.mem_sdiff.1 (hB.2.1 he)).1, w, hw, x, hx, rfl⟩
    · rw [FGraph.deg_eq_degE]; exact hB.2.2.2.1 x hx
    · rw [FGraph.deg_eq_degE]; exact hB.2.2.2.2 w hw

end EG.P13sProof
