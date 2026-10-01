module

public import EG.Lib.Chain.MedExc
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp

/-!
# Lemma MED (a): the median orientation is admissible and has a potential (manuscript s6:lemMED)

Probe unit P2E (probe P-2, part 1), proof round 1. For a parity-clean cluster `𝒦` and a rank
`rk` injective on the ports:
* `Cluster.medOrient_isOrientation`: `MED(≺)` orients every bead exactly once ("Every bead is
  oriented exactly once: a bead at a hub has its other end at a port, so it is oriented by the
  rule at that hub only"); this needs only `rk` injective on the ports;
* `Cluster.medOrient_hub_bal`: "Every hub of degree `2d` has exactly `d` in-arcs and `d`
  out-arcs" (the positions `medPos` of the `2d` neighbours are exactly `1, …, 2d`);
* `Cluster.medOrient_potential`: a potential `pot : V → ℝ` with values in `(0,1)` on `V(𝒦)`,
  strictly increasing along every arc. As in the manuscript, ports get
  `pot(u) = (rk(u) + 1)/(M + 2)` (with `M = max rk` on the ports; the manuscript uses the rank
  bijection onto `{1, …, |U_𝒦|}`, any strictly increasing rescaling works) and a hub `h` gets
  `(rk(u_d) + 1 + 1/2)/(M + 2)`, where `u_d` is the last in-neighbour (written as the maximum of
  `rk + 1` over the in-neighbours, `0` when there is none);
* `Cluster.medOrient_isAdmissible`: `MED(≺)` is admissible (acyclic by the potential).
-/

public section

namespace EG.Chain

variable {V : Type*} [DecidableEq V]

namespace Cluster

variable (K : Cluster V)

/-- A `B_𝒦`-neighbour of a hub is a port ("These neighbours are ports, since no bead joins two
hubs"). -/
theorem mem_ports_of_mem_beadNbrs {h w : V} (hh : h ∈ K.hubs) (hw : w ∈ K.beadNbrs h) :
    w ∈ K.ports := by
  rw [mem_beadNbrs] at hw
  rcases (K.mem_verts).1 hw.1 with h1 | h1
  · exfalso
    apply K.no_hub_hub _ hw.2
    intro v hv
    rcases Sym2.mem_iff.1 hv with rfl | rfl
    · exact hh
    · exact h1
  · exact h1

/-- `medPos` is monotone in the rank. -/
theorem medPos_le_of_rk_le (rk : V → ℕ) (h : V) {w w' : V} (hle : rk w ≤ rk w') :
    K.medPos rk h w ≤ K.medPos rk h w' := by
  unfold medPos
  exact Finset.card_le_card fun x hx => by
    rw [Finset.mem_filter] at hx ⊢
    exact ⟨hx.1, hx.2.trans hle⟩

theorem one_le_medPos (rk : V → ℕ) {h w : V} (hw : w ∈ K.beadNbrs h) : 1 ≤ K.medPos rk h w := by
  unfold medPos
  exact Finset.card_pos.2 ⟨w, Finset.mem_filter.2 ⟨hw, le_rfl⟩⟩

theorem medPos_le_card (rk : V → ℕ) (h w : V) : K.medPos rk h w ≤ (K.beadNbrs h).card := by
  unfold medPos
  exact Finset.card_filter_le _ _

/-- For `rk` injective on the ports, the positions of distinct neighbours of a hub are distinct:
a neighbour of strictly larger rank has a strictly larger position. -/
theorem medPos_lt_of_rk_lt (rk : V → ℕ) (h : V) {w w' : V} (hw' : w' ∈ K.beadNbrs h)
    (hlt : rk w < rk w') : K.medPos rk h w < K.medPos rk h w' := by
  unfold medPos
  refine Finset.card_lt_card ⟨fun x hx => ?_, fun hsub => ?_⟩
  · rw [Finset.mem_filter] at hx ⊢
    exact ⟨hx.1, hx.2.trans hlt.le⟩
  · have := hsub (Finset.mem_filter.2 ⟨hw', le_rfl⟩)
    rw [Finset.mem_filter] at this
    omega

theorem medPos_injOn {rk : V → ℕ} (hrk : Set.InjOn rk (K.ports : Set V)) {h : V}
    (hh : h ∈ K.hubs) : Set.InjOn (K.medPos rk h) (K.beadNbrs h : Set V) := by
  intro w hw w' hw' heq
  rw [Finset.mem_coe] at hw hw'
  by_contra hne
  have hrk' : rk w ≠ rk w' := fun h' =>
    hne (hrk (Finset.mem_coe.2 (K.mem_ports_of_mem_beadNbrs hh hw))
      (Finset.mem_coe.2 (K.mem_ports_of_mem_beadNbrs hh hw')) h')
  rcases Nat.lt_or_gt_of_ne hrk' with hlt | hlt
  · exact absurd heq (K.medPos_lt_of_rk_lt rk h hw' hlt).ne
  · exact absurd heq (K.medPos_lt_of_rk_lt rk h hw hlt).ne'

/-- The positions of the neighbours of a hub are exactly `1, …, n` (`n = deg_{B_𝒦}(h)`). -/
theorem image_medPos {rk : V → ℕ} (hrk : Set.InjOn rk (K.ports : Set V)) {h : V}
    (hh : h ∈ K.hubs) :
    (K.beadNbrs h).image (K.medPos rk h) = Finset.Icc 1 (K.beadNbrs h).card := by
  apply Finset.eq_of_subset_of_card_le
  · intro i hi
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hi
    exact Finset.mem_Icc.2 ⟨K.one_le_medPos rk hw, K.medPos_le_card rk h w⟩
  · rw [Nat.card_Icc, Finset.card_image_of_injOn (K.medPos_injOn hrk hh)]
    omega

/-- The number of neighbours `u_i` of a hub with a given property of the position `i`. -/
theorem card_filter_medPos {rk : V → ℕ} (hrk : Set.InjOn rk (K.ports : Set V)) {h : V}
    (hh : h ∈ K.hubs) (P : ℕ → Prop) [DecidablePred P] :
    ((K.beadNbrs h).filter (fun w => P (K.medPos rk h w))).card =
      ((Finset.Icc 1 (K.beadNbrs h).card).filter P).card := by
  rw [← K.image_medPos hrk hh, Finset.filter_image,
    Finset.card_image_of_injOn ((K.medPos_injOn hrk hh).mono (Finset.coe_subset.2
      (Finset.filter_subset _ _)))]

theorem card_Icc_filter_two_mul_le (n : ℕ) :
    ((Finset.Icc 1 n).filter (fun i => 2 * i ≤ n)).card = n / 2 := by
  have : (Finset.Icc 1 n).filter (fun i => 2 * i ≤ n) = Finset.Icc 1 (n / 2) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  rw [this, Nat.card_Icc]
  omega

/-- The arcs of an arc set `A` leaving `h`, via their heads. -/
theorem outDeg_eq_card_image (A : Finset (V × V)) (h : V) :
    outDeg A h = ((A.filter (fun a => a.1 = h)).image Prod.snd).card := by
  unfold outDeg
  rw [Finset.card_image_of_injOn]
  intro x hx y hy hxy
  have h1 := (Finset.mem_filter.1 hx).2
  have h2 := (Finset.mem_filter.1 hy).2
  exact Prod.ext (h1.trans h2.symm) hxy

theorem inDeg_eq_card_image (A : Finset (V × V)) (h : V) :
    inDeg A h = ((A.filter (fun a => a.2 = h)).image Prod.fst).card := by
  unfold inDeg
  rw [Finset.card_image_of_injOn]
  intro x hx y hy hxy
  have h1 := (Finset.mem_filter.1 hx).2
  have h2 := (Finset.mem_filter.1 hy).2
  exact Prod.ext hxy (h1.trans h2.symm)

/-- The in-neighbours of a hub `h` in `MED(≺)`: the `u_i` with `i ≤ d`. -/
theorem image_fst_medOrient_in (rk : V → ℕ) {h : V} (hh : h ∈ K.hubs) :
    ((K.medOrient rk).filter (fun a => a.2 = h)).image Prod.fst =
      (K.beadNbrs h).filter (fun w => 2 * K.medPos rk h w ≤ (K.beadNbrs h).card) := by
  have hnp : h ∉ K.ports := K.not_mem_ports_of_mem_hubs hh
  ext w
  simp only [Finset.mem_image, Finset.mem_filter, mem_medOrient, mem_beadNbrs, medRule]
  constructor
  · rintro ⟨⟨x, y⟩, ⟨⟨hb, hr⟩, rfl⟩, rfl⟩
    simp only at hb hr ⊢
    refine ⟨⟨K.mem_verts_of_mem_beads hb (Sym2.mem_mk_left _ _), Sym2.eq_swap ▸ hb⟩, ?_⟩
    rcases hr with h1 | h1 | h1
    · exact h1.2.2
    · exact absurd h1.2.1 hnp
    · exact absurd h1.2.1 hnp
  · rintro ⟨⟨hwv, hb⟩, hpos⟩
    have hwp : w ∈ K.ports := K.mem_ports_of_mem_beadNbrs hh ((K.mem_beadNbrs).2 ⟨hwv, hb⟩)
    exact ⟨(w, h), ⟨⟨Sym2.eq_swap ▸ hb, Or.inl ⟨hwp, hh, hpos⟩⟩, rfl⟩, rfl⟩

/-- The out-neighbours of a hub `h` in `MED(≺)`: the `u_i` with `i > d`. -/
theorem image_snd_medOrient_out (rk : V → ℕ) {h : V} (hh : h ∈ K.hubs) :
    ((K.medOrient rk).filter (fun a => a.1 = h)).image Prod.snd =
      (K.beadNbrs h).filter (fun w => (K.beadNbrs h).card < 2 * K.medPos rk h w) := by
  have hnp : h ∉ K.ports := K.not_mem_ports_of_mem_hubs hh
  ext w
  simp only [Finset.mem_image, Finset.mem_filter, mem_medOrient, mem_beadNbrs, medRule]
  constructor
  · rintro ⟨⟨x, y⟩, ⟨⟨hb, hr⟩, rfl⟩, rfl⟩
    simp only at hb hr ⊢
    refine ⟨⟨K.mem_verts_of_mem_beads hb (Sym2.mem_mk_right _ _), hb⟩, ?_⟩
    rcases hr with h1 | h1 | h1
    · exact absurd h1.1 hnp
    · exact h1.2.2
    · exact absurd h1.1 hnp
  · rintro ⟨⟨hwv, hb⟩, hpos⟩
    have hwp : w ∈ K.ports := K.mem_ports_of_mem_beadNbrs hh ((K.mem_beadNbrs).2 ⟨hwv, hb⟩)
    exact ⟨(h, w), ⟨⟨hb, Or.inr (Or.inl ⟨hh, hwp, hpos⟩)⟩, rfl⟩, rfl⟩

/-- [s6:lemMED] (a) "Every hub of degree `2d` has exactly `d` in-arcs and `d` out-arcs." -/
theorem medOrient_inDeg {rk : V → ℕ} (hrk : Set.InjOn rk (K.ports : Set V)) {h : V}
    (hh : h ∈ K.hubs) : inDeg (K.medOrient rk) h = (K.beadNbrs h).card / 2 := by
  rw [inDeg_eq_card_image, K.image_fst_medOrient_in rk hh,
    K.card_filter_medPos hrk hh (fun i => 2 * i ≤ (K.beadNbrs h).card),
    card_Icc_filter_two_mul_le]

theorem medOrient_outDeg {rk : V → ℕ} (hrk : Set.InjOn rk (K.ports : Set V)) {h : V}
    (hh : h ∈ K.hubs) : outDeg (K.medOrient rk) h = (K.beadNbrs h).card - (K.beadNbrs h).card / 2 := by
  rw [outDeg_eq_card_image, K.image_snd_medOrient_out rk hh,
    K.card_filter_medPos hrk hh (fun i => (K.beadNbrs h).card < 2 * i)]
  set n := (K.beadNbrs h).card
  have : (Finset.Icc 1 n).filter (fun i => n < 2 * i) = Finset.Icc (n / 2 + 1) n := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  rw [this, Nat.card_Icc]
  omega

/-- [s6:defCluster] "Every bead is oriented exactly once: a bead at a hub has its other end at a
port, so it is oriented by the rule at that hub only." `MED(≺)` is an orientation of `B_𝒦`. -/
theorem medOrient_isOrientation {rk : V → ℕ} (hrk : Set.InjOn rk (K.ports : Set V)) :
    IsOrientation K.beads (K.medOrient rk) := by
  -- exactly one direction of every bead satisfies the rule
  have hrule : ∀ x y, s(x, y) ∈ K.beads → (K.medRule rk x y ↔ ¬ K.medRule rk y x) := by
    intro x y hb
    have hxy : x ≠ y := fun h => K.loopless _ hb (h ▸ Sym2.mk_isDiag_iff.2 rfl)
    have hx := K.ends_mem _ hb x (Sym2.mem_mk_left _ _)
    have hy := K.ends_mem _ hb y (Sym2.mem_mk_right _ _)
    have hd := K.disjoint
    unfold medRule
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact absurd (fun v hv => by rcases Sym2.mem_iff.1 hv with rfl | rfl <;> assumption)
        (K.no_hub_hub _ hb)
    · have hxp : x ∉ K.ports := Finset.disjoint_left.1 hd hx
      have hyh : y ∉ K.hubs := fun h' => Finset.disjoint_left.1 hd h' hy
      simp only [hx, hy, hxp, hyh, false_and, true_and, false_or, or_false, not_le]
    · have hyp : y ∉ K.ports := Finset.disjoint_left.1 hd hy
      have hxh : x ∉ K.hubs := fun h' => Finset.disjoint_left.1 hd h' hx
      simp only [hx, hy, hyp, hxh, false_and, true_and, false_or, or_false, not_lt]
    · have hxh : x ∉ K.hubs := fun h' => Finset.disjoint_left.1 hd h' hx
      have hyh : y ∉ K.hubs := fun h' => Finset.disjoint_left.1 hd h' hy
      have hne : rk x ≠ rk y := fun h => hxy (hrk (Finset.mem_coe.2 hx) (Finset.mem_coe.2 hy) h)
      simp only [hx, hy, hxh, hyh, false_and, true_and, false_or, not_lt]
      omega
  refine ⟨fun a ha => ?_, fun a ha => ((K.mem_medOrient).1 ha).1, fun e he => ?_⟩
  · have hb := ((K.mem_medOrient).1 ha).1
    intro h
    exact K.loopless _ hb (h ▸ Sym2.mk_isDiag_iff.2 rfl)
  · induction e using Sym2.ind with
    | h x y =>
      by_cases hr : K.medRule rk x y
      · refine ⟨(x, y), ⟨(K.mem_medOrient).2 ⟨he, hr⟩, rfl⟩, ?_⟩
        rintro ⟨x', y'⟩ ⟨ha', he'⟩
        simp only at he'
        rcases Sym2.eq_iff.1 he' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rfl
        · exact absurd ((K.mem_medOrient).1 ha').2 ((hrule y' x' he).1 hr)
      · have hr' : K.medRule rk y x := by
          by_contra h'
          exact hr ((hrule x y he).2 h')
        refine ⟨(y, x), ⟨(K.mem_medOrient).2 ⟨Sym2.eq_swap ▸ he, hr'⟩, Sym2.eq_swap⟩, ?_⟩
        rintro ⟨x', y'⟩ ⟨ha', he'⟩
        simp only at he'
        rcases Sym2.eq_iff.1 he' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact absurd ((K.mem_medOrient).1 ha').2 hr
        · rfl

/-- [s6:lemMED] (a) hub balance: `d⁺(h) = d⁻(h)` at every hub of a parity-clean cluster. -/
theorem medOrient_hub_bal (hK : K.ParityClean) {rk : V → ℕ}
    (hrk : Set.InjOn rk (K.ports : Set V)) (h : V) (hh : h ∈ K.hubs) :
    outDeg (K.medOrient rk) h = inDeg (K.medOrient rk) h := by
  rw [K.medOrient_outDeg hrk hh, K.medOrient_inDeg hrk hh]
  have := hK h hh
  rw [← K.card_beadNbrs] at this
  obtain ⟨r, hr⟩ := this
  omega

/-- The maximum `rk + 1` over the in-neighbours `u_1, …, u_d` of a hub (`0` if there is none);
it is `rk(u_d) + 1`. -/
@[expose] def medInMax (rk : V → ℕ) (h : V) : ℕ :=
  ((K.beadNbrs h).filter (fun w => 2 * K.medPos rk h w ≤ (K.beadNbrs h).card)).sup
    (fun w => rk w + 1)

/-- [s6:lemMED] (a) (proof) The potential: `pot(u) = (rk(u) + 1)/(M + 2)` on ports and
`pot(h) = (rk(u_d) + 1 + 1/2)/(M + 2)` on hubs, `M = max_{U_𝒦} rk`. -/
@[expose] noncomputable def medPot (rk : V → ℕ) (v : V) : ℝ :=
  if v ∈ K.ports then ((rk v : ℝ) + 1) / ((K.ports.sup rk : ℕ) + 2)
  else ((K.medInMax rk v : ℝ) + 1 / 2) / ((K.ports.sup rk : ℕ) + 2)

theorem medInMax_le (rk : V → ℕ) {h : V} (hh : h ∈ K.hubs) :
    K.medInMax rk h ≤ K.ports.sup rk + 1 := by
  unfold medInMax
  refine Finset.sup_le fun w hw => ?_
  have := Finset.le_sup (f := rk)
    (K.mem_ports_of_mem_beadNbrs hh (Finset.mem_filter.1 hw).1)
  omega

/-- [s6:lemMED] (a) "There is a function `pot : A_𝒦 ∪ U_𝒦 → (0,1)` that strictly increases along
every arc of `MED(≺)`." (Values in `(0,1)` on `V(𝒦)`; only the monotonicity of `medPos` is
needed for the arcs.) -/
theorem medPot_mem (rk : V → ℕ) {v : V} (hv : v ∈ K.verts) :
    0 < K.medPot rk v ∧ K.medPot rk v < 1 := by
  have hM : (0 : ℝ) < ((K.ports.sup rk : ℕ) : ℝ) + 2 := by positivity
  unfold medPot
  split_ifs with hp
  · refine ⟨by positivity, ?_⟩
    rw [div_lt_one hM]
    have := Finset.le_sup (f := rk) hp
    have : (rk v : ℝ) ≤ (K.ports.sup rk : ℕ) := by exact_mod_cast this
    linarith
  · have hh : v ∈ K.hubs := ((K.mem_verts).1 hv).resolve_right hp
    refine ⟨by positivity, ?_⟩
    rw [div_lt_one hM]
    have := K.medInMax_le rk hh
    have : (K.medInMax rk v : ℝ) ≤ (K.ports.sup rk : ℕ) + 1 := by exact_mod_cast this
    linarith

theorem medPot_lt (rk : V → ℕ) {a : V × V} (ha : a ∈ K.medOrient rk) :
    K.medPot rk a.1 < K.medPot rk a.2 := by
  obtain ⟨hb, hr⟩ := (K.mem_medOrient).1 ha
  have hM : (0 : ℝ) < ((K.ports.sup rk : ℕ) : ℝ) + 2 := by positivity
  unfold medPot
  rcases hr with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · -- `u_i → h`, `i ≤ d`: `rk(u_i) + 1 ≤ rk(u_d) + 1 < rk(u_d) + 1 + 1/2`
    have hnp : a.2 ∉ K.ports := K.not_mem_ports_of_mem_hubs h2
    rw [if_pos h1, if_neg hnp, div_lt_div_iff_of_pos_right hM]
    have hmem : a.1 ∈ (K.beadNbrs a.2).filter
        (fun w => 2 * K.medPos rk a.2 w ≤ (K.beadNbrs a.2).card) :=
      Finset.mem_filter.2 ⟨(K.mem_beadNbrs).2 ⟨K.mem_verts_of_mem_beads hb (Sym2.mem_mk_left _ _),
        Sym2.eq_swap ▸ hb⟩, h3⟩
    have := Finset.le_sup (f := fun w => rk w + 1) hmem
    have : (rk a.1 : ℝ) + 1 ≤ (K.medInMax rk a.2 : ℝ) := by
      unfold medInMax; exact_mod_cast this
    linarith
  · -- `h → u_i`, `i > d`: every in-neighbour has smaller rank than `u_i`
    have hnp : a.1 ∉ K.ports := K.not_mem_ports_of_mem_hubs h1
    rw [if_neg hnp, if_pos h2, div_lt_div_iff_of_pos_right hM]
    have hle : K.medInMax rk a.1 ≤ rk a.2 := by
      unfold medInMax
      refine Finset.sup_le fun w hw => ?_
      have hw2 := (Finset.mem_filter.1 hw).2
      by_contra hlt
      have := K.medPos_le_of_rk_le rk a.1 (w := a.2) (w' := w) (by omega)
      omega
    have : (K.medInMax rk a.1 : ℝ) ≤ rk a.2 := by exact_mod_cast hle
    linarith
  · rw [if_pos h1, if_pos h2, div_lt_div_iff_of_pos_right hM]
    have : (rk a.1 : ℝ) < rk a.2 := by exact_mod_cast h3
    linarith

/-- [s6:lemMED] (a) "`MED(≺)` is an admissible orientation." -/
theorem medOrient_isAdmissible (hK : K.ParityClean) {rk : V → ℕ}
    (hrk : Set.InjOn rk (K.ports : Set V)) : K.IsAdmissible (K.medOrient rk) where
  orient := K.medOrient_isOrientation hrk
  acyclic := isAcyclic_of_potential (K.medPot rk) fun _ ha => K.medPot_lt rk ha
  hub_bal := K.medOrient_hub_bal hK hrk

end Cluster

end EG.Chain
