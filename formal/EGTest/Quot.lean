import EG.Lib.Quot.Round
import EG.Lib.Quot.Constants
import EG.Lib.Quot.Xprime
import EG.Defs.Main.Gamma
import Mathlib.Tactic.IrreducibleDef

/-! Unit tests for the s7 quotient layer (`EG.Defs.Quot.*`, `EG.Defs.Main.Gamma`; design note
`work/p2d/quot.md`).

* **`RoundInput.Valid` is satisfiable and not `∅`-only**: `I1` has one `J^hub` edge `01` (hub `0`,
  port `1`, class `(1, [])`) with `M = 2^40`, `λ = 64`, and is valid; the item is paid in (a3)
  (its port is JV-bad), so nothing is live.
* **(J1) has content**: `I2` has two `J^hub` edges `01`, `02` at the hub `0` with ports of the
  same class; it is **not** valid.
* **Valid rules exist** for every valid input (`Rules.exists_valid`), in particular for `I1`.
* **The construction reads live items**: on the (invalid, `M = 1`) input `I3` (port not JV-bad,
  nothing pooled), the item `01` is live and is the hub item `(0, 1)`.
* Pairing lists, HUB lists, the `3`-subset law, and the parse of the constants.
* **A valid input with a live item** (`Live.I`, fix round 1, from the reviewer's non-vacuity
  scratch of quot.review1 §4): the star `1–w` (`w ∈ [2, 2^500)`) plus the edge `01` on `V = ℕ`,
  hub `0`, port `1` of class `(1, [])`, `Pool_l = [2, 2^500)`, `LJV = {1w}`, `M = 2^40`, `λ = 64`
  (`Hcd = 2^487 ≤ |Cand(1)|`; literal exponents are kept `≤ 256`, see `Live.N`). `Live.I_valid`,
  `Live.I_live : I.live = {01}`, and `Live.Q_nonempty`: for **every** valid rule and every `ξ`, the quotient has an edge (the chain
  (c) → (d) → (e1) → (g) works end to end); `Live.chosen_Q_nonempty` for the chosen rules.
* `ofPast_multAt`, `roundOut` (the type of `JConsumer.out`), `roundQuotient` (parse checks).
* **The PAR path and the rank split** (`Par`, fix round 2, from the reviewer's scratch of
  quot.review2 §4): two parallel `J^par` items with the same junction pair `{4, 5}`; for every valid
  rule and every `ξ`: (b) colour `0`, (e2) junctions via `inOrder`, (e3) not looped, (g) ranks
  `(1, 2)` / `(2, 1)` and `|E(Q_l)| = 2`, `|V(Q_l)| = 4`, (h) the two `Q`-edges lift to the two
  items. -/

namespace EGTest.Quot

open EG EG.Quot

/-- The graph on `Fin 3` with the edges `01` and `02`. -/
def G3 : FGraph (Fin 3) where
  verts := Finset.univ
  edges := {s(0, 1), s(0, 2)}
  edge_verts _ _ _ _ := Finset.mem_univ _
  loopless e he := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl <;> decide

/-- One `J^hub` edge `01`; its port `1` is JV-bad. -/
def I1 : RoundInput (Fin 3) where
  G := G3
  l := 3
  M := 2 ^ 40
  lam := 64
  ancs := {(1, [])}
  ancVerts _ := {1, 2}
  ljv _ := ∅
  lendGood _ := True
  pool := ∅
  poolRound _ := 0
  hubs := {0}
  fresh := ∅
  ports := {1}
  lost := ∅
  cls _ := (1, [])
  jvBad _ := True
  Jlost := ∅
  Jhub := {s(0, 1)}
  Jfr := ∅
  Jpar := ∅

theorem I1_J : I1.J = {s(0, 1)} := by decide

/-- `Finset.card_filter_le` with the decidability instance taken by unification (the instance in
`RoundInput.Valid` is the generic one, not the `Fin`-specific one found by synthesis). -/
theorem card_filter_le' {α : Type*} (s : Finset α) (p : α → Prop) {_ : DecidablePred p} :
    (s.filter p).card ≤ s.card := Finset.card_filter_le _ _

/-- `Finset.mem_filter` (introduction) with the instance taken by unification. -/
theorem mem_filter_of {α : Type*} {s : Finset α} {p : α → Prop} {_ : DecidablePred p} {a : α}
    (h1 : a ∈ s) (h2 : p a) : a ∈ s.filter p := Finset.mem_filter.2 ⟨h1, h2⟩

theorem degE_le_card (F : Finset (Sym2 (Fin 3))) (v : Fin 3) : degE F v ≤ F.card := by
  unfold degE edgesAt
  exact Finset.card_filter_le _ _

theorem I1_valid : I1.Valid where
  M_ge := le_refl _
  Hcd_ge := by
    simp only [RoundInput.Hcd, HcdOf, I1]
    norm_num
  roles := by decide
  hub_typed e he := by
    simp only [I1, Finset.mem_singleton] at he
    exact ⟨0, by simp [I1], 1, by simp [I1], he⟩
  fr_typed e he := by simp [I1] at he
  par_typed e he := by simp [I1] at he
  lost_typed e he := by simp [I1] at he
  J_sub := by rw [I1_J]; decide
  J1 h Y := le_trans (card_filter_le' _ _) (le_of_eq (Finset.card_singleton _))
  J2 v _ := le_trans (degE_le_card _ v) (by rw [I1_J]; simp [I1])
  J2tot := by rw [I1_J]; simp [I1, G3, FGraph.card]
  cls_anc u _ := by simp [I1]
  cls_round u _ := by simp [I1]
  cls_mem u hu := by simp [I1] at hu ⊢; simp [hu]
  ljv_in _ _ e he := by simp [I1] at he
  ljv_disj _ _ _ _ _ := Finset.disjoint_empty_left _
  ljv_J _ _ := Finset.disjoint_empty_left _
  lendGood_ports _ _ := trivial
  good_cand _ _ h := (h trivial).elim
  pool_sub := Finset.empty_subset _
  ports_sub := Finset.subset_univ _

/-- The item `01` is paid in (a3): its port `1` is JV-bad. -/
theorem I1_paidJVBad : I1.paidJVBad = {s(0, 1)} := by
  classical
  ext e
  simp only [RoundInput.paidJVBad, RoundInput.items, Finset.mem_filter, Finset.mem_sdiff,
    Finset.mem_singleton, I1_J]
  constructor
  · rintro ⟨⟨h, -⟩, -⟩
    exact h
  · rintro rfl
    exact ⟨⟨rfl, by simp [I1]⟩, 1, Sym2.mem_mk_right _ _, by simp [I1], trivial⟩

theorem I1_live : I1.live = ∅ := by
  classical
  ext e
  simp only [RoundInput.live, Finset.mem_sdiff, Finset.mem_union, I1_paidJVBad,
    Finset.notMem_empty, iff_false, not_and, not_or, not_not]
  intro he _
  simp only [RoundInput.items, Finset.mem_sdiff, I1_J, Finset.mem_singleton] at he
  simpa using he.1

/-- Valid fixed rules exist for `I1`. -/
example : ∃ R : Rules I1, R.Valid := Rules.exists_valid I1_valid

/-- Two `J^hub` edges of the same class at the hub `0`: (J1) fails. -/
def I2 : RoundInput (Fin 3) :=
  { I1 with ports := {1, 2}, Jhub := {s(0, 1), s(0, 2)} }

theorem I2_not_valid : ¬ I2.Valid := by
  intro h
  obtain ⟨S, hS, hcard⟩ : ∃ S : Finset (Sym2 (Fin 3)), S = _ ∧ S.card ≤ 1 :=
    ⟨_, rfl, h.J1 0 (1, [])⟩
  have hsub : ({s(0, 1), s(0, 2)} : Finset (Sym2 (Fin 3))) ⊆ S := by
    subst hS
    intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl
    · exact mem_filter_of (by simp [I2]) ⟨1, by simp [I2], rfl, rfl⟩
    · exact mem_filter_of (by simp [I2]) ⟨2, by simp [I2], rfl, rfl⟩
  have h2 := Finset.card_le_card hsub
  have h3 : ({s(0, 1), s(0, 2)} : Finset (Sym2 (Fin 3))).card = 2 := by decide
  omega

/-- An invalid input (`M = 1`) whose port is JV-good and nothing is pooled: the item `01` is live
and is the hub item `(0, 1)`. -/
def I3 : RoundInput (Fin 3) := { I1 with M := 1, jvBad _ := False }

theorem I3_live : I3.live = {s(0, 1)} := by
  classical
  have hJ : I3.J = {s(0, 1)} := by decide
  ext e
  simp only [RoundInput.live, RoundInput.paidPool, RoundInput.paidJVBad, RoundInput.items,
    Finset.mem_sdiff, Finset.mem_union, Finset.mem_filter, hJ, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨h, -⟩, -⟩
    exact h
  · rintro rfl
    refine ⟨⟨rfl, by simp [I3, I1]⟩, ?_⟩
    simp [I3, I1]

theorem I3_hubItems : I3.hubItems = {(0, 1)} := by
  classical
  ext p
  rw [RoundInput.mem_hubItems, I3_live]
  rcases p with ⟨a, b⟩
  simp only [I3, I1, Finset.mem_singleton, Prod.mk.injEq]
  constructor
  · rintro ⟨rfl, rfl, -, -⟩
    exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨rfl, rfl, rfl, rfl⟩

theorem I3_clive : I3.clive 0 = 1 := by
  rw [RoundInput.clive, I3_hubItems]
  decide

/-! ## Pairing lists and HUB lists -/

example : pairUp [1, 2, 3, 4, 5] = [(1, 2), (3, 4)] := rfl
example : leftover [1, 2, 3, 4, 5] = some 5 := rfl
example : leftover [1, 2, 3, 4] = none := rfl

/-- Group `2` (0-based) of the identity permutation of `[12]` receives `{6, 7, 8}`. -/
example : listOf (1 : Equiv.Perm (Fin 12)) 2 = {6, 7, 8} := by decide

example : (listOf (1 : Equiv.Perm (Fin 12)) 2).card = 3 := card_listOf _ (by norm_num)

example : Disjoint (listOf (1 : Equiv.Perm (Fin 12)) 0) (listOf (1 : Equiv.Perm (Fin 12)) 3) :=
  disjoint_listOf _ (by norm_num)

/-- The law of `ζ` gives only `3`-subsets. -/
example (s : Finset (Fin 8)) (hs : s ∈ (subset3Law 8).supp) : s.card = 3 :=
  card_of_mem_supp_subset3Law (by norm_num) hs

/-! ## Constants (parse checks) -/

example (D : ℝ) : Quot.C0 D = D / 2 + 1085 + Quot.eps1 D := rfl
example (D : ℝ) : Quot.eps2 D = 12 * Quot.epsX D +
    4 * (3 * HB.epsA D + 60 / D + 2 * Quot.FQ (Real.logb 2 D)) := rfl
example (D : ℝ) : Gamma4 D ↔ Quot.eps1 D ≤ 6 ∧ Quot.thetaQ D ≤ 1 / 4 := Iff.rfl
example (N0 D : ℝ) : cEG N0 D = max (Quot.C0 D / (1 - 2 * Quot.eps2 D)) (N0 / 2) := rfl
example (x : ℝ) : Quot.FQ x = (3184 + 30400 * Real.logb 2 x) * x ^ (-(90.2 : ℝ)) := rfl
example : Quot.tCC 4 = 4 := by
  simp only [Quot.tCC]
  have : Real.logb 2 (4 : ℕ) = 2 := by
    rw [show ((4 : ℕ) : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.logb_pow]; simp
  rw [this]; norm_num

/-! ## The run-level J-consumer (parse checks) -/

section consumer

variable {V : Type} [DecidableEq V] (run : HB.Run V) (G : FGraph V) (δ : Chain.Designation V)
  (S : Chain.StageData V) (π : ↥G.verts → Option (ℕ × ℕ))

noncomputable example : ℕ → Finset (Sym2 V) → List (Obj V) × Finset (Sym2 V) :=
  roundOut run G δ S π
noncomputable example (l : ℕ) (J : Finset (Sym2 V)) : FGraph (QVert V) :=
  roundQuotient run G δ S π l J
example (l r : ℕ) (J : Finset (Sym2 V)) (w : V) :
    (RoundInput.ofPast run G δ S π l J).multAt r w = run.mult G r w :=
  ofPast_multAt run G δ S π l J r w

end consumer

/-! ## A valid input with a live item (fix round 1; reviewer scratch of quot.review1 §4) -/

namespace Live

open EG EG.Quot

noncomputable section

-- `N = 2^500` must stay irreducible: a reducible `N` makes `simp`/kernel reduction of
-- `Finset.Ico 2 N` blow up (> 9 GB, reviewer's note, quot.review1 §4). Every literal exponent is
-- kept `≤ 256` (the default `exponentiation.threshold`; the option is not on the lint allowlist):
-- `N = (2^250)^2` and `Hcd = 64^95/(8 (2^40)^2)` (`= 2^487`).
irreducible_def N : ℕ := (2 ^ 250) ^ 2

/-- `Hcd = λ^95/(8M^2)` for `λ = 64`, `M = 2^40` (this is `2^487`). -/
noncomputable def Hval : ℝ := 64 ^ 95 / (8 * (2 ^ 40) ^ 2)

theorem two_lt_N : 2 < N := by rw [N_def]; norm_num

theorem N_big : Hval ≤ ((N - 2 : ℕ) : ℝ) := by
  rw [N_def, Nat.cast_sub (by norm_num), Hval]; norm_num

/-- The star `1–w` (`w ∈ [2, N)`) plus the edge `01`, on `range N`. -/
def G : FGraph ℕ where
  verts := Finset.range N
  edges := insert s(0, 1) ((Finset.Ico 2 N).image (fun w => s(1, w)))
  edge_verts e he v hv := by
    simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_Ico] at he
    simp only [Finset.mem_range]
    have := two_lt_N
    rcases he with rfl | ⟨w, ⟨hw1, hw2⟩, rfl⟩
    · rcases Sym2.mem_iff.1 hv with rfl | rfl <;> omega
    · rcases Sym2.mem_iff.1 hv with rfl | rfl
      · omega
      · exact hw2
  loopless e he := by
    simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_Ico] at he
    rcases he with rfl | ⟨w, ⟨hw1, hw2⟩, rfl⟩
    · simp
    · simp only [Sym2.mk_isDiag_iff]; omega

/-- Hub `0`, port `1` of class `(1, [])`, `Pool_l = [2, N)`, `LJV = {1w}`, `J^hub = {01}`. -/
def I : RoundInput ℕ where
  G := G
  l := 3
  M := 2 ^ 40
  lam := 64
  ancs := {(1, [])}
  ancVerts _ := Finset.range N
  ljv _ := (Finset.Ico 2 N).image (fun w => s(1, w))
  lendGood _ := True
  pool := Finset.Ico 2 N
  poolRound _ := 1
  hubs := {0}
  fresh := ∅
  ports := {1}
  lost := ∅
  cls _ := (1, [])
  jvBad _ := False
  Jlost := ∅
  Jhub := {s(0, 1)}
  Jfr := ∅
  Jpar := ∅

theorem I_J : I.J = {s(0, 1)} := by
  simp [RoundInput.J, I]

theorem I_cand : I.cand 1 = Finset.Ico 2 N := by
  ext w
  rw [RoundInput.cand, Finset.mem_filter]
  change w ∈ Finset.Ico 2 N ∧ 1 = 1 ∧ s(1, w) ∈ (Finset.Ico 2 N).image (fun w => s(1, w)) ↔ _
  constructor
  · rintro ⟨h, -⟩; exact h
  · intro h; exact ⟨h, rfl, Finset.mem_image.2 ⟨w, h, rfl⟩⟩

theorem I_Hcd : I.Hcd = Hval := by
  simp only [RoundInput.Hcd, HcdOf, I, Hval]; norm_num

theorem I_valid : I.Valid where
  M_ge := le_refl _
  Hcd_ge := by rw [I_Hcd, Hval]; simp only [I]; norm_num
  roles := by simp [I]
  hub_typed e he := by
    simp only [I, Finset.mem_singleton] at he
    exact ⟨0, by simp [I], 1, by simp [I], he⟩
  fr_typed e he := by simp [I] at he
  par_typed e he := by simp [I] at he
  lost_typed e he := by simp [I] at he
  J_sub := by rw [I_J]; simp [I, G]
  J1 h Y := by
    classical
    refine le_trans (Finset.card_filter_le _ _) ?_
    simp [I]
  J2 v _ := by
    rw [I_J]
    refine le_trans (Finset.card_filter_le _ _) ?_
    simp [I]
  J2tot := by
    rw [I_J]; simp only [I, G, FGraph.card, Finset.card_range, Finset.card_singleton]
    have := two_lt_N; exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by norm_num))
  cls_anc u _ := by simp [I]
  cls_round u _ := by simp [I]
  cls_mem u hu := by simp [I] at hu ⊢; subst hu; have := two_lt_N; omega
  ljv_in Y _ e he := by
    simp only [I, Finset.mem_image, Finset.mem_Ico] at he
    obtain ⟨w, ⟨hw1, hw2⟩, rfl⟩ := he
    refine ⟨Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨w, Finset.mem_Ico.2 ⟨hw1, hw2⟩, rfl⟩), ?_⟩
    intro v hv
    change v ∈ Finset.range N
    rw [Finset.mem_range]
    rcases Sym2.mem_iff.1 hv with rfl | rfl
    · have := two_lt_N; omega
    · exact hw2
  ljv_disj Y hY Y' hY' hne := by simp [I] at hY hY'; exact absurd (hY.trans hY'.symm) hne
  ljv_J Y _ := by
    rw [I_J]
    simp only [I, Finset.disjoint_singleton_right, Finset.mem_image, Finset.mem_Ico, not_exists,
      not_and]
    intro w hw h
    rcases Sym2.eq_iff.1 h with ⟨h1, -⟩ | ⟨-, h2⟩ <;> omega
  lendGood_ports _ _ := trivial
  good_cand u hu _ := by
    simp [I] at hu; subst hu
    rw [I_cand, I_Hcd, Nat.card_Ico]; exact N_big
  pool_sub := by intro w hw; simp only [I, G, Finset.mem_Ico, Finset.mem_range] at hw ⊢; omega
  ports_sub := by
    intro w hw; simp only [I, G, Finset.mem_singleton, Finset.mem_range] at hw ⊢; have := two_lt_N; omega

/-- The item `01` is live. -/
theorem I_live : I.live = {s(0, 1)} := by
  classical
  ext e
  simp only [RoundInput.live, RoundInput.paidPool, RoundInput.paidJVBad, RoundInput.items,
    Finset.mem_sdiff, Finset.mem_union, Finset.mem_filter, I_J, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨h, -⟩, -⟩; exact h
  · rintro rfl
    refine ⟨⟨rfl, by simp [I]⟩, ?_⟩
    simp [I]

theorem I_hubItems : I.hubItems = {(0, 1)} := by
  classical
  ext p
  rw [RoundInput.mem_hubItems, I_live]
  rcases p with ⟨a, b⟩
  simp only [I, Finset.mem_singleton, Prod.mk.injEq]
  constructor
  · rintro ⟨rfl, rfl, -, -⟩; exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩; exact ⟨rfl, rfl, rfl, rfl⟩


theorem I_clive : I.clive 0 = 1 := by
  rw [RoundInput.clive, I_hubItems]; decide

theorem I_not_ultra : ¬ I.ultra 0 := by
  rw [RoundInput.ultra_iff, I_clive, not_lt, RoundInput.thult, thultOf, I_Hcd]
  change 1 ≤ ⌊((2 ^ 40 : ℕ) : ℝ) * Hval / 7⌋₊
  rw [Nat.one_le_floor_iff, Hval]; norm_num

theorem I_kh : I.kh 0 = 1 := by
  simp only [RoundInput.kh, I_clive, I_Hcd]
  rw [Nat.ceil_eq_iff (by norm_num), Hval]; norm_num

theorem I_hubItemsAt : I.hubItemsAt 1 = {(0, 1)} := by
  ext p; rw [RoundInput.mem_hubItemsAt, I_hubItems]; simp only [Finset.mem_singleton]
  constructor
  · rintro ⟨h, -⟩; exact h
  · rintro rfl; exact ⟨rfl, rfl⟩

theorem zero_mem : (0 : ℕ) ∈ I.G.verts := by
  simp only [I, G, Finset.mem_range]; have := two_lt_N; omega

/-- For EVERY valid rule and EVERY `ξ`, the quotient of this valid input has an edge. -/
theorem Q_nonempty (R : Rules I) (hR : R.Valid) (ξ : Xi I.G I.M) : (R.Q ξ).edges.Nonempty := by
  classical
  -- the group of (0,1) is 0
  have hg : R.group (0, 1) = 0 := by
    have := (hR.group 0 I_not_ultra).1 (0, 1) (by rw [I_hubItems]; simp) rfl
    rw [I_kh] at this; omega
  have hlist : R.hubList ξ.1 (0, 1) = listOf (etaAt ξ.1 0) 0 := by
    simp only [Rules.hubList, if_neg I_not_ultra, hg]
  have h4M : 3 ≤ 4 * I.M := by simp only [I]; norm_num
  have hne : (listOf (etaAt ξ.1 0) 0).Nonempty := by
    rw [← Finset.card_pos, card_listOf _ (by simpa using h4M)]; norm_num
  obtain ⟨c, hc⟩ := hne
  have hSDR : R.SDRExists ξ.1 1 := by
    refine ⟨fun _ => c, ?_, ?_⟩
    · intro it hit; rw [I_hubItemsAt, Finset.mem_singleton] at hit; subst hit; rw [hlist]; exact hc
    · intro a ha b hb _
      rw [I_hubItemsAt, Finset.coe_singleton] at ha hb; rw [ha, hb]
  have hcol : R.colouredHub ξ.1 = {(0, 1)} := by
    ext it; simp only [Rules.colouredHub, Finset.mem_filter, I_hubItems, Finset.mem_singleton]
    constructor
    · rintro ⟨h, -⟩; exact h
    · rintro rfl; exact ⟨rfl, hSDR⟩
  have hhc : R.hubColour ξ.1 (0, 1) = some (R.sdr ξ.1 (0, 1)) := by
    simp only [Rules.hubColour, I_hubItems, Finset.mem_singleton, true_and]
    rw [if_pos hSDR]
  have he1i : R.e1Items ξ.1 = {(0, 1)} := by
    ext it; simp only [Rules.e1Items, hcol, Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨h, -⟩; exact h
    · rintro rfl; exact ⟨rfl, I_not_ultra⟩
  have he1o : R.e1Order ξ.1 = [(0, 1)] := by
    obtain ⟨hnd, hfs⟩ := hR.e1Order ξ.1
    rw [he1i] at hfs
    have hperm : (R.e1Order ξ.1).Perm [(0, 1)] :=
      (List.perm_ext_iff_of_nodup hnd (List.nodup_singleton _)).2 (fun a => by
        rw [← List.mem_toFinset, hfs]; simp)
    exact List.perm_singleton.1 hperm
  -- the (e1) search succeeds
  have hfind : ((R.vertOrder ξ.1).find? (fun w => decide (w ∈ Rules.e1Free I
      ⟨fun _ => ∅, fun _ _ => ∅, fun _ => none⟩ (0, 1) (R.sdr ξ.1 (0, 1))))).isSome := by
    rw [List.find?_isSome]
    refine ⟨2, ?_, ?_⟩
    · rw [← List.mem_toFinset, (hR.vertOrder ξ.1).2]; simp only [I, G, Finset.mem_range]; exact two_lt_N
    · simp only [Rules.e1Free, I_cand, decide_eq_true_eq, Finset.sdiff_empty, Finset.mem_Ico]; exact ⟨le_refl _, two_lt_N⟩
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 hfind
  have hjunc : R.junction ξ (.hub 0 1) = some w := by
    simp only [Rules.junction, Rules.e1State, he1o, List.foldl_cons,
      List.foldl_nil, Rules.e1Step, hhc, if_neg I_not_ultra, hw]
    simp
  refine ⟨s((hubTag (R.sdr ξ.1 (0, 1)) (R.rank ξ (Sum.inr (0, 1))) true, 0),
      (hubTag (R.sdr ξ.1 (0, 1)) (R.rank ξ (Sum.inr (0, 1))) false, w)),
    Finset.mem_biUnion.2 ⟨Sum.inr (0, 1), ?_, ?_⟩⟩
  · simp [Rules.layerEdges, hcol]
  · simp only [Rules.qEdge, hhc, hjunc]; simp

/-- The chosen rules of this valid input are valid, and its quotient has an edge. -/
theorem chosen_Q_nonempty : I.chosenRules.quotient.edges.Nonempty :=
  Q_nonempty _ (RoundInput.chosenRules_valid I_valid) _

end

end Live

/-! ## The PAR path and the rank split (fix round 2, r2-3; from the reviewer's scratch of
quot.review2 §4)

Input `Par.I` on `V = ℕ`: ports `0, 1, 2, 3`, pooled vertices `4, 5`, two live `J^par` items `02`,
`13`; every port has exactly one candidate (`cand 0 = cand 1 = {4}`, `cand 2 = cand 3 = {5}`), no
hubs, no fresh centres, `M = 1`, `λ = 2` (the input is not `RoundInput.Valid`; the construction and
`Rules.Valid` do not need it, and `Rules.std_valid` applies since `Hcd > 0`). For **every** valid
rule `R` and **every** `ξ`: both PAR objects get colour `0` ((b) first fit, `parColour_eq`), every
end gets its junction through `inOrder` ((e2), `junction_o₁/₂`), neither object is looped ((e3)),
the two layer edges have the same rank-`0` `Q`-edge `[4][5]` and are split by rank into `(1, 2)` or
`(2, 1)` ((g), `rank_eq`), `|E(Q_l)| = 2`, `|V(Q_l)| = 4`, and the two single edges of `Q_l` lift to
the two `J^par` items ((h), `layerOf_E`, `lift_edges`). -/

namespace Par

open EG EG.Quot


open EG EG.Quot

def G : FGraph ℕ where
  verts := Finset.range 6
  edges := {s(0, 2), s(1, 3), s(0, 4), s(1, 4), s(2, 5), s(3, 5)}
  edge_verts e he v hv := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    simp only [Finset.mem_range]
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases Sym2.mem_iff.1 hv with rfl | rfl <;> omega
  loopless e he := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

def I : RoundInput ℕ where
  G := G
  l := 3
  M := 1
  lam := 2
  ancs := {(1, [])}
  ancVerts _ := Finset.range 6
  ljv _ := {s(0, 4), s(1, 4), s(2, 5), s(3, 5)}
  lendGood _ := True
  pool := {4, 5}
  poolRound _ := 1
  hubs := ∅
  fresh := ∅
  ports := {0, 1, 2, 3}
  lost := ∅
  cls _ := (1, [])
  jvBad _ := False
  Jlost := ∅
  Jhub := ∅
  Jfr := ∅
  Jpar := {s(0, 2), s(1, 3)}

theorem I_J : I.J = {s(0, 2), s(1, 3)} := by simp [RoundInput.J, I]

theorem I_items : I.items = {s(0, 2), s(1, 3)} := by
  rw [RoundInput.items, I_J]; simp [I]

theorem I_live : I.live = {s(0, 2), s(1, 3)} := by
  classical
  ext e
  simp only [RoundInput.live, RoundInput.paidPool, RoundInput.paidJVBad, I_items,
    Finset.mem_sdiff, Finset.mem_union, Finset.mem_filter]
  constructor
  · rintro ⟨h, -⟩; exact h
  · intro h
    refine ⟨h, ?_⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    simp only [I, Finset.mem_insert, Finset.mem_singleton, not_or, not_and, not_exists, and_false,
      exists_false, or_false]
    rcases h with rfl | rfl <;> simp

theorem I_hubItems : I.hubItems = ∅ := by
  simp [RoundInput.hubItems, I]

theorem I_parItems : I.parItems = {s(0, 2), s(1, 3)} := by
  ext e
  rw [RoundInput.mem_parItems, I_live]
  simp only [I, Finset.mem_insert, Finset.mem_singleton]
  tauto

/-- The candidate of a port: `4` for `0, 1` and `5` for `2, 3`. -/
def jn (p : ℕ) : ℕ := if p < 2 then 4 else 5

theorem I_cand {p : ℕ} (hp : p ∈ ({0, 1, 2, 3} : Finset ℕ)) : I.cand p = {jn p} := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  ext w
  rw [RoundInput.cand, Finset.mem_filter]
  rcases hp with rfl | rfl | rfl | rfl <;> simp [I, jn] <;> omega

theorem I_Hcd_pos : 0 < I.Hcd := by
  simp only [RoundInput.Hcd, HcdOf, I]; positivity

theorem zero_lt_verts_card : ∀ p, p < 6 → p ∈ I.G.verts := by
  intro p hp; simp [I, G, hp]


/-! ## The two PAR objects -/

/-- The PAR object of the item `02` (ends `(Quot.out s(0,2))`, orientation unknown). -/
noncomputable abbrev o₁ : ParObj ℕ :=
  ParObj.par (_root_.Quot.out s(0, 2)).1 (_root_.Quot.out s(0, 2)).2
noncomputable abbrev o₂ : ParObj ℕ :=
  ParObj.par (_root_.Quot.out s(1, 3)).1 (_root_.Quot.out s(1, 3)).2

theorem out_spec (e : Sym2 ℕ) : s((_root_.Quot.out e).1, (_root_.Quot.out e).2) = e := by
  have := Quot.out_eq e
  exact this

theorem o₁_ends : ((_root_.Quot.out s(0, 2)).1 = 0 ∧ (_root_.Quot.out s(0, 2)).2 = 2) ∨
    ((_root_.Quot.out s(0, 2)).1 = 2 ∧ (_root_.Quot.out s(0, 2)).2 = 0) :=
  Sym2.eq_iff.1 (out_spec s(0, 2))

theorem o₂_ends : ((_root_.Quot.out s(1, 3)).1 = 1 ∧ (_root_.Quot.out s(1, 3)).2 = 3) ∨
    ((_root_.Quot.out s(1, 3)).1 = 3 ∧ (_root_.Quot.out s(1, 3)).2 = 1) :=
  Sym2.eq_iff.1 (out_spec s(1, 3))

theorem endAt_o₁_mem (b : Bool) : o₁.endAt b ∈ ({0, 2} : Finset ℕ) := by
  rcases o₁_ends with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> cases b <;> simp [ParObj.endAt, h1, h2]

theorem endAt_o₂_mem (b : Bool) : o₂.endAt b ∈ ({1, 3} : Finset ℕ) := by
  rcases o₂_ends with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> cases b <;> simp [ParObj.endAt, h1, h2]

theorem endAt_o₁_inj {b b' : Bool} (h : o₁.endAt b = o₁.endAt b') : b = b' := by
  rcases o₁_ends with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> cases b <;> cases b' <;>
    simp [ParObj.endAt, h1, h2] at h ⊢

theorem endAt_o₂_inj {b b' : Bool} (h : o₂.endAt b = o₂.endAt b') : b = b' := by
  rcases o₂_ends with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> cases b <;> cases b' <;>
    simp [ParObj.endAt, h1, h2] at h ⊢

theorem endAt_o₁_ne_o₂ (b b' : Bool) : o₁.endAt b ≠ o₂.endAt b' := by
  have h1 := endAt_o₁_mem b
  have h2 := endAt_o₂_mem b'
  simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2
  omega

theorem o₁_ne_o₂ : o₁ ≠ o₂ := by
  intro h
  have := endAt_o₁_ne_o₂ false false
  rw [h] at this
  exact this rfl

theorem endAt_o₁_port (b : Bool) : o₁.endAt b ∈ ({0, 1, 2, 3} : Finset ℕ) := by
  have := endAt_o₁_mem b; simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢; omega

theorem endAt_o₂_port (b : Bool) : o₂.endAt b ∈ ({0, 1, 2, 3} : Finset ℕ) := by
  have := endAt_o₂_mem b; simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢; omega

theorem not_conflict : ¬ ParObj.Conflict o₁ o₂ ∧ ¬ ParObj.Conflict o₂ o₁ := by
  constructor
  · rintro (⟨b, b', h⟩ | ⟨x, hx, -⟩)
    · exact endAt_o₁_ne_o₂ b b' h
    · simp [ParObj.middle] at hx
  · rintro (⟨b, b', h⟩ | ⟨x, hx, -⟩)
    · exact endAt_o₁_ne_o₂ b' b h.symm
    · simp [ParObj.middle] at hx

/-- The junction pair of `o₁` is `{4, 5}`, and of `o₂` too. -/
theorem jn_o₁ (t : QTag) :
    jn (o₁.endAt false) ≠ jn (o₁.endAt true) ∧
    s((t, jn (o₁.endAt false)), (t, jn (o₁.endAt true))) = s((t, 4), (t, 5)) := by
  rcases o₁_ends with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [ParObj.endAt, h1, h2, jn, Sym2.eq_swap]

theorem jn_o₂ (t : QTag) :
    jn (o₂.endAt false) ≠ jn (o₂.endAt true) ∧
    s((t, jn (o₂.endAt false)), (t, jn (o₂.endAt true))) = s((t, 4), (t, 5)) := by
  rcases o₂_ends with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [ParObj.endAt, h1, h2, jn, Sym2.eq_swap]

/-- A Nodup list whose set is a pair is one of the two orderings. -/
theorem list_of_pair {α : Type*} [DecidableEq α] {l : List α} {a b : α} (hab : a ≠ b)
    (hnd : l.Nodup) (hl : l.toFinset = {a, b}) : l = [a, b] ∨ l = [b, a] := by
  have hperm : l.Perm [a, b] :=
    (List.perm_ext_iff_of_nodup hnd (by simp [hab])).2 (fun x => by
      rw [← List.mem_toFinset, hl]; simp)
  have hlen : l.length = 2 := by simpa using hperm.length_eq
  obtain ⟨x, y, rfl⟩ := List.length_eq_two.1 hlen
  have hx : x ∈ [a, b] := hperm.subset (by simp)
  have hy : y ∈ [a, b] := hperm.subset (by simp)
  have hxy : x ≠ y := by simpa using hnd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · exact absurd rfl hxy
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact absurd rfl hxy

theorem range_three : List.range (3 * I.M) = [0, 1, 2] := rfl

theorem list_singleton_of {α : Type*} [DecidableEq α] {l : List α} {a : α} (hnd : l.Nodup)
    (hl : l.toFinset = {a}) : l = [a] := by
  classical
  have hperm : l.Perm [a] :=
    (List.perm_ext_iff_of_nodup hnd (List.nodup_singleton _)).2 (fun x => by
      rw [← List.mem_toFinset, hl]; simp)
  exact List.perm_singleton.1 hperm

/-- The order list of a one-element candidate set at a port is that element. -/
theorem inOrder_single (O : Orders I.G) {p : ℕ} (hp : p ∈ ({0, 1, 2, 3} : Finset ℕ)) :
    inOrder O p {jn p} = [jn p] := by
  have hpv : p ∈ I.G.verts := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    apply zero_lt_verts_card; omega
  have hjv : ({jn p} : Finset ℕ) ⊆ I.G.verts := by
    intro w hw; simp only [Finset.mem_singleton] at hw; subst hw
    apply zero_lt_verts_card; unfold jn; split_ifs <;> omega
  have hlen := length_inOrder (O := O) hpv hjv
  rw [Finset.card_singleton] at hlen
  obtain ⟨x, hx⟩ := List.length_eq_one_iff.1 hlen
  have hmem : jn p ∈ inOrder O p {jn p} := (mem_inOrder hpv _ _).2 ⟨by simp, hjv (by simp)⟩
  rw [hx] at hmem ⊢
  simp only [List.mem_singleton] at hmem
  rw [hmem]

/-- The edge `[4][5]` of the PAR sub-layer `(0, ι)`. -/
def E (ι : ℕ) : Sym2 (QVert ℕ) := s((parTag 0 ι, 4), (parTag 0 ι, 5))

theorem inl_ne : (Sum.inl o₁ : LayerEdge ℕ) ≠ Sum.inl o₂ := by
  intro h; exact o₁_ne_o₂ (Sum.inl.inj h)

theorem E_ne : E 1 ≠ E 2 := by
  simp [E, parTag]


section rules

variable (R : Rules I) (hR : R.Valid)
include hR

omit hR in
theorem parObjs_eq : R.parObjs = {o₁, o₂} := by
  unfold Rules.parObjs Rules.parObjsPar
  rw [I_parItems]
  simp [Rules.cherries, I]

theorem parOrder_eq : R.parOrder = [o₁, o₂] ∨ R.parOrder = [o₂, o₁] :=
  list_of_pair o₁_ne_o₂ hR.parOrder.1 (hR.parOrder.2.trans (parObjs_eq R))

omit hR in
/-- One greedy step on a fresh object with no coloured conflicting neighbour gives colour `0`. -/
theorem colourStep_zero (col : ParObj ℕ → Option ℕ) (o : ParObj ℕ)
    (h : ∀ o' ∈ R.parObjs, o' ≠ o → ParObj.Conflict o o' → col o' ≠ some 0) :
    R.colourStep col o = Function.update col o (some 0) := by
  unfold Rules.colourStep
  rw [range_three, List.find?_cons_of_pos]
  simpa using h

theorem parColour_eq : R.parColour o₁ = some 0 ∧ R.parColour o₂ = some 0 := by
  have hpo := parObjs_eq R
  have hc := not_conflict
  have step2 : ∀ x y : ParObj ℕ, x ≠ y → ¬ ParObj.Conflict y x →
      R.colourStep (Function.update (fun _ => none) x (some 0)) y =
        Function.update (Function.update (fun _ => none) x (some 0)) y (some 0) := by
    intro x y hxy hyx
    apply colourStep_zero R
    intro o' _ ho' hcf
    by_cases hx : o' = x
    · subst hx; exact absurd hcf hyx
    · simp [Function.update_of_ne hx]
  have step1 : ∀ x : ParObj ℕ, R.colourStep (fun _ => none) x =
      Function.update (fun _ => none) x (some 0) := by
    intro x
    apply colourStep_zero R
    intro o' _ _ _; simp
  unfold Rules.parColour
  rcases parOrder_eq R hR with h | h <;> rw [h]
  · simp only [List.foldl_cons, List.foldl_nil, step1,
      step2 o₁ o₂ o₁_ne_o₂ hc.2]
    simp [Function.update_of_ne o₁_ne_o₂]
  · simp only [List.foldl_cons, List.foldl_nil, step1,
      step2 o₂ o₁ o₁_ne_o₂.symm hc.1]
    simp [Function.update_of_ne o₁_ne_o₂.symm]


/-! ## (c), (d), (e1): nothing happens (no hubs) -/

omit hR in
theorem colouredHub_eq (L : Lists I.G I.M) : R.colouredHub L = ∅ := by
  simp [Rules.colouredHub, I_hubItems]

omit hR in
theorem e1Items_eq (L : Lists I.G I.M) : R.e1Items L = ∅ := by
  simp [Rules.e1Items, colouredHub_eq R]

theorem e1Order_eq (L : Lists I.G I.M) : R.e1Order L = [] := by
  have h := (hR.e1Order L).2
  rw [e1Items_eq R] at h
  simpa using h

theorem used_eq (L : Lists I.G I.M) (u : ℕ) : R.used L u = ∅ := by
  simp [Rules.used, Rules.e1State, e1Order_eq R hR]

/-! ## (e2): `E'` and the junctions -/

omit hR in
theorem E'_o₁ (L : Lists I.G I.M) (b : Bool) : R.E' L (o₁.endAt b) = {REnd.par o₁ b} := by
  rw [Rules.E', colouredHub_eq R, parObjs_eq R]
  simp only [Finset.filter_empty, Finset.image_empty, Finset.union_empty]
  rw [Finset.biUnion_insert, Finset.singleton_biUnion]
  have h2 : (Finset.univ.filter (fun b' : Bool => o₂.endAt b' = o₁.endAt b)) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro b' _ h; exact endAt_o₁_ne_o₂ b b' h.symm
  have h1 : (Finset.univ.filter (fun b' : Bool => o₁.endAt b' = o₁.endAt b)) = {b} := by
    ext b'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨fun h => endAt_o₁_inj h, fun h => h ▸ rfl⟩
  rw [h1, h2]
  simp

omit hR in
theorem E'_o₂ (L : Lists I.G I.M) (b : Bool) : R.E' L (o₂.endAt b) = {REnd.par o₂ b} := by
  rw [Rules.E', colouredHub_eq R, parObjs_eq R]
  simp only [Finset.filter_empty, Finset.image_empty, Finset.union_empty]
  rw [Finset.biUnion_insert, Finset.singleton_biUnion]
  have h1 : (Finset.univ.filter (fun b' : Bool => o₁.endAt b' = o₂.endAt b)) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro b' _ h; exact endAt_o₁_ne_o₂ b' b h
  have h2 : (Finset.univ.filter (fun b' : Bool => o₂.endAt b' = o₂.endAt b)) = {b} := by
    ext b'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨fun h => endAt_o₂_inj h, fun h => h ▸ rfl⟩
  rw [h1, h2]
  simp

theorem e2Order_o₁ (L : Lists I.G I.M) (b : Bool) :
    R.e2Order L (o₁.endAt b) = [REnd.par o₁ b] :=
  list_singleton_of (hR.e2Order L _).1 ((hR.e2Order L _).2.trans (E'_o₁ R L b))

theorem e2Order_o₂ (L : Lists I.G I.M) (b : Bool) :
    R.e2Order L (o₂.endAt b) = [REnd.par o₂ b] :=
  list_singleton_of (hR.e2Order L _).1 ((hR.e2Order L _).2.trans (E'_o₂ R L b))

theorem junction_o₁ (ξ : Xi I.G I.M) (b : Bool) :
    R.junction ξ (.par o₁ b) = some (jn (o₁.endAt b)) := by
  simp only [Rules.junction, Rules.e2Junc, REnd.port, e2Order_o₁ R hR, used_eq R hR,
    Finset.sdiff_empty, I_cand (endAt_o₁_port b)]
  rw [inOrder_single ξ.2 (endAt_o₁_port b)]
  simp

theorem junction_o₂ (ξ : Xi I.G I.M) (b : Bool) :
    R.junction ξ (.par o₂ b) = some (jn (o₂.endAt b)) := by
  simp only [Rules.junction, Rules.e2Junc, REnd.port, e2Order_o₂ R hR, used_eq R hR,
    Finset.sdiff_empty, I_cand (endAt_o₂_port b)]
  rw [inOrder_single ξ.2 (endAt_o₂_port b)]
  simp

theorem not_looped (ξ : Xi I.G I.M) : ¬ R.Looped ξ o₁ ∧ ¬ R.Looped ξ o₂ := by
  constructor
  · rintro ⟨w, h1, h2⟩
    rw [junction_o₁ R hR] at h1 h2
    exact (jn_o₁ (parTag 0 0)).1 (Option.some_inj.1 h1 |>.trans (Option.some_inj.1 h2).symm)
  · rintro ⟨w, h1, h2⟩
    rw [junction_o₂ R hR] at h1 h2
    exact (jn_o₂ (parTag 0 0)).1 (Option.some_inj.1 h1 |>.trans (Option.some_inj.1 h2).symm)

/-! ## (g): layer edges, the `Q`-edge of each object, ranks -/

theorem layerEdges_eq (ξ : Xi I.G I.M) : R.layerEdges ξ = {Sum.inl o₁, Sum.inl o₂} := by
  have hnl := not_looped R hR ξ
  simp [Rules.layerEdges, Rules.unpaidPar, parObjs_eq R, colouredHub_eq R,
    Finset.filter_insert, Finset.filter_singleton, hnl.1, hnl.2]

theorem qEdge_o₁ (ξ : Xi I.G I.M) (ι : ℕ) : R.qEdge ξ ι (Sum.inl o₁) = some (E ι) := by
  simp only [Rules.qEdge, (parColour_eq R hR).1, junction_o₁ R hR, E]
  rw [if_neg (jn_o₁ (parTag 0 ι)).1, (jn_o₁ (parTag 0 ι)).2]

theorem qEdge_o₂ (ξ : Xi I.G I.M) (ι : ℕ) : R.qEdge ξ ι (Sum.inl o₂) = some (E ι) := by
  simp only [Rules.qEdge, (parColour_eq R hR).2, junction_o₂ R hR, E]
  rw [if_neg (jn_o₂ (parTag 0 ι)).1, (jn_o₂ (parTag 0 ι)).2]

theorem rankOrder_eq (ξ : Xi I.G I.M) :
    R.rankOrder ξ = [Sum.inl o₁, Sum.inl o₂] ∨ R.rankOrder ξ = [Sum.inl o₂, Sum.inl o₁] :=
  list_of_pair inl_ne (hR.rankOrder ξ).1 ((hR.rankOrder ξ).2.trans (layerEdges_eq R hR ξ))

/-- The two ranks are `1` and `2` (in the order of the rank list): **the rank split**. -/
theorem rank_eq (ξ : Xi I.G I.M) :
    (R.rank ξ (Sum.inl o₁) = 1 ∧ R.rank ξ (Sum.inl o₂) = 2) ∨
    (R.rank ξ (Sum.inl o₁) = 2 ∧ R.rank ξ (Sum.inl o₂) = 1) := by
  have hq := (qEdge_o₁ R hR ξ 0).trans (qEdge_o₂ R hR ξ 0).symm
  have hne : (Sum.inl o₁ : LayerEdge ℕ) ≠ Sum.inl o₂ := inl_ne
  rcases rankOrder_eq R hR ξ with h | h
  · left
    constructor
    · simp [Rules.rank, h]
    · simp [Rules.rank, h, hne, hq]
  · right
    constructor
    · simp [Rules.rank, h, hne.symm, hq]
    · simp [Rules.rank, h]

/-- **The quotient has exactly two edges**: the parallel pair `[4][5]` is split by rank. -/
theorem Q_edges (ξ : Xi I.G I.M) : (R.Q ξ).edges = {E 1, E 2} := by
  rw [Rules.Q_edges, Rules.qEdges, layerEdges_eq R hR]
  rw [Finset.biUnion_insert, Finset.singleton_biUnion]
  rcases rank_eq R hR ξ with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2, qEdge_o₁ R hR, qEdge_o₂ R hR]; simp
  · rw [h1, h2, qEdge_o₁ R hR, qEdge_o₂ R hR]; simp [Finset.pair_comm]

theorem Q_card_edges (ξ : Xi I.G I.M) : (R.Q ξ).edges.card = 2 := by
  rw [Q_edges R hR]; exact Finset.card_pair E_ne

theorem Q_card (ξ : Xi I.G I.M) : (R.Q ξ).card = 4 := by
  have hq := Q_edges R hR ξ
  rw [Rules.Q_edges] at hq
  rw [FGraph.card, Rules.Q_verts, hq]
  rw [Finset.biUnion_insert, Finset.singleton_biUnion]
  simp only [E]
  rw [Finset.card_eq_four]
  refine ⟨(parTag 0 1, 4), (parTag 0 1, 5), (parTag 0 2, 4), (parTag 0 2, 5), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [parTag]
  · simp [parTag]
  · simp [parTag]
  · simp [parTag]
  · simp [parTag]
  · simp [parTag]
  · ext v
    simp only [Finset.mem_union, Sym2.mem_toFinset, Sym2.mem_iff, Finset.mem_insert,
      Finset.mem_singleton, parTag]
    tauto

/-! ## (h): the lift of the two single edges of `Q_l` -/

theorem layerOf_E (ξ : Xi I.G I.M) :
    (R.layerOf ξ (E 1) = some (Sum.inl o₁) ∧ R.layerOf ξ (E 2) = some (Sum.inl o₂)) ∨
    (R.layerOf ξ (E 1) = some (Sum.inl o₂) ∧ R.layerOf ξ (E 2) = some (Sum.inl o₁)) := by
  unfold Rules.layerOf
  rw [layerEdges_eq R hR]
  have hE : E 2 ≠ E 1 := E_ne.symm
  rcases rank_eq R hR ξ with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left
    constructor
    · rw [Finset.filter_insert, Finset.filter_singleton, h1, h2, qEdge_o₁ R hR, qEdge_o₂ R hR]
      simp [hE]
    · rw [Finset.filter_insert, Finset.filter_singleton, h1, h2, qEdge_o₁ R hR, qEdge_o₂ R hR]
      simp [E_ne]
  · right
    constructor
    · rw [Finset.filter_insert, Finset.filter_singleton, h1, h2, qEdge_o₁ R hR, qEdge_o₂ R hR]
      simp [hE]
    · rw [Finset.filter_insert, Finset.filter_singleton, h1, h2, qEdge_o₁ R hR, qEdge_o₂ R hR]
      simp [E_ne]

/-- The lifts of the two `Q`-edges are the two `J^par` items, each as a single edge. -/
theorem lift_edges (ξ : Xi I.G I.M) :
    (R.liftObj ξ (.edge (E 1)) ++ R.liftObj ξ (.edge (E 2))).toFinset =
      {Obj.edge s(0, 2), Obj.edge s(1, 3)} := by
  have e1 := out_spec s(0, 2)
  have e2 := out_spec s(1, 3)
  rcases layerOf_E R hR ξ with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    simp [Rules.liftObj, h1, h2, ParObj.edgeList, e1, e2, Finset.pair_comm]

omit hR in
/-- Valid rules exist for this input, so the statement above is not vacuous. -/
theorem exists_valid_rules : ∃ R : Rules I, R.Valid := ⟨_, Rules.std_valid I I_Hcd_pos⟩

end rules

end Par

end EGTest.Quot
