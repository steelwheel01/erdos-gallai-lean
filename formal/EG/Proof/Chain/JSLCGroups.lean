module

public import EG.Proof.Chain.JSLCCtx

/-!
# JS-LC, Steps 5–7: cherry systems, junction pairs, joint routing, HCC-P hypotheses
(manuscript s6:lemJSLC, proof)

Probe unit P2J (probe P-2, part 2), proof round 1.

**Construction used here (a simplification of Steps 4–5, see `work/p2b/P2J.md`, "Proof round 1").**
Every component of `R_Y` (giant or not) is split into cherries (Step 5). The cherries of `(Y,l)`
are grouped by a first-fit pass (`EG.exists_firstFit`, the greedy colouring of Step 5 with the
colour classes cut into groups of at most `K^JS_l` cherries); each group `c_0, …, c_{k−1}`
(`1 ≤ k ≤ K^JS_l`, pairwise vertex-disjoint) is a layered system of depth `k` with one cherry per
layer (`EG.Chain.Cherry.cherrySys`): all loads are `1`, no padding is needed, and the system costs
one cycle. The manuscript's system `𝒮_0(Y,l)` (MED orientation, EQ-LPT layering, padding) is not
used; its hypothesis checks are the separately proved claims `EG.jslcPairsBalance`,
`EG.jslcPairsDistinct`, `EG.jslcJointMult`.

* `chs Y`: the cherries of `R_Y`; `grp Y i`, `lst Y i`: the group of colour `i` (as a list);
  `used Y`: the colours in use; `usedJ Y j`: the groups of depth `> j`;
* `pair Y j i`: the junction-`j` pair of the group `i`: `(u'_j, u_{j+1 mod k})` (Step 6: "the
  out-units of layer `j` … and the in-units of layer `j+1` modulo `k_𝒮`");
* `pair_ends`: claim (a) (ends distinct, in `V(Y)`); `card_pairs_le`: claim (c) (every vertex lies
  in at most `deg_{R_Y}(v) ≤ M_l − 1 < t` pairs of `𝔓_j(Y,l)`); `exists_routes`: claim (d) (joint
  routing through `T_j(Y,l)` in `LJS_{Y,l,j}`, by `EG.jslcRouting`);
* `sys Y i`: the HCC-P data of the group; `sys_valid`: Step 7, the hypotheses of HCC-P.
-/

public section

namespace EG.Chain.JSLC

open EG.HB EG.Chain EG.Chain.Cherry

variable {V : Type*} [DecidableEq V] (run : Run V) (G : FGraph V) (S : StageData V) (l : ℕ)
  (R : PartId → Finset (Sym2 V)) (col : PartId → V × V × V → ℕ)

/-- The cherries of `R_Y` (centres outside `V(Y)`). -/
@[expose] noncomputable def chs (Y : PartId) : Finset (V × V × V) :=
  cherries (R Y) (run.ancVerts G Y)

/-- The group of colour `i`. -/
@[expose] noncomputable def grp (Y : PartId) (i : ℕ) : Finset (V × V × V) :=
  (chs run G R Y).filter (fun c => col Y c = i)

/-- The group of colour `i` as a list `c_0, …, c_{k−1}` (the layers). -/
@[expose] noncomputable def lst (Y : PartId) (i : ℕ) : List (V × V × V) := (grp run G R col Y i).toList

/-- The colours in use. -/
@[expose] noncomputable def used (Y : PartId) : Finset ℕ := (chs run G R Y).image (col Y)

/-- The groups of depth `> j` (those with a junction `j`). -/
@[expose] noncomputable def usedJ (Y : PartId) (j : ℕ) : Finset ℕ :=
  (used run G R col Y).filter (fun i => j < (lst run G R col Y i).length)

/-- The junction-`j` pair `(u'_j, u_{j+1 mod k})` of the group `i`. -/
@[expose] noncomputable def pair (Y : PartId) (j : ℕ) (i : usedJ run G R col Y j) : V × V :=
  (((lst run G R col Y i).get ⟨j, (Finset.mem_filter.1 i.2).2⟩).2.2,
   ((lst run G R col Y i).get ⟨(j + 1) % (lst run G R col Y i).length,
     Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_filter.1 i.2).2)⟩).2.1)

/-- The paths of the group `i`, one per junction (junk `[]` outside its depth). -/
@[expose] noncomputable def Qs (rt : ∀ Y j, usedJ run G R col Y j → List V) (Y : PartId) (i : ℕ) :
    ℕ → List V :=
  fun j => if h : i ∈ usedJ run G R col Y j then rt Y j ⟨i, h⟩ else []

/-- The HCC-P data of the group `i` of `(Y,l)`. -/
@[expose] noncomputable def sys (rt : ∀ Y j, usedJ run G R col Y j → List V) (Y : PartId) (i : ℕ) :
    HccpData V :=
  cherrySys (lst run G R col Y i) (fun j => Tj run G S Y l j) (Qs run G R col rt Y i)

variable {run G S l R col}

theorem mem_lst {Y : PartId} {i : ℕ} {c : V × V × V} :
    c ∈ lst run G R col Y i ↔ c ∈ chs run G R Y ∧ col Y c = i := by
  unfold lst grp; rw [Finset.mem_toList, Finset.mem_filter]

theorem length_lst (Y : PartId) (i : ℕ) :
    (lst run G R col Y i).length = (grp run G R col Y i).card := Finset.length_toList _

theorem mem_used {Y : PartId} {i : ℕ} :
    i ∈ used run G R col Y ↔ ∃ c ∈ chs run G R Y, col Y c = i := by
  unfold used; rw [Finset.mem_image]

theorem lst_ne_nil {Y : PartId} {i : ℕ} (hi : i ∈ used run G R col Y) :
    lst run G R col Y i ≠ [] := by
  obtain ⟨c, hc, hci⟩ := mem_used.1 hi
  exact List.ne_nil_of_mem (mem_lst.2 ⟨hc, hci⟩)

/-! ### Under the setting and the grouping -/

variable {δ : Designation V} {B : Addr → Finset (Sym2 V)} {J : Finset (Sym2 V)}

/-- The conflict-degree bound for the grouping: `deg(h) + deg(u) + deg(u') ≤ m_{Y,l} + 2(M_l−1)`. -/
theorem card_conf_le' (C : JslcCtx run G δ S l B J R) (Y : PartId) :
    ∀ c ∈ chs run G R Y, ((chs run G R Y).filter (fun c' => c' ≠ c ∧ Conf c c')).card ≤
      mY run G δ Y l + 2 * (run.M G l - 1) := by
  intro c hc
  have hH := C.cherryHyp Y
  obtain ⟨-, -, -, h0, h1, h2⟩ := cherry_spec hH hc
  have := card_conf_le hH hc
  have d0 := C.degE_centre_le Y h0
  have d1 := C.degE_port_le Y h1
  have d2 := C.degE_port_le Y h2
  unfold chs
  omega

/-- The grouping of Step 5 exists for every `Y` ("Greedy colouring uses … colours"; the colour
classes cut into groups of at most `K^JS_l` cherries). -/
theorem exists_grouping (C : JslcCtx run G δ S l B J R) :
    ∃ (m : PartId → ℕ) (col : PartId → V × V × V → ℕ), ∀ Y,
      (∀ c ∈ chs run G R Y, col Y c < m Y) ∧
      (∀ c ∈ chs run G R Y, ∀ c' ∈ chs run G R Y, c ≠ c' → Conf c c' → col Y c ≠ col Y c') ∧
      (∀ i, ((chs run G R Y).filter (fun c => col Y c = i)).card ≤ Stage1.KJS G run l) ∧
      m Y * Stage1.KJS G run l ≤ (mY run G δ Y l + 2 * (run.M G l - 1) + 1) *
        Stage1.KJS G run l + (chs run G R Y).card := by
  have hK : 1 ≤ Stage1.KJS G run l := by
    unfold Stage1.KJS
    exact Nat.one_le_pow _ _ (lt_of_lt_of_le (by norm_num) (EG.Stage1.two_pow_le_M G run l))
  have h : ∀ Y, ∃ (m : ℕ) (c : V × V × V → ℕ),
      (∀ x ∈ chs run G R Y, c x < m) ∧
      (∀ x ∈ chs run G R Y, ∀ y ∈ chs run G R Y, x ≠ y → Conf x y → c x ≠ c y) ∧
      (∀ i, ((chs run G R Y).filter (fun x => c x = i)).card ≤ Stage1.KJS G run l) ∧
      m * Stage1.KJS G run l ≤ (mY run G δ Y l + 2 * (run.M G l - 1) + 1) *
        Stage1.KJS G run l + (chs run G R Y).card := fun Y =>
    EG.exists_firstFit (chs run G R Y) Conf (fun _ _ h => conf_symm h) _ _ hK
      (fun c hc => by
        refine le_trans (Finset.card_le_card fun c' hc' => ?_) (card_conf_le' C Y c hc)
        obtain ⟨hc', hne, hconf⟩ := Finset.mem_filter.1 hc'
        exact Finset.mem_filter.2 ⟨hc', hne, hconf⟩)
  choose m col hcol using h
  exact ⟨m, col, hcol⟩

/-- The specification of a grouping. -/
@[expose] def GroupSpec (run : Run V) (G : FGraph V) (l : ℕ) (R : PartId → Finset (Sym2 V))
    (δ : Designation V) (m : PartId → ℕ) (col : PartId → V × V × V → ℕ) : Prop :=
  ∀ Y, (∀ c ∈ chs run G R Y, col Y c < m Y) ∧
    (∀ c ∈ chs run G R Y, ∀ c' ∈ chs run G R Y, c ≠ c' → Conf c c' → col Y c ≠ col Y c') ∧
    (∀ i, ((chs run G R Y).filter (fun c => col Y c = i)).card ≤ Stage1.KJS G run l) ∧
    m Y * Stage1.KJS G run l ≤ (mY run G δ Y l + 2 * (run.M G l - 1) + 1) *
      Stage1.KJS G run l + (chs run G R Y).card

variable {m : PartId → ℕ}

/-- The cherries of one group are pairwise vertex-disjoint ("each colour class … is a set of
pairwise vertex-disjoint cherries"). -/
theorem lst_pairwise (hg : GroupSpec run G l R δ m col)
    (Y : PartId) (i : ℕ) :
    (lst run G R col Y i).Pairwise (fun c c' => Disjoint (cVerts c) (cVerts c')) := by
  refine (Finset.nodup_toList _).pairwise_of_forall_ne fun c hc c' hc' hne => ?_
  obtain ⟨hc, hci⟩ := mem_lst.1 hc
  obtain ⟨hc', hci'⟩ := mem_lst.1 hc'
  by_contra hconf
  exact (hg Y).2.1 c hc c' hc' hne hconf (hci.trans hci'.symm)

theorem length_lst_le (hg : GroupSpec run G l R δ m col)
    (Y : PartId) (i : ℕ) : (lst run G R col Y i).length ≤ Stage1.KJS G run l := by
  rw [length_lst]; exact (hg Y).2.2.1 i

/-- The groups of distinct colours are disjoint. -/
theorem grp_disjoint {Y : PartId} {i i' : ℕ} (hii : i ≠ i') :
    Disjoint (grp run G R col Y i) (grp run G R col Y i') := by
  rw [Finset.disjoint_left]
  intro c hc hc'
  exact hii ((Finset.mem_filter.1 hc).2.symm.trans (Finset.mem_filter.1 hc').2)

/-- Claim (a): the two vertices of a pair are distinct ports of `V(Y)`. -/
theorem pair_ends (C : JslcCtx run G δ S l B J R)
    (hg : GroupSpec run G l R δ m col) (Y : PartId) (j : ℕ)
    (i : usedJ run G R col Y j) :
    (pair run G R col Y j i).1 ∈ run.ancVerts G Y ∧ (pair run G R col Y j i).2 ∈ run.ancVerts G Y ∧
      (pair run G R col Y j i).1 ≠ (pair run G R col Y j i).2 := by
  have hH := C.cherryHyp Y
  set L := lst run G R col Y i with hL
  have hj : j < L.length := (Finset.mem_filter.1 i.2).2
  have hpos : 0 < L.length := Nat.lt_of_le_of_lt (Nat.zero_le _) hj
  have hmem : ∀ x : Fin L.length, L.get x ∈ chs run G R Y := fun x => (mem_lst.1 (List.get_mem L x)).1
  obtain ⟨-, -, hne1, -, -, h2⟩ := cherry_spec hH (hmem ⟨j, hj⟩)
  obtain ⟨-, -, hne2, -, h1', -⟩ := cherry_spec hH (hmem ⟨(j + 1) % L.length, Nat.mod_lt _ hpos⟩)
  refine ⟨h2, h1', ?_⟩
  show (L.get ⟨j, hj⟩).2.2 ≠ (L.get ⟨(j + 1) % L.length, Nat.mod_lt _ hpos⟩).2.1
  by_cases hjj : j = (j + 1) % L.length
  · have : (⟨j, hj⟩ : Fin L.length) = ⟨(j + 1) % L.length, Nat.mod_lt _ hpos⟩ := Fin.ext hjj
    rw [← this]
    exact Ne.symm hne1
  · -- distinct cherries of one group are vertex-disjoint
    have hdisj := lst_pairwise hg Y i
    have hne : (⟨j, hj⟩ : Fin L.length) ≠ ⟨(j + 1) % L.length, Nat.mod_lt _ hpos⟩ :=
      fun h => hjj (congrArg Fin.val h)
    have hD : Disjoint (cVerts (L.get ⟨j, hj⟩))
        (cVerts (L.get ⟨(j + 1) % L.length, Nat.mod_lt _ hpos⟩)) := by
      rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with h | h
      · exact List.Pairwise.rel_get_of_lt hdisj h
      · exact (List.Pairwise.rel_get_of_lt hdisj h).symm
    intro heq
    have hm1 : (L.get ⟨j, hj⟩).2.2 ∈ cVerts (L.get ⟨j, hj⟩) := by unfold cVerts; simp
    have hm2 : (L.get ⟨j, hj⟩).2.2 ∈ cVerts (L.get ⟨(j + 1) % L.length, Nat.mod_lt _ hpos⟩) := by
      rw [heq]; unfold cVerts; simp
    exact Finset.disjoint_left.1 hD hm1 hm2

/-- Claim (c): a vertex `v` lies in at most `deg_{R_Y}(v)` junction-`j` pairs of `(Y,l)` (at most
one per group, and only in groups having a cherry with end `v`). -/
theorem card_pairs_le (C : JslcCtx run G δ S l B J R)
    (hg : GroupSpec run G l R δ m col) (Y : PartId) (j : ℕ)
    (v : V) :
    (Finset.univ.filter (fun i : usedJ run G R col Y j =>
      (pair run G R col Y j i).1 = v ∨ (pair run G R col Y j i).2 = v)).card ≤ degE (R Y) v := by
  classical
  have hH := C.cherryHyp Y
  refine le_trans ?_ (card_cherries_port_le hH v)
  -- the cherry of the group containing `v` in the pair
  let f : usedJ run G R col Y j → V × V × V := fun i =>
    if (pair run G R col Y j i).1 = v then
      (lst run G R col Y i).get ⟨j, (Finset.mem_filter.1 i.2).2⟩
    else (lst run G R col Y i).get ⟨(j + 1) % (lst run G R col Y i).length,
      Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_filter.1 i.2).2)⟩
  have hf : ∀ i : usedJ run G R col Y j, f i ∈ lst run G R col Y i := by
    intro i; simp only [f]; split_ifs <;> exact List.get_mem _ _
  refine Finset.card_le_card_of_injOn f ?_ ?_
  · intro i hi
    obtain ⟨-, hv⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hi)
    refine Finset.mem_coe.2 (Finset.mem_filter.2 ⟨(mem_lst.1 (hf i)).1, ?_⟩)
    simp only [f]
    split_ifs with h1
    · exact Or.inr h1
    · rcases hv with h | h
      · exact absurd h h1
      · exact Or.inl h
  · intro i _ i' _ hii
    have e1 := (mem_lst.1 (hf i)).2
    have e2 := (mem_lst.1 (hf i')).2
    rw [hii] at e1
    exact Subtype.ext (e1.symm.trans e2)

/-- Claim (d) with (a), (c): the joint routing of the junction-`j` pairs of `(Y,l)` in
`LJS_{Y,l,j}` through `T_j(Y,l)` (Lemma s3:lemCOL(b), `EG.jslcRouting`). -/
theorem exists_routes (C : JslcCtx run G δ S l B J R)
    (hg : GroupSpec run G l R δ m col) :
    ∃ rt : ∀ Y j, usedJ run G R col Y j → List V, ∀ Y j,
      Y ∈ Step2.classes run G δ S l → j < Stage1.KJS G run l →
      (∀ i, IsPathBetween (S.ljs Y l j) (pair run G R col Y j i).1 (pair run G R col Y j i).2
          (rt Y j i) ∧ IsThrough (Tj run G S Y l j) (rt Y j i)) ∧
      ∀ i i', i ≠ i' → (walkEdges (rt Y j i)).Disjoint (walkEdges (rt Y j i')) := by
  have h : ∀ Y j, ∃ Qr : usedJ run G R col Y j → List V,
      Y ∈ Step2.classes run G δ S l → j < Stage1.KJS G run l →
      (∀ i, IsPathBetween (S.ljs Y l j) (pair run G R col Y j i).1 (pair run G R col Y j i).2
          (Qr i) ∧ IsThrough (Tj run G S Y l j) (Qr i)) ∧
      ∀ i i', i ≠ i' → (walkEdges (Qr i)).Disjoint (walkEdges (Qr i')) := by
    intro Y j
    by_cases hc : Y ∈ Step2.classes run G δ S l ∧ j < Stage1.KJS G run l
    · obtain ⟨Q, hQ, hdisj⟩ := EG.jslcRouting V G run S l Y j C.hS (C.Ycl_lendGood hc.1) C.lR
        hc.2 (usedJ run G R col Y j) (pair run G R col Y j) (pair_ends C hg Y j)
        (fun v => by
          have key : (Finset.univ.filter (fun i : usedJ run G R col Y j =>
              (pair run G R col Y j i).1 = v ∨ (pair run G R col Y j i).2 = v)).card ≤
              Stage1.tJS G run l := by
            by_cases hv : v ∈ run.ancVerts G Y
            · have h1 := card_pairs_le C hg Y j v
              have h2 := C.degE_port_le Y hv
              unfold Stage1.tJS; omega
            · -- a centre is in no pair
              have hz : (Finset.univ.filter (fun i : usedJ run G R col Y j =>
                  (pair run G R col Y j i).1 = v ∨ (pair run G R col Y j i).2 = v)).card = 0 := by
                rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
                intro i _ hi
                obtain ⟨h1, h2, -⟩ := pair_ends C hg Y j i
                rcases hi with hi | hi
                · exact hv (hi ▸ h1)
                · exact hv (hi ▸ h2)
              rw [hz]; exact Nat.zero_le _
          exact_mod_cast key)
      exact ⟨Q, fun _ _ => ⟨fun i => ⟨(hQ i).1, (hQ i).2.1⟩, hdisj⟩⟩
    · exact ⟨fun _ => [], fun h1 h2 => absurd ⟨h1, h2⟩ hc⟩
  choose rt hrt using h
  exact ⟨rt, hrt⟩

end EG.Chain.JSLC
