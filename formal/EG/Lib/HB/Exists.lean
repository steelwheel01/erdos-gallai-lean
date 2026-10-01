module

public import EG.Lib.HB.Lemma14Ind
public import EG.Lib.HB.Run
public import EG.Lib.Found.Fnum

/-!
# Helpers for Proposition s2:propExists (manuscript s2:propExists)

Helper lemmas for `EG.Todo.RoundSteps`, `EG.Todo.RoundExists`, `EG.Todo.ExistsRun` (unit P3-s2).
* `Round.exists_cyclesValid`: "(R1) deletes at least one edge per step, so it terminates": a
  maximal family of edge-disjoint long cycles exists (greedy, by induction on the number of
  remaining edges);
* `STree.s0Build`, `STree.s0Build_spec`: "In the first level of (R3), a node that is not an
  `(ε,0)`-expander has a witness …, and its children have `|U| + |N| < (3/4) m` and `m - |U| < m`
  vertices …; so every root-to-node path has at most `n` nodes and this level terminates": the
  `s = 0` recursion using a given witness rule (fuel `n ≥ |K|`).
-/

public section

namespace EG.HB

open Real

variable {V : Type*} [DecidableEq V]

/-! ### (R1): a maximal family of long cycles -/

namespace Round

/-- The (R1) conditions on a list of cycles, without maximality. -/
def CycGood (H : FGraph V) (L : List (List V)) : Prop :=
  (∀ cyc ∈ L, (Obj.cycle cyc).WF ∧ (∀ e ∈ cycleEdges cyc, e ∈ H.edges) ∧
      TOf (d H) ≤ (cyc.length : ℝ)) ∧ (L.flatMap cycleEdges).Nodup

theorem graph'_edges_mk (H : FGraph V) (L : List (List V)) :
    (graph' H (⟨L, .nil, fun _ => .nil, []⟩ : RoundChoice V)).edges =
      H.edges \ (L.flatMap cycleEdges).toFinset := rfl

theorem exists_cyclesValid_aux (H : FGraph V) : ∀ (n : ℕ) (L : List (List V)), CycGood H L →
    (H.edges \ (L.flatMap cycleEdges).toFinset).card ≤ n →
    ∃ L' : List (List V), CyclesValid H (⟨L', .nil, fun _ => .nil, []⟩ : RoundChoice V) := by
  intro n
  induction n with
  | zero =>
    intro L hL hcard
    refine ⟨L, hL.1, hL.2, fun cyc hwf hce => ?_⟩
    exfalso
    have hrem : H.edges \ (L.flatMap cycleEdges).toFinset = ∅ :=
      Finset.card_eq_zero.1 (by omega)
    have hne : cycleEdges cyc ≠ [] := by
      intro h; have h3 : 3 ≤ cyc.length := hwf.2; have := congrArg List.length h
      rw [length_cycleEdges, List.length_nil] at this; omega
    obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil _ hne
    have := hce e he
    rw [graph'_edges_mk, hrem] at this
    simp at this
  | succ n ih =>
    intro L hL hcard
    by_cases hex : ∃ cyc : List V, (Obj.cycle cyc).WF ∧
        (∀ e ∈ cycleEdges cyc, e ∈ H.edges \ (L.flatMap cycleEdges).toFinset) ∧
        TOf (d H) ≤ (cyc.length : ℝ)
    · obtain ⟨cyc, hwf, hce, hT⟩ := hex
      have hce' : ∀ e ∈ cycleEdges cyc, e ∈ H.edges := fun e he => (Finset.mem_sdiff.1 (hce e he)).1
      have hL' : CycGood H (L ++ [cyc]) := by
        refine ⟨fun c hc => ?_, ?_⟩
        · rcases List.mem_append.1 hc with hc | hc
          · exact hL.1 c hc
          · rw [List.mem_singleton] at hc; subst hc; exact ⟨hwf, hce', hT⟩
        · rw [List.flatMap_append, List.nodup_append]
          refine ⟨hL.2, by simpa using nodup_cycleEdges hwf.1 hwf.2, fun a ha b hb hab => ?_⟩
          subst hab
          have := (Finset.mem_sdiff.1 (hce a (by simpa using hb))).2
          exact this (List.mem_toFinset.2 ha)
      apply ih (L ++ [cyc]) hL'
      have hne : cycleEdges cyc ≠ [] := by
        intro h; have h3 : 3 ≤ cyc.length := hwf.2; have := congrArg List.length h
        rw [length_cycleEdges, List.length_nil] at this; omega
      obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil _ hne
      have hsub : H.edges \ ((L ++ [cyc]).flatMap cycleEdges).toFinset ⊂
          H.edges \ (L.flatMap cycleEdges).toFinset := by
        rw [Finset.ssubset_iff_of_subset]
        · refine ⟨e, hce e he, ?_⟩
          simp only [Finset.mem_sdiff, List.mem_toFinset, List.flatMap_append, List.mem_append,
            not_or, not_and, not_not]
          intro _ _
          simpa using he
        · intro x hx
          simp only [Finset.mem_sdiff, List.mem_toFinset, List.flatMap_append, List.mem_append,
            not_or] at hx ⊢
          exact ⟨hx.1, hx.2.1⟩
      have := Finset.card_lt_card hsub
      omega
    · push Not at hex
      exact ⟨L, hL.1, hL.2, fun cyc hwf hce => hex cyc hwf (fun e he => by
        have := hce e he; rwa [graph'_edges_mk] at this)⟩

/-- "(R1) … terminates": a family of long cycles as required by (R1) exists. -/
theorem exists_cyclesValid (H : FGraph V) :
    ∃ L : List (List V), CyclesValid H (⟨L, .nil, fun _ => .nil, []⟩ : RoundChoice V) :=
  exists_cyclesValid_aux H _ [] ⟨by simp, by simp⟩ le_rfl

end Round

/-! ### (R3), first level: the `s = 0` recursion with a given witness rule -/

namespace STree

/-- The `s = 0` recursion that uses the witness rule `W`, with fuel `n`. -/
noncomputable def s0Build (ε : ℝ) (W : Addr → FGraph V → Finset V × Finset (Sym2 V)) :
    ℕ → Addr → FGraph V → STree V
  | 0, _, _ => .nil
  | n + 1, a, K =>
    haveI := Classical.dec (K.IsExpander ε 0)
    if K.IsExpander ε 0 then .nil else
      .node ((W a K).1, K.nbrSet (W a K).1)
        (s0Build ε W n (a ++ [false]) (splitFst K (W a K).1 (K.nbrSet (W a K).1)))
        (s0Build ε W n (a ++ [true]) (splitSnd K (W a K).1 (K.nbrSet (W a K).1)))

theorem isS0Rec_node {ε : ℝ} (p : Finset V × Finset V) (l r : STree V) (K : FGraph V)
    (h0 : p.1 ⊆ K.verts ∧ p.2 ⊆ K.verts ∧ Disjoint p.1 p.2)
    (hw : ∃ (U : Finset V) (F : Finset (Sym2 V)), IsWitness K ε 0 U F ∧ p = (U, K.nbrSet U))
    (hl : l.IsS0Rec ε (splitFst K p.1 p.2)) (hr : r.IsS0Rec ε (splitSnd K p.1 p.2)) :
    (STree.node p l r).IsS0Rec ε K := by
  refine ⟨(wf_node_iff p l r K).2 ⟨h0, hl.1, hr.1⟩, fun a ha => ?_⟩
  cases a with
  | nil =>
    obtain ⟨U, F, hwit, hp⟩ := hw
    exact ⟨U, F, by simpa using hwit, by simp [hp]⟩
  | cons c a =>
    rw [mem_internalAddrs_node_cons] at ha
    cases c
    · obtain ⟨U, F, hwit, h⟩ := hl.2 a ha
      exact ⟨U, F, by simpa using hwit, by simpa using h⟩
    · obtain ⟨U, F, hwit, h⟩ := hr.2 a ha
      exact ⟨U, F, by simpa using hwit, by simpa using h⟩

theorem stopsAt_node {P : FGraph V → Prop} (p : Finset V × Finset V) (l r : STree V)
    (K : FGraph V) (hK : ¬ P K) (hl : l.StopsAt (splitFst K p.1 p.2) P)
    (hr : r.StopsAt (splitSnd K p.1 p.2) P) : (STree.node p l r).StopsAt K P := by
  intro a ha
  cases a with
  | nil => simpa using hK
  | cons c a =>
    rw [mem_nodeAddrs_node_cons] at ha
    cases c
    · simpa using hl a ha
    · simpa using hr a ha

/-- The children of an `s = 0` split are smaller: `|U ∪ N| < m` and `m - |U| < m`. -/
theorem s0_children_lt {K : FGraph V} {U : Finset V} {F : Finset (Sym2 V)}
    (hw : IsWitness K epsC 0 U F) :
    (splitFst K U (K.nbrSet U)).card < K.card ∧ (splitSnd K U (K.nbrSet U)).card < K.card := by
  have hF : F = ∅ := eq_empty_of_isWitness_zero hw
  subst hF
  obtain ⟨hUV, -, hU1, hU2, -, hN⟩ := hw
  rw [FGraph.deleteEdges_empty] at hN
  have h2 : 2 ≤ K.card := by
    have h1' : (1 : ℝ) ≤ U.card := by exact_mod_cast hU1
    have : (1 : ℝ) < K.card := by linarith
    have : 1 < K.card := by exact_mod_cast this
    omega
  have hL : 1 ≤ logb 2 (K.card : ℝ) := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by positivity)]
    have : (2 : ℝ) ≤ K.card := by exact_mod_cast h2
    simpa using this
  have hL2 : 1 ≤ logb 2 (K.card : ℝ) ^ 2 := one_le_pow₀ hL
  have hε := epsC_eq
  have hNU : ((K.nbrSet U).card : ℝ) < U.card / 32 := by
    rw [hε] at hN
    have : 1 / 32 * (U.card : ℝ) / logb 2 (K.card : ℝ) ^ 2 ≤ U.card / 32 := by
      rw [div_le_iff₀ (by positivity)]
      have : (0 : ℝ) ≤ U.card := Nat.cast_nonneg _
      nlinarith
    linarith
  constructor
  · have h1 : (splitFst K U (K.nbrSet U)).card ≤ (U ∪ K.nbrSet U).card := by
      show (splitFst K U (K.nbrSet U)).verts.card ≤ _
      rw [splitFst_verts]; exact Finset.card_le_card Finset.inter_subset_right
    have h2' := Finset.card_union_le U (K.nbrSet U)
    have e1 : ((splitFst K U (K.nbrSet U)).card : ℝ) ≤ U.card + (K.nbrSet U).card := by
      exact_mod_cast h1.trans h2'
    have : ((splitFst K U (K.nbrSet U)).card : ℝ) < K.card := by
      have : (0 : ℝ) ≤ U.card := Nat.cast_nonneg _
      linarith
    exact_mod_cast this
  · show (splitSnd K U (K.nbrSet U)).verts.card < K.verts.card
    rw [splitSnd_verts, Finset.card_sdiff_of_subset hUV]
    have : U.card ≤ K.verts.card := Finset.card_le_card hUV
    omega

theorem s0Build_spec (W : Addr → FGraph V → Finset V × Finset (Sym2 V))
    (hW : ∀ (a : Addr) (K : FGraph V), ¬ K.IsExpander epsC 0 →
      IsWitness K epsC 0 (W a K).1 (W a K).2) :
    ∀ (n : ℕ) (a : Addr) (K : FGraph V), K.card ≤ n →
      (s0Build epsC W n a K).IsS0Rec epsC K ∧
      (s0Build epsC W n a K).StopsAt K (fun Q => Q.IsExpander epsC 0) ∧
      ∀ b ∈ (s0Build epsC W n a K).internalAddrs,
        (s0Build epsC W n a K).labelAt b = some
          ((W (a ++ b) ((s0Build epsC W n a K).graphAtD K b)).1,
            ((s0Build epsC W n a K).graphAtD K b).nbrSet
              (W (a ++ b) ((s0Build epsC W n a K).graphAtD K b)).1) := by
  intro n
  induction n with
  | zero =>
    intro a K hK
    have hK0 : K.card = 0 := by omega
    refine ⟨isS0Rec_nil _ _, (stopsAt_nil_iff _ _).2 (isExpander_of_card_eq_zero hK0 _ _), ?_⟩
    intro b hb
    simp [s0Build] at hb
  | succ n ih =>
    intro a K hK
    by_cases hexp : K.IsExpander epsC 0
    · have e : s0Build epsC W (n + 1) a K = .nil := by
        simp only [s0Build]; rw [if_pos hexp]
      rw [e]
      refine ⟨isS0Rec_nil _ _, (stopsAt_nil_iff _ _).2 hexp, ?_⟩
      intro b hb; simp at hb
    · set U := (W a K).1
      have hw : IsWitness K epsC 0 U (W a K).2 := hW a K hexp
      set N := K.nbrSet U
      have e : s0Build epsC W (n + 1) a K =
          .node (U, N) (s0Build epsC W n (a ++ [false]) (splitFst K U N))
            (s0Build epsC W n (a ++ [true]) (splitSnd K U N)) := by
        simp only [s0Build]; rw [if_neg hexp]
      rw [e]
      obtain ⟨h1, h2⟩ : (splitFst K U N).card < K.card ∧ (splitSnd K U N).card < K.card :=
        s0_children_lt hw
      obtain ⟨hl, hls, hll⟩ := ih (a ++ [false]) (splitFst K U N) (by omega)
      obtain ⟨hr, hrs, hrl⟩ := ih (a ++ [true]) (splitSnd K U N) (by omega)
      have h0 : U ⊆ K.verts ∧ N ⊆ K.verts ∧ Disjoint U N :=
        ⟨hw.1, K.nbrSet_subset_verts U, K.disjoint_nbrSet U⟩
      refine ⟨isS0Rec_node (U, N) _ _ K h0 ⟨U, (W a K).2, hw, rfl⟩ hl hr,
        stopsAt_node (U, N) _ _ K hexp hls hrs, ?_⟩
      intro b hb
      cases b with
      | nil => simp [U, N]
      | cons c b =>
        rw [mem_internalAddrs_node_cons] at hb
        cases c
        · have := hll b hb
          simp only [labelAt_node_false, graphAtD_node_false]
          rw [this]
          simp
        · have := hrl b hb
          simp only [labelAt_node_true, graphAtD_node_true]
          rw [this]
          simp

end STree

/-! ### Runs: prepending a round -/

namespace Run

omit [DecidableEq V] in
theorem choice_cons (c : RoundChoice V) (cs : List (RoundChoice V)) (l : ℕ) (hl : 1 ≤ l) :
    (Run.mk (c :: cs)).choice (l + 1) = (Run.mk cs).choice l := by
  simp only [choice, Nat.add_sub_cancel]
  obtain ⟨k, rfl⟩ : ∃ k, l = k + 1 := ⟨l - 1, by omega⟩
  simp

theorem graph_cons (G : FGraph V) (c : RoundChoice V) (cs : List (RoundChoice V)) :
    ∀ l, 1 ≤ l → (Run.mk (c :: cs)).graph G (l + 1) =
      (Run.mk cs).graph (Round.next G c) l := by
  intro l hl
  induction l, hl using Nat.le_induction with
  | base =>
    have h1 : (Run.mk (c :: cs)).IsRound 1 := ⟨le_rfl, by simp [R]⟩
    rw [graph_succ_of_isRound _ _ h1, graph_one, graph_one]
    rfl
  | succ l hl ih =>
    by_cases hr : (Run.mk cs).IsRound l
    · have hr' : (Run.mk (c :: cs)).IsRound (l + 1) := ⟨by omega, by
        have := hr.2; simp only [R, List.length_cons] at this ⊢; omega⟩
      rw [graph_succ_of_isRound _ _ hr', graph_succ_of_isRound _ _ hr, ih, choice_cons c cs l hl]
    · have hr' : ¬ (Run.mk (c :: cs)).IsRound (l + 1) := by
        intro h; apply hr
        refine ⟨hl, ?_⟩
        have := h.2; simp only [R, List.length_cons] at this ⊢; omega
      rw [graph_succ_of_not_isRound _ _ hr', graph_succ_of_not_isRound _ _ hr, ih]

theorem valid_cons {G : FGraph V} {Dstar : ℝ} {c : RoundChoice V} {cs : List (RoundChoice V)}
    (hd : Dstar ≤ Round.d G) (hc : Round.Valid G c)
    (hv : (Run.mk cs).Valid (Round.next G c) Dstar) : (Run.mk (c :: cs)).Valid G Dstar := by
  have hR : (Run.mk (c :: cs)).R = (Run.mk cs).R + 1 := by simp [R]
  refine ⟨fun l hl => ?_, ?_⟩
  · rw [hR, Finset.mem_Icc] at hl
    rcases Nat.eq_or_lt_of_le hl.1 with h1 | h1
    · subst h1
      refine ⟨?_, ?_⟩
      · change Dstar ≤ Round.d ((Run.mk (c :: cs)).graph G 1); rw [graph_one]; exact hd
      · rw [graph_one]; exact hc
    · obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
      have hl' : l' ∈ Finset.Icc 1 (Run.mk cs).R := Finset.mem_Icc.2 ⟨by omega, by omega⟩
      obtain ⟨h1', h2'⟩ := hv.1 l' hl'
      refine ⟨?_, ?_⟩
      · change Dstar ≤ Round.d ((Run.mk (c :: cs)).graph G (l' + 1))
        rw [graph_cons G c cs l' (by omega)]; exact h1'
      · rw [graph_cons G c cs l' (by omega), choice_cons c cs l' (by omega)]; exact h2'
  · rw [hR]
    change Round.d ((Run.mk (c :: cs)).graph G ((Run.mk cs).R + 1 + 1)) < Dstar
    rw [graph_cons G c cs _ (by omega)]
    exact hv.2

end Run

end EG.HB
