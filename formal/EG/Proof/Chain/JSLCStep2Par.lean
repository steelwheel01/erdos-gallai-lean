module

public import EG.Proof.Chain.PAR
public import EG.Lib.Found.Graph

/-!
# JS-LC Step 2 (2a): Lemma PAR for one pair of classes (manuscript s6:lemJSLC, proof, Step 2)

Probe unit P2J (probe P-2, part 2), proof round 1.

"(2a) For each `Z ∈ Std_l` and each unordered pair `{a,b}` of distinct classes, let `E_ab(Z)` be
the set of port–port edges of `B_Z` joining a class-`a` port of `Q*_Z` to a class-`b` port of
`Q*_Z`. It is bipartite with sides `V_a` (class-`a` ports) and `V_b` (class-`b` ports). Apply
Lemma s6:lemPAR with any admissible choice of the deleted edges. This gives `J'_ab(Z)` and
`E_ab(Z) \ J'_ab(Z) = S_a ⊔ S_b`. The edges of `S_a` are *assigned to class `a`*: in them the
class-`b` end is a *pseudo-hub*, of even `S_a`-degree. Symmetrically, `S_b` is assigned to class
`b`."

Generic form: the classes are given by a map `cl : V → α`, the unordered pair of classes is
`p : Sym2 α` (not a loop), and `E` is an edge set whose edges `e` have `e.map cl = p` (one end of
each class). The assignment is a function `asg` with `asg e ∈ p`; "the class-`b` end is a
pseudo-hub of even `S_a`-degree" becomes: for every vertex `v` and every class `Y ≠ cl v`, the
number of edges of `E \ J'` at `v` assigned to `Y` is even. Uses `EG.parExists`, `EG.par`.
-/

public section

namespace EG.Chain

variable {V : Type*} [DecidableEq V] {α : Type*} [DecidableEq α]

/-- The bipartition of an edge set all of whose edges join a class-`Y₁` vertex to a class-`Y₂`
vertex. -/
theorem bip_of_map_eq {cl : V → α} {E : Finset (Sym2 V)} {Y₁ Y₂ : α}
    (hE : ∀ e ∈ E, e.map cl = s(Y₁, Y₂)) :
    ∀ e ∈ E, ∃ a ∈ (edgeVerts E).filter (fun v => cl v = Y₁),
      ∃ b ∈ (edgeVerts E).filter (fun v => cl v = Y₂), e = s(a, b) := by
  intro e he
  have hme := hE e he
  induction e using Sym2.ind with
  | _ u w =>
    rw [Sym2.map_mk, Sym2.eq_iff] at hme
    have hu : u ∈ edgeVerts E := by
      unfold edgeVerts; exact Finset.mem_biUnion.2 ⟨s(u, w), he, by simp⟩
    have hw : w ∈ edgeVerts E := by
      unfold edgeVerts; exact Finset.mem_biUnion.2 ⟨s(u, w), he, by simp⟩
    rcases hme with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨u, Finset.mem_filter.2 ⟨hu, h1⟩, w, Finset.mem_filter.2 ⟨hw, h2⟩, rfl⟩
    · exact ⟨w, Finset.mem_filter.2 ⟨hw, h2⟩, u, Finset.mem_filter.2 ⟨hu, h1⟩, Sym2.eq_swap⟩

/-- A vertex of an edge `e` with `e.map cl = s(Y₁, Y₂)` has class `Y₁` or `Y₂`. -/
theorem cl_mem_of_map_eq {cl : V → α} {e : Sym2 V} {p : Sym2 α} (hme : e.map cl = p) {v : V}
    (hv : v ∈ e) : cl v ∈ p := by
  rw [← hme]; exact Sym2.mem_map.2 ⟨v, hv, rfl⟩

/-- [s6:lemJSLC] (proof, Step 2 (2a)) Lemma PAR applied to one unordered pair `p = {a, b}` of
distinct classes: a deleted set `J'` with `2|J'| ≤ |V(E_ab)|` and an assignment of the remaining
edges to the classes of `p` such that every vertex has even degree in the edges assigned to each
class other than its own. -/
theorem exists_parLocal (cl : V → α) (E : Finset (Sym2 V)) (p : Sym2 α) :
    ∃ (Jp : Finset (Sym2 V)) (asg : Sym2 V → α), Jp ⊆ E ∧
      ((∀ e ∈ E, e.map cl = p) → ¬ p.IsDiag →
        2 * Jp.card ≤ (edgeVerts E).card ∧ (∀ e ∈ E, asg e ∈ p) ∧
        ∀ v Y, cl v ≠ Y → Even ((E \ Jp).filter (fun e => v ∈ e ∧ asg e = Y)).card) := by
  classical
  by_cases hgood : (∀ e ∈ E, e.map cl = p) ∧ ¬ p.IsDiag
  · obtain ⟨hE, hp⟩ := hgood
    induction p using Sym2.ind with
    | _ Y₁ Y₂ =>
      have hY : Y₁ ≠ Y₂ := fun h => hp (by rw [h]; exact Sym2.mk_isDiag_iff.2 rfl)
      set Va := (edgeVerts E).filter (fun v => cl v = Y₁) with hVa
      set Vb := (edgeVerts E).filter (fun v => cl v = Y₂) with hVb
      have hVab : Disjoint Va Vb := by
        rw [Finset.disjoint_left]
        intro v h1 h2
        exact hY ((Finset.mem_filter.1 h1).2.symm.trans (Finset.mem_filter.1 h2).2)
      have hbip := bip_of_map_eq hE
      obtain ⟨-, J', hJ'⟩ := EG.parExists V E Va Vb hVab hbip
      obtain ⟨hcard, hodd, Sa, Sb, hdisj, hunion, hSa, hSb⟩ := EG.par V E Va Vb hVab hbip J' hJ'
      refine ⟨J', fun e => if e ∈ Sa then Y₁ else Y₂, hJ'.1, fun _ _ => ⟨?_, ?_, ?_⟩⟩
      · have h2 : (oddComps E).card * 2 ≤ (edgeVerts E).card := by
          have := hodd
          rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)] at this
          exact_mod_cast this
        omega
      · intro e _
        by_cases h : e ∈ Sa <;> simp [h]
      · intro v Y hvY
        -- the edges of `E \ J'` at `v` assigned to `Y`
        by_cases h1 : Y = Y₁
        · subst h1
          have hset : (E \ J').filter (fun e => v ∈ e ∧ (if e ∈ Sa then Y else Y₂) = Y) =
              edgesAt Sa v := by
            ext e
            simp only [Finset.mem_filter, FGraph.mem_edgesAt]
            constructor
            · rintro ⟨-, hv, hs⟩
              split_ifs at hs with h
              · exact ⟨h, hv⟩
              · exact absurd hs.symm hY
            · rintro ⟨h, hv⟩
              refine ⟨?_, hv, by simp [h]⟩
              rw [← hunion]; exact Finset.mem_union_left _ h
          rw [hset]
          by_cases hvb : v ∈ Vb
          · exact hSa v hvb
          · -- `v` is on no edge of `Sa`: its class is not `Y`, so it would be in `Vb`
            have : edgesAt Sa v = ∅ := by
              ext e
              simp only [FGraph.mem_edgesAt, Finset.notMem_empty, iff_false, not_and]
              intro heS hv
              have heE : e ∈ E := by
                have : e ∈ E \ J' := by rw [← hunion]; exact Finset.mem_union_left _ heS
                exact (Finset.mem_sdiff.1 this).1
              have hcl := cl_mem_of_map_eq (hE e heE) hv
              rcases Sym2.mem_iff.1 hcl with h | h
              · exact hvY h
              · apply hvb
                refine Finset.mem_filter.2 ⟨?_, h⟩
                unfold edgeVerts; exact Finset.mem_biUnion.2 ⟨e, heE, by simpa using hv⟩
            rw [this]; exact ⟨0, rfl⟩
        · by_cases h2 : Y = Y₂
          · subst h2
            have hset : (E \ J').filter (fun e => v ∈ e ∧ (if e ∈ Sa then Y₁ else Y) = Y) =
                edgesAt Sb v := by
              ext e
              simp only [Finset.mem_filter, FGraph.mem_edgesAt]
              constructor
              · rintro ⟨he, hv, hs⟩
                split_ifs at hs with h
                · exact absurd hs.symm h1
                · refine ⟨?_, hv⟩
                  rw [← hunion] at he
                  rcases Finset.mem_union.1 he with h' | h'
                  · exact absurd h' h
                  · exact h'
              · rintro ⟨h, hv⟩
                have hnot : e ∉ Sa := fun h' => Finset.disjoint_left.1 hdisj h' h
                refine ⟨?_, hv, by simp [hnot]⟩
                rw [← hunion]; exact Finset.mem_union_right _ h
            rw [hset]
            by_cases hva : v ∈ Va
            · exact hSb v hva
            · have : edgesAt Sb v = ∅ := by
                ext e
                simp only [FGraph.mem_edgesAt, Finset.notMem_empty, iff_false, not_and]
                intro heS hv
                have heE : e ∈ E := by
                  have : e ∈ E \ J' := by rw [← hunion]; exact Finset.mem_union_right _ heS
                  exact (Finset.mem_sdiff.1 this).1
                have hcl := cl_mem_of_map_eq (hE e heE) hv
                rcases Sym2.mem_iff.1 hcl with h | h
                · apply hva
                  refine Finset.mem_filter.2 ⟨?_, h⟩
                  unfold edgeVerts; exact Finset.mem_biUnion.2 ⟨e, heE, by simpa using hv⟩
                · exact hvY h
              rw [this]; exact ⟨0, rfl⟩
          · have : (E \ J').filter (fun e => v ∈ e ∧ (if e ∈ Sa then Y₁ else Y₂) = Y) = ∅ := by
              ext e
              simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
              intro _ _ hs
              split_ifs at hs
              · exact h1 hs.symm
              · exact h2 hs.symm
            rw [this]; exact ⟨0, rfl⟩
  · refine ⟨∅, fun _ => (Quot.out p).1, Finset.empty_subset _, fun hE hp => ?_⟩
    · exact absurd ⟨hE, hp⟩ hgood

end EG.Chain
