module

public import EG.Spec.Quot.Simple
public import EG.Lib.Quot.Quotient

/-!
# Proof of Lemma "`Q_l` is simple" (manuscript s7:lemSimple) — probe P-1, stage 3

Unit P1, design note `formal/work/p2b/P1.md`. Manuscript proof: "By the definition of ranks, a
sub-layer contains at most one edge of rank `ι` between any two vertices, so it has no parallel
edges. An edge of a PAR layer joins `[w_1]` and `[w_2]` with `w_1 ≠ w_2`, because looped PAR objects
were paid in (e3); so PAR sub-layers have no loops. An edge `h[w]` of a HUB layer joins the side
`D_l` to the side `{[w]}`. Moreover `h` is the hub of a coloured, hence live, item, so `h` is a live
vertex and `h ∉ Pool_l` by (a2), while `w ∈ Pool_l`. So `h ≠ w` […]."
-/

public section

namespace EG

open EG.Quot

theorem Quot.Rules.qEdge_tags {V : Type*} [DecidableEq V] {I : RoundInput V} {R : Rules I}
    (hI : I.Valid) (hR : R.Valid) {ξ : Xi I.G I.M} {a b : QVert V}
    (hab : s(a, b) ∈ (R.Q ξ).edges) :
    a.1.1 = b.1.1 ∧ a.1.2.1 = b.1.2.1 ∧ a.1.2.2.1 = b.1.2.2.1 ∧ 1 ≤ a.1.2.2.1 ∧
      (a.1.1 = false → a.1.2.1 < 3 * I.M ∧ a.1.2.2.2 = false ∧ b.1.2.2.2 = false) ∧
      (a.1.1 = true → a.1.2.1 < 4 * I.M ∧ a.1.2.2.2 ≠ b.1.2.2.2) ∧
      (∀ x : QVert V, x = a ∨ x = b →
        (x.1.2.2.2 = true → x.2 ∈ I.hubs) ∧ (x.1.2.2.2 = false → x.2 ∈ I.pool)) := by
  obtain ⟨e, he, hq⟩ := (R.mem_qEdges).1 hab
  have hι := R.one_le_rank ξ e
  rcases e with o | it
  · obtain ⟨κ, w₁, w₂, hκ, hw₁, hw₂, -, hq'⟩ := Rules.qEdge_par_iff.1 hq
    have hκ' := Rules.parColour_lt' hI hR hκ
    have p₁ := Rules.junction_pool hw₁
    have p₂ := Rules.junction_pool hw₂
    rcases Sym2.eq_iff.1 hq' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · refine ⟨rfl, rfl, rfl, hι, fun _ => ⟨hκ', rfl, rfl⟩, fun h => by simp [parTag] at h, ?_⟩
      rintro x (rfl | rfl) <;> simp [parTag, p₁, p₂]
    · refine ⟨rfl, rfl, rfl, hι, fun _ => ⟨hκ', rfl, rfl⟩, fun h => by simp [parTag] at h, ?_⟩
      rintro x (rfl | rfl) <;> simp [parTag, p₁, p₂]
  · obtain ⟨κ, w, hκ, hw, hq'⟩ := Rules.qEdge_hub_iff.1 hq
    have hκ' := Rules.hubColour_lt hR hκ
    have hit : it ∈ R.colouredHub ξ.1 := (Rules.hubColour_eq_some hκ).1
    have hh := RoundInput.hubItems_hub ((Rules.mem_colouredHub).1 hit).1
    have pw := Rules.junction_pool hw
    rcases Sym2.eq_iff.1 hq' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · refine ⟨rfl, rfl, rfl, hι, fun h => by simp [hubTag] at h, fun _ => ⟨hκ', by simp [hubTag]⟩,
        ?_⟩
      rintro x (rfl | rfl) <;> simp [hubTag, hh, pw]
    · refine ⟨rfl, rfl, rfl, hι, fun h => by simp [hubTag] at h, fun _ => ⟨hκ', by simp [hubTag]⟩,
        ?_⟩
      rintro x (rfl | rfl) <;> simp [hubTag, hh, pw]

/-- [s7:lemSimple] "Every sub-layer of Construction s7:consRound(g) is a simple graph: it has no
parallel edges, PAR sub-layers have no loops, and HUB sub-layers are bipartite between hubs and
junction copies `[w]`, where the hub `h` and the junction `w` of any edge `h[w]` are distinct
vertices of `G`. Consequently `Q_l` is a simple graph without isolated vertices." -/
theorem quotSimple : EG.Spec.QuotSimpleStatement := by
  intro V _ I hI R hR ξ
  refine ⟨fun e he e' he' q h h' => Rules.rank_inj hR he he' h h', ?_, ?_,
    fun a b hab => Quot.Rules.qEdge_tags hI hR hab, (R.Q ξ).loopless, R.Q_noIsolated ξ⟩
  · intro o ho w₁ w₂ h1 h2 heq
    subst heq
    exact ((Rules.mem_unpaidPar).1 ho).2 ⟨w₁, h1, h2⟩
  · intro it hit w hw
    have hH := ((Rules.mem_colouredHub).1 hit).1
    exact ⟨RoundInput.hubItems_hub hH, Rules.junction_pool hw,
      fun h => RoundInput.hubItems_hub_not_pool hH (h ▸ Rules.junction_pool hw)⟩

end EG
