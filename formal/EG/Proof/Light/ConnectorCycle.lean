module

public import EG.Spec.Light.ParentSteps
public import EG.Lib.Vortex.Trail

/-!
# Proof of the cycle claim of Lemma parent side (s5:lemParent, Step 7, Claim (cycles))

Proof file of probe unit P4B (probe P-4, part 2), proof round 1: `EG.connectorCycle`
(`ConnectorCycleStatement`). The closed walk `a_1 𝒞_1° a_2 𝒞_2° ⋯ a_k 𝒞_k°` has no repeated vertex
((1)–(3) of the TeX proof), its edges are the arc edges and the connector edges, and it has at
least three vertices (the case `k = 1` with two single edges is excluded by the edge-disjointness
of arcs and connectors, (F-c)). Design note `formal/work/p2b/P4B.md`.
-/

public section

namespace EG

namespace ConnCyc

variable {V : Type*}

/-- One segment: the arc `s.1` followed by the interior of its connector `s.2`, closed by the last
vertex `y` of the connector, has the edges of the arc and of the connector. -/
theorem walkEdges_seg (s : List V × List V) (y : V) (h1 : s.1 ≠ []) (h2 : 2 ≤ s.2.length)
    (hh : s.2.head? = s.1.getLast?) (hl : s.2.getLast? = some y) :
    walkEdges (s.1 ++ interior s.2 ++ [y]) = walkEdges s.1 ++ walkEdges s.2 := by
  obtain ⟨a, b⟩ := s
  simp only at h1 h2 hh hl ⊢
  rcases List.eq_nil_or_concat a with rfl | ⟨a', x, rfl⟩
  · exact absurd rfl h1
  match b, h2 with
  | u :: w :: rest, _ =>
    rcases List.eq_nil_or_concat (w :: rest) with h | ⟨m, y', hm⟩
    · simp at h
    · have hu : u = x := by simpa using hh
      have hy : y' = y := by
        rw [List.getLast?_cons, hm] at hl; simpa using hl
      subst hu hy
      have hint : interior (u :: w :: rest) = m := by
        simp [interior, hm]
      rw [hint, hm]
      simp only [List.concat_eq_append, List.append_assoc, List.cons_append]
      rw [walkEdges_append_cons]
      simp

/-- The segments along a list `x :: xs`, followed by `e` (whose arc starts at `z`): the walk
`x.1 x.2° … ` closed by `z` has the arc and connector edges of all segments. -/
theorem walkEdges_chain (e : List V × List V) (z : V) (he : e.1.head? = some z) :
    ∀ (x : List V × List V) (xs : List (List V × List V)),
      (∀ s ∈ x :: xs, s.1 ≠ [] ∧ 2 ≤ s.2.length) →
      (∀ p ∈ List.zip (x :: xs) (xs ++ [e]),
        p.1.2.head? = p.1.1.getLast? ∧ p.1.2.getLast? = p.2.1.head?) →
      walkEdges ((x :: xs).flatMap (fun s => s.1 ++ interior s.2) ++ [z]) =
        (x :: xs).flatMap (fun s => walkEdges s.1 ++ walkEdges s.2)
  | x, [], hs, hz => by
    have h := hz (x, e) (by simp)
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    exact walkEdges_seg x z (hs x (by simp)).1 (hs x (by simp)).2 h.1 (h.2.trans he)
  | x, y :: ys, hs, hz => by
    have ih := walkEdges_chain e z he y ys (fun s hs' => hs s (List.mem_cons_of_mem _ hs'))
      (fun p hp => hz p (by simp [List.zip_cons_cons, hp]))
    have hxy := hz (x, y) (by simp)
    obtain ⟨w, y1, hy1⟩ := List.exists_cons_of_ne_nil (hs y (by simp)).1
    have hT : (y :: ys).flatMap (fun s => s.1 ++ interior s.2) ++ [z] =
        w :: (y1 ++ interior y.2 ++ (ys.flatMap (fun s => s.1 ++ interior s.2) ++ [z])) := by
      simp [hy1]
    have hlast : x.2.getLast? = some w := by rw [hxy.2, hy1]; rfl
    rw [List.flatMap_cons, List.append_assoc, hT, walkEdges_append_cons, ← hT, ih,
      walkEdges_seg x w (hs x (by simp)).1 (hs x (by simp)).2 hxy.1 hlast]
    simp only [List.flatMap_cons, List.append_assoc]

theorem flatMap_append_perm {α γ : Type*} (l : List α) (f g : α → List γ) :
    (l.flatMap fun x => f x ++ g x).Perm (l.flatMap f ++ l.flatMap g) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.flatMap_cons, List.append_assoc]
    refine List.Perm.append_left _ ?_
    refine (List.Perm.append_left _ ih).trans ?_
    simp only [← List.append_assoc]
    exact List.Perm.append_right _ List.perm_append_comm

end ConnCyc

open ConnCyc

universe u

/-- [s5:lemParent] Step 7, Claim (cycles): "`C(𝒲)` is a cycle of `G` of length at least `3`",
with its edges exactly the arc edges and the connector edges (Step 8). -/
theorem connectorCycle : EG.Spec.ConnectorCycleStatement.{u} := by
  intro V _ segs hne hsz hcon harc hint hia hed
  obtain ⟨x, xs, rfl⟩ := List.exists_cons_of_ne_nil hne
  have hs : ∀ s ∈ x :: xs, s.1 ≠ [] ∧ 2 ≤ s.2.length := fun s hs' =>
    ⟨fun h => by have := (hsz s hs').2.1; simp [h] at this, (hsz s hs').2.2.2⟩
  obtain ⟨w0, x1, hx1⟩ := List.exists_cons_of_ne_nil (hs x (by simp)).1
  have hrot : (x :: xs).rotate 1 = xs ++ [x] := by
    rw [List.rotate_cons_succ, List.rotate_zero]
  rw [hrot] at hcon
  -- the edges
  have hC : (x :: xs).flatMap (fun s => s.1 ++ interior s.2) =
      w0 :: (x1 ++ interior x.2 ++ xs.flatMap (fun s => s.1 ++ interior s.2)) := by
    simp [hx1]
  have hedges : cycleEdges ((x :: xs).flatMap fun s => s.1 ++ interior s.2) =
      (x :: xs).flatMap fun s => walkEdges s.1 ++ walkEdges s.2 := by
    rw [hC, cycleEdges_cons, ← hC]
    exact walkEdges_chain x w0 (by rw [hx1]; rfl) x xs hs hcon
  refine ⟨⟨?_, ?_⟩, by rw [hedges]⟩
  · -- no repeated vertex
    refine List.Perm.nodup_iff (flatMap_append_perm _ _ _) |>.2 ?_
    rw [List.nodup_append]
    refine ⟨harc, hint, ?_⟩
    intro a ha b hb hab
    subst hab
    obtain ⟨s', hs', has'⟩ := List.mem_flatMap.1 ha
    obtain ⟨s, hs, has⟩ := List.mem_flatMap.1 hb
    exact hia s hs s' hs' a has has'
  · -- at least three vertices
    rcases xs with _ | ⟨y, ys⟩
    · have h1 := (hsz x (by simp)).2.1
      have h2 := (hsz x (by simp)).2.2.2
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_append]
      by_contra hlt
      have hlen1 : x.1.length = 2 := by
        have : (interior x.2).length + x.1.length < 3 := by omega
        omega
      have hlen2 : x.2.length = 2 := by
        have : (interior x.2).length = x.2.length - 2 := by simp [interior]; omega
        omega
      obtain ⟨a, b⟩ := x
      simp only at hlen1 hlen2 hcon hed
      match a, b, hlen1, hlen2 with
      | [a0, a1], [b0, b1], _, _ =>
        have hc := hcon (([a0, a1], [b0, b1]), ([a0, a1], [b0, b1])) (by simp)
        simp at hc
        obtain ⟨rfl, rfl⟩ := hc
        exact hed (a := s(b1, b0)) (by simp [walkEdges]) (by simp [walkEdges, Sym2.eq_swap])
    · have h1 := (hsz x (by simp)).2.1
      have h2 := (hsz y (by simp)).2.1
      simp only [List.flatMap_cons, List.length_append]
      omega

end EG
