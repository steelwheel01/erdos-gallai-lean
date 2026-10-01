import FormalConjectures.ErdosProblems.«184»
import EG.Proof.Main
import EGCheck.BridgeCore

/-!
# Bridge: internal main theorem ⇒ upstream `Erdos184.erdos_184` (thin FC-importing wrapper)

The only bridge file that imports `FormalConjectures.ErdosProblems.«184»`; it is imported by the
protected `EGCheck/Final.lean`. All the work is in the FC-184-free files
`EGCheck/BridgeLemmas.lean` and `EGCheck/BridgeCore.lean`, which comparator's
`formal/comparator/Solution.lean` imports as well (trust audits of 2026-09-26, §6 of
`APPROVALS/reviews/trust.opus.md`).

`of_mainInternal` turns `EGCheck.Bridge.of_mainInternal_unfolded` (the upstream statement with
the body of `IsCycleOrEdge` for arbitrary instances) into the upstream statement itself: the
kernel unfolds `Erdos184.IsCycleOrEdge` and instantiates the two instance arguments with the
(classical) instances of the upstream elaboration.

Phase P1 deliverable: `of_mainInternal` proved; `EG.Proof.mainInternal` may still be `sorry`.
-/

namespace EGCheck.Bridge

universe u

/-- The internal main theorem implies the upstream statement, with `f n = c * n`. -/
theorem of_mainInternal (h : EG.Spec.MainInternal) : type_of% @_root_.Erdos184.erdos_184.{u} := by
  obtain ⟨f, hf, hD⟩ := of_mainInternal_unfolded.{u} h
  exact ⟨f, hf, fun G => (hD G).imp fun _ hD => ⟨fun H hH => hD.1 H hH _ _, hD.2⟩⟩

theorem solution : type_of% @_root_.Erdos184.erdos_184.{u} :=
  of_mainInternal EG.Proof.mainInternal

end EGCheck.Bridge
