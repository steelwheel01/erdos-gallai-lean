module

public import EG.Defs.Quot.Xprime

/-!
# API for `X_V`, `ω_l(v)`, `X_pool`, `X'` (s7:lemVstar, s7:lemPay (a2), s7:defXprime)

Design note: `formal/work/p2d/quot.md`.
-/

public section

namespace EG.Quot

open EG.HB EG.Chain

variable {V : Type*} [DecidableEq V] (run : Run V) (G : FGraph V) (δ : Designation V)
  (S : StageData V)

theorem Xprime_eq (π : ↥G.verts → Option (ℕ × ℕ)) :
    Xprime run G δ S π = XU run G δ S + Xpool run G δ S π + XV run G π := rfl

theorem poolWeight_of_mem {l : ℕ} {v : V} (hv : v ∈ run.D G l) :
    poolWeight run G δ l v = cAgg run G δ v l := by
  simp [poolWeight, hv]

theorem poolWeight_of_not_mem {l : ℕ} {v : V} (hv : v ∉ run.D G l) :
    poolWeight run G δ l v = run.M G l := by
  simp [poolWeight, hv]

/-- [s7:lemVstar] "Each `X_{V,l}` is a deterministic function of the run and the pool labels":
definitional (`XVl` reads only `π`). -/
theorem XV_le_Xprime (π : ↥G.verts → Option (ℕ × ℕ)) : XV run G π ≤ Xprime run G δ S π := by
  unfold Xprime; omega

theorem Xpool_le_Xprime (π : ↥G.verts → Option (ℕ × ℕ)) :
    Xpool run G δ S π ≤ Xprime run G δ S π := by
  unfold Xprime; omega

theorem XU_le_Xprime (π : ↥G.verts → Option (ℕ × ℕ)) : XU run G δ S ≤ Xprime run G δ S π := by
  unfold Xprime; omega

open Classical in
theorem mem_jvBadPorts {π : ↥G.verts → Option (ℕ × ℕ)} {l : ℕ} {u : V} :
    u ∈ jvBadPorts run G δ S π l ↔ JVBad run G δ S π l u := by
  unfold jvBadPorts
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩

end EG.Quot
