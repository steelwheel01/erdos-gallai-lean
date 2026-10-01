module

public import EG.Defs.Stage1.COL
public import EG.Proof.Chain.EngineMult

/-!
# Bridge from the numeric refutation target to `t^JS_l` (probe P-2, part 1)

`EG.Spec.JsMultNumStatement` writes `t = t^JS_l` as the literal `2M + 2`, because
`EG.Stage1.tJS G run l` depends on a run. This file links the two:
* `EG.tJS_eq_two_mul_add_two`: `tJS G run l = 2 * run.M G l + 2` ([s3:defCOL], "Also put
  `t^JS_l := 2M_l + 2`"; true by definition);
* `EG.jsMult_lt_tJS`: for `M_l ≥ 2`, `max(2M_l − 2, (M_l − 1) + ⌈M_l/2⌉) = 2M_l − 2 < t^JS_l`
  (joint-routing claim (c) of [s6:lemJSLC], numeric part, from `EG.jsMultNum`).

Probe unit P2E, fix round 1 (review R3); design note `formal/work/p2b/P2E.md`. The aggregated
multiplicity bound of claim (c) is a Spec of probe P-2 part 2.
-/

public section

namespace EG

/-- [s3:defCOL] (Derived quantities) "Also put `t^JS_l := 2M_l + 2`": the bridge from the literal
`2M + 2` of `EG.Spec.JsMultNumStatement` to `EG.Stage1.tJS`. -/
theorem tJS_eq_two_mul_add_two {V : Type*} [DecidableEq V] (G : FGraph V) (run : HB.Run V)
    (l : ℕ) : Stage1.tJS G run l = 2 * run.M G l + 2 := rfl

/-- [s6:lemJSLC:proof-claim-c] (proof of [s6:lemJSLC], joint-routing claim (c), numeric part,
stated with `t^JS_l`) "`max(2M_l − 2, (M_l − 1) + ⌈M_l/2⌉) = 2M_l − 2 ≤ t` ... For `M_l ≥ 2`
... both are at most `2M_l − 2 < t = 2M_l + 2`". -/
theorem jsMult_lt_tJS {V : Type*} [DecidableEq V] (G : FGraph V) (run : HB.Run V) (l : ℕ)
    (hM : 2 ≤ run.M G l) :
    max (2 * run.M G l - 2) ((run.M G l - 1) + ⌈(run.M G l : ℝ) / 2⌉₊) = 2 * run.M G l - 2 ∧
      2 * run.M G l - 2 < Stage1.tJS G run l := by
  obtain ⟨-, -, -, h4, h5⟩ := jsMultNum (run.M G l) hM
  exact ⟨h4, by rw [tJS_eq_two_mul_add_two]; exact h5⟩

end EG
