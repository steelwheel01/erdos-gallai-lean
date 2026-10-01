module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Order.Lattice.Nat

/-!
# Iterated logarithms, the tower function and `log*` (manuscript s1:convGraphs (b), s2:lemLacunary)

PROTECTED FILE (`EG/Defs/**`): changes need the approval procedure in `APPROVALS/README.md`.

Manuscript text ([s1:convGraphs] (b)):
"`log = log₂` throughout, as in [BM, l. 141]. We put `log^{[0]} x := x` and
`log^{[k]} x := log(log^{[k-1]} x)`, and `log* x` is the least integer `k ≥ 0` with
`log^{[k]} x ≤ 1` [BM, l. 144–145]."

Manuscript text (proof of [s2:lemLacunary](iv)):
"Let `tw(0) := 1` and `tw(j+1) := 2^{tw(j)}`. Since `log^{[i]}` is increasing and
`log^{[j]} tw(j) = 1`, a real `z > 1` has `log* z = j` iff `tw(j-1) < z ≤ tw(j)`."

Formal counterparts (TRIAGE §2.3):
* `EG.logIter k x = log^{[k]} x`, the `k`-fold iterate of `Real.logb 2`;
* `EG.tower j = tw(j)` (a real number; `2^{tw j}` is `Real.rpow`);
* `EG.logStar x = log* x`, defined with `sInf` (so the definition contains no proof term).

Totality. `Real.logb 2` is total (`logb 2 0 = 0`, `logb 2 x = logb 2 |x|`), so `logIter` is
defined everywhere; the manuscript only iterates while the value stays `> 1`, where the Lean
iterate is the real iterated logarithm. For every real `x` some iterate is `≤ 1`
(`EG.exists_logIter_le_one`, in `EG/Lib/Found/Log.lean`), so the set in `logStar` is non-empty
and `sInf` is its least element (`Nat.sInf_mem`). (Were the set empty, `sInf ∅ = 0`; this never
happens.) API: `logStar_eq_zero_iff`, `logStar_of_one_lt`, `logStar_le_iff_le_tower`,
`logStar_two_rpow`, `logStar_le_self` in `EG/Lib/Found/Log.lean`.
-/

@[expose] public section


namespace EG

/-- [s1:convGraphs] (b) "We put `log^{[0]} x := x` and `log^{[k]} x := log(log^{[k-1]} x)`"
(`log = log₂`): the `k`-fold iterate of `Real.logb 2`. -/
noncomputable def logIter (k : ℕ) (x : ℝ) : ℝ := (Real.logb 2)^[k] x

/-- [s2:lemLacunary] (proof of (iv)) "Let `tw(0) := 1` and `tw(j+1) := 2^{tw(j)}`": the tower
function, real-valued (`2 ^ tower j` is `Real.rpow`; its values are natural numbers). -/
noncomputable def tower : ℕ → ℝ
  | 0 => 1
  | j + 1 => (2 : ℝ) ^ tower j

/-- [s1:convGraphs] (b) "`log* x` is the least integer `k ≥ 0` with `log^{[k]} x ≤ 1`".
Defined as `sInf {k | logIter k x ≤ 1}`; the set is non-empty for every real `x`
(`EG.exists_logIter_le_one`), so this is its least element. -/
noncomputable def logStar (x : ℝ) : ℕ := sInf {k : ℕ | logIter k x ≤ 1}

end EG
