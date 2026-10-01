module

public import EG.Defs.Quot.Xprime

/-!
# The numeric facts of Lemma CC (iii) and Lemma UH*-split (ii) (manuscript s7)

Statement file (`EG/Spec/**`), unit NUM (cheap numeric probes, TRIAGE §4). Proofs:
`EG/Proof/Num/CC.lean`. Design note: `formal/work/p2b/NUM.md`.

Manuscript v6.1, `s7.tex`, proof of Lemma [s7:lemCC] (iii) ("Lemma CC: PAR copies"):
"The number of PAR copies is `∑_{κ∈[3M_l]} ∑_{w∈Pool_l} max_{w'} m_κ(w,w')`. Averaging (ii) over
the indicators and summing over the at most `3M_l|Pool_l|` pairs `(κ,w)` gives at most
`3M_l t |Pool_l| + (6e/H^{cd}_l + 4e2^{−t}) E∑_{κ,w}|S_w|`. Every PAR object lies in at most two
of the sets `S_w` (one for each end), so `∑_{κ,w}|S_w| ≤ 2·1.37nM_l = 2.74nM_l`. With `t = t^CC_l`
we have `2^{−t} ≤ M_l^{−2}`, and `6e·2.74 < 44.7` and `4e·2.74 < 29.8`. Finally `t ≤ t+1`."
and the statement (iii): "With `t := t^CC_l := ⌈2log₂M_l⌉`, […]
`E[#{PAR copies} | Past_l, lists] ≤ 3M_l(t^CC_l+1)|Pool_l| + 44.7 nM_l/H^{cd}_l + 29.8 n/M_l`."

Proof of Lemma [s7:lemUHsplit] (ii): "`∑_{h:c^live_h≥1} 3k_h ≤ … ≤ 3|D_l| + 24·1.37nM_l/H^{cd}_l`,
since `∑_h c^live_h ≤ 1.37nM_l`. Here `24·1.37 = 32.88 < 32.9`." and "The remaining terms add up
to at most `det_l`, because `44.7+32.9 ≤ 78` and `29.8 ≤ 30`."

`t^CC` is the shared constant `EG.Quot.tCC M = ⌈2 log₂ M⌉₊` (`EG/Defs/Quot/Xprime.lean`). The
thin constants: `6e·2.74 < 44.7` and `4e·2.74 < 29.8` both need `e < 2.71897…` (true value
`2.71828…`; slack 0.025%); `Real.exp_one_lt_d9` gives `e < 2.7182818286`.
-/

@[expose] public section


namespace EG.Spec

/-- [s7:lemCC] (iii), proof: "`∑_{κ,w}|S_w| ≤ 2·1.37nM_l = 2.74nM_l`" and "`6e·2.74 < 44.7` and
`4e·2.74 < 29.8`" (values `44.688…` and `29.792…`). -/
def NumCCConstStatement : Prop :=
  2 * (1.37 : ℝ) = 2.74 ∧ 6 * Real.exp 1 * 2.74 < 44.7 ∧ 4 * Real.exp 1 * 2.74 < 29.8

/-- [s7:lemCC] (iii), proof: "With `t = t^CC_l` we have `2^{−t} ≤ M_l^{−2}`", for
`t^CC_l = ⌈2log₂M_l⌉` and every natural `M_l ≥ 1` (in the manuscript `M_l ≥ 2^{40}`). -/
def NumCCTwoPowStatement : Prop :=
  ∀ M : ℕ, 1 ≤ M → (2 : ℝ) ^ (-(Quot.tCC M : ℤ)) ≤ (M : ℝ) ^ (-2 : ℤ)

/-- [s7:lemCC] (iii), the final computation: from the bound
`3M_l t|Pool_l| + (6e/H^{cd}_l + 4e2^{−t}) E∑|S_w|` with `t = t^CC_l` and
`E∑|S_w| ≤ 2.74nM_l`, the bound `3M_l(t^CC_l+1)|Pool_l| + 44.7nM_l/H^{cd}_l + 29.8n/M_l`.
Here `M = M_l ≥ 1`, `H = H^{cd}_l > 0`, `P = |Pool_l| ≥ 0` and `S = E∑_{κ,w}|S_w| ≥ 0`. -/
def NumCCCombineStatement : Prop :=
  ∀ (M : ℕ) (n H P S : ℝ), 1 ≤ M → 0 < H → 0 ≤ P → 0 ≤ S → S ≤ 2.74 * n * M →
    3 * (M : ℝ) * (Quot.tCC M : ℝ) * P +
        (6 * Real.exp 1 / H + 4 * Real.exp 1 * (2 : ℝ) ^ (-(Quot.tCC M : ℤ))) * S ≤
      3 * (M : ℝ) * ((Quot.tCC M : ℝ) + 1) * P + 44.7 * n * M / H + 29.8 * n / M

/-- [s7:lemUHsplit] (ii), proof: "Here `24·1.37 = 32.88 < 32.9`" and "because `44.7+32.9 ≤ 78`
and `29.8 ≤ 30`". -/
def NumUHsplitConstStatement : Prop :=
  24 * (1.37 : ℝ) = 32.88 ∧ (32.88 : ℝ) < 32.9 ∧ (44.7 : ℝ) + 32.9 ≤ 78 ∧ (29.8 : ℝ) ≤ 30

end EG.Spec
