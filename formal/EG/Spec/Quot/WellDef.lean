module

public import EG.Defs.Quot.Round

/-!
# Statement of Lemma "The round step is well defined" (manuscript s7:lemWellDef) — probe P-1

Statement file (`EG/Spec/**`), unit P1 (probe P-1). Design note: `formal/work/p2b/P1.md`. Proofs
(stage 2): `EG/Proof/Quot/WellDef.lean` (parts (i), (ii), (iv), (v)) and
`EG/Proof/Quot/Cuckoo.lean` (part (iii); the series bound is the proved
`EG.Spec.NumWellDefSDRUseStatement` of unit NUM, `EG/Spec/Num/WellDef.lean`).

Manuscript v6.1, `s7.tex`, Lemma [s7:lemWellDef]:
"For every past `Past_l` (`3 ≤ l ≤ R`) the following hold.
(i) *PAR palette.* Every PAR object shares a port or a middle with fewer than `3M_l` other PAR
objects, so the greedy colouring of (b) succeeds. Consequently every port carries at most one PAR
object of each colour, and every fresh centre is the middle of at most one cherry of each colour.
(ii) *Disjoint lists.* Every non-ultra hub `h` has `k_h ≤ ⌈8M_l/7⌉` and `3k_h ≤ 4M_l`.
(iii) *Cuckoo SDR.* For every port `u`, `P(SDR failure at u | Past_l) ≤ (K^HUB_l)^{-4} = (4M_l)^{-4}`.
(iv) *Greedy step.* Step (e1) always finds a junction. Two coloured items of the same non-ultra hub
`h` with the same colour `κ` receive distinct junctions.
(v) *Injections.* At every port `u` carrying a live item,
`|Cand_l(u) \ Used(u)| ≥ Hcd_l − (M_l − 1) ≥ Hcd_l/2 ≥ M_l > |E'(u)|`, so step (e2) is well
defined."

Formal reading (TRIAGE §2.10; design note `work/p2d/quot.md` D-Q-4 to D-Q-9).
* "For every past" is `∀ I : RoundInput V, I.Valid → ∀ R : Rules I, R.Valid`: `I.Valid` carries
  (J1)–(J3) of s6:lemJplus, `M_l ≥ 2^40`, `Hcd_l ≥ 2^10 M_l^10` and "JV-good ⇒ `|Cand_l(u)| ≥ Hcd_l`"
  (s7:lemCand(iv)); J⁺ is assumed (probe P-1). The statements hold for every admissible choice of
  the fixed rules ("Every statement of this section about the round step holds for every choice of
  the fixed rules that obeys these restrictions", s7:consRound *Fixed rules*).
* The construction is total (D-Q-6): "the greedy colouring succeeds", "(e1) always finds a
  junction" and "(e2) is well defined" are stated as "no fallback is taken": every PAR object gets a
  colour `κ < 3M_l`; every coloured hub item of a non-ultra hub gets an (e1) junction, a candidate
  of its port; every end in `E'(u)` gets an (e2) junction in `Cand_l(u) \ Used(u)`.
* (i) "shares a port or a middle" is `ParObj.Conflict`; "carries at most one PAR object of each
  colour" counts the PAR objects with an end at the port.
* (ii) "`k_h`" is `I.kh h = ⌈8 c^live_h / Hcd_l⌉₊`; `⌈8M_l/7⌉` is the natural ceiling of the real
  `8M_l/7`. "Every non-ultra hub": `h ∈ D_l = I.hubs` with `¬ I.ultra h`.
* (iii) The probability is over `ξ_l ∼ roundLaw I.G I.M` with the past `I` fixed
  (`P(·|Past_l)`, s7:defSchedule; the past is a parameter). "SDR failure at `u`" is
  `¬ R.SDRExists ξ.1 u` (no system of distinct representatives for the live hub items of `u`);
  `K^HUB_l = I.KHUB = 4M_l`, and `(K)^{-4}` is the integer power `(K : ℝ) ^ (-4 : ℤ)`.
* (iv) is stated for every value of the lists `L` (the only part of `ξ_l` that (e1) reads):
  `(R.e1State L).junc it` is the (e1) junction of the item `it`; the items processed in (e1) are
  `R.e1Items L` (the coloured hub items of non-ultra hubs).
* (v) "`u` carrying a live item" is `u ∈ I.ports ∧ ∃ e ∈ I.live, u ∈ e`; `Used(u)` is the value
  after (e1), `R.used ξ.1 u`; the real inequalities use the casts of the natural numbers; the
  junction of an end `e ∈ E'(u)` in (e2) is `R.e2Junc ξ e`.
-/

@[expose] public section

namespace EG.Spec

open EG.Quot

/-- [s7:lemWellDef] (i) *PAR palette.* "Every PAR object shares a port or a middle with fewer than
`3M_l` other PAR objects, so the greedy colouring of (b) succeeds. Consequently every port carries
at most one PAR object of each colour, and every fresh centre is the middle of at most one cherry
of each colour." -/
def WellDefParStatement : Prop :=
  ∀ (V : Type) [DecidableEq V] (I : RoundInput V), I.Valid → ∀ R : Rules I, R.Valid →
    -- `ParObj.Conflict` is a `Prop` without a `Decidable` instance: classical filter, scoped to
    -- this conjunct only, so that conjuncts (3), (4) elaborate with the same (non-classical)
    -- instances as `LiftRolesStatement` (fix round 1, review issue C3)
    (∀ o ∈ R.parObjs, (open Classical in
        (R.parObjs.erase o).filter (fun o' => ParObj.Conflict o o')).card < 3 * I.M) ∧
    (∀ o ∈ R.parObjs, ∃ κ, κ < 3 * I.M ∧ R.parColour o = some κ) ∧
    -- (3), (4) quantify over every vertex `u` / `x`, not only over ports / fresh centres: stronger
    -- than the TeX and still true, since only ports are ends and only fresh centres are middles
    -- of PAR objects (second review of P1, cosmetic C2)
    (∀ (u : V) (κ : ℕ),
        (R.parObjs.filter (fun o => (∃ b, o.endAt b = u) ∧ R.parColour o = some κ)).card ≤ 1) ∧
    (∀ (x : V) (κ : ℕ),
        (R.parObjs.filter (fun o => o.middle = some x ∧ R.parColour o = some κ)).card ≤ 1)

/-- [s7:lemWellDef] (ii) *Disjoint lists.* "Every non-ultra hub `h` has `k_h ≤ ⌈8M_l/7⌉` and
`3k_h ≤ 4M_l`." -/
def WellDefListsStatement : Prop :=
  ∀ (V : Type) [DecidableEq V] (I : RoundInput V), I.Valid →
    ∀ h ∈ I.hubs, ¬ I.ultra h →
      I.kh h ≤ ⌈8 * (I.M : ℝ) / 7⌉₊ ∧ 3 * I.kh h ≤ 4 * I.M

/-- [s7:lemWellDef] (iii) *Cuckoo SDR.* "For every port `u`,
`P(SDR failure at u | Past_l) ≤ (K^HUB_l)^{-4} = (4M_l)^{-4}`." -/
def CuckooSDRStatement : Prop :=
  ∀ (V : Type) [DecidableEq V] (I : RoundInput V), I.Valid → ∀ R : Rules I, R.Valid →
    ∀ u ∈ I.ports,
      (roundLaw I.G I.M).prob {ξ | ¬ R.SDRExists ξ.1 u} ≤ (I.KHUB : ℝ) ^ (-4 : ℤ)

/-- [s7:lemWellDef] (iv) *Greedy step.* "Step (e1) always finds a junction. Two coloured items of
the same non-ultra hub `h` with the same colour `κ` receive distinct junctions." (For every value
`L` of the lists.) -/
def WellDefE1Statement : Prop :=
  ∀ (V : Type) [DecidableEq V] (I : RoundInput V), I.Valid → ∀ R : Rules I, R.Valid →
    ∀ L : Lists I.G I.M,
      (∀ it ∈ R.e1Items L, ∃ w, (R.e1State L).junc it = some w ∧ w ∈ I.cand it.2) ∧
      (∀ it ∈ R.e1Items L, ∀ it' ∈ R.e1Items L, it ≠ it' → it.1 = it'.1 →
          R.hubColour L it = R.hubColour L it' →
          (R.e1State L).junc it ≠ (R.e1State L).junc it')

/-- [s7:lemWellDef] (v) *Injections.* "At every port `u` carrying a live item,
`|Cand_l(u) \ Used(u)| ≥ Hcd_l − (M_l − 1) ≥ Hcd_l/2 ≥ M_l > |E'(u)|`, so step (e2) is well
defined." -/
def WellDefE2Statement : Prop :=
  ∀ (V : Type) [DecidableEq V] (I : RoundInput V), I.Valid → ∀ R : Rules I, R.Valid →
    ∀ (ξ : Xi I.G I.M) (u : V), u ∈ I.ports → (∃ e ∈ I.live, u ∈ e) →
      I.Hcd - ((I.M : ℝ) - 1) ≤ ((I.cand u \ R.used ξ.1 u).card : ℝ) ∧
      I.Hcd / 2 ≤ I.Hcd - ((I.M : ℝ) - 1) ∧
      (I.M : ℝ) ≤ I.Hcd / 2 ∧
      (R.E' ξ.1 u).card < I.M ∧
      ∀ e ∈ R.E' ξ.1 u, ∃ w, R.e2Junc ξ e = some w ∧ w ∈ I.cand u \ R.used ξ.1 u

end EG.Spec
