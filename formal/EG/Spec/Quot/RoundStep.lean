module

public import EG.Defs.Quot.Round

/-!
# The claims made inside Construction "The JV⁺* round step" (manuscript s7:consRound)

Statement file (`EG/Spec/**`), chunk s7a (P2 Specs). Status note: `formal/work/p2s/s7a.md`.
The construction itself is the locked Defs of `EG/Defs/Quot/Round.lean` (`RoundInput`,
`RoundInput.Valid`, `Rules`, `Rules.Valid`, the steps (a)–(h)) and `EG/Defs/Quot/Schedule.lean`
(`Lists`, `Orders`, `listsLaw`, `ordersLaw`, `roundLaw`). Its well-definedness claims are Lemma
s7:lemWellDef (`EG/Spec/Quot/WellDef.lean`); its claims "`Live ∩ Pool_l = ∅`" and "every port
carries at most one coloured hub item of each HUB colour" are Lemma s7:lemLift (i)
(`EG/Spec/Quot/Lift.lean`). This file states the remaining claims of the construction text that
have mathematical content:

Manuscript v6.1, `s7.tex`, Construction [s7:consRound]:
* *Fixed rules*: "Rules with these arguments exist, for instance lexicographically first choices
  for fixed orders of the finite sets involved (the greedy colouring of (b) succeeds for every
  order, by part (i) of the next lemma, and a split into groups as in (c) always exists)."
* (c): "For a non-ultra `h` with `c^live_h ≥ 1`, its live items are split, by a fixed rule, into
  `k_h := ⌈8c^live_h/Hcd_l⌉` groups of at most `⌈Hcd_l/8⌉` items each. This is possible because
  `k_h⌈Hcd_l/8⌉ ≥ c^live_h`. The `i`-th group receives the list
  `{η_h(3i−2), η_h(3i−1), η_h(3i)} ⊆ [4M_l]` … The lists of the groups of `h` are pairwise
  disjoint, and, since the groups and their numbering are functions of `Past_l` while `η_h` is
  independent of `Past_l`, they form a uniformly random sequence of `k_h` pairwise disjoint
  `3`-subsets of `[4M_l]`. Lists of distinct hubs are independent. For an ultra `h`, every live
  item `(h,u)` is its own group, with list `ζ_{h,u}`."
* (e2): "With `Past_l` and the lists fixed, the map `e_i ↦ w_i` is a uniformly random injection of
  `E'(u)` into `Cand_l(u) \ Used(u)`, and these injections are independent over ports: by the
  restrictions on the fixed rules, `Used(u)`, the set `E'(u)` and its order `e_1,…,e_q` are
  determined by `Past_l` and the lists, and the orders `≺_u` are independent of both."
* (f): "By Markov's inequality in the form (b) of Cited result s1:citMarkov, taken conditionally as
  in its item (c) …, this event has probability at least `1/2` given `Past_l` (each of the two
  events fails with probability at most `1/4`)."

Formal reading (TRIAGE §2.10; design note `work/p2d/quot.md`).
* "For every past" is `∀ I : RoundInput V, I.Valid` and, where a rule is involved, `∀ R : Rules I,
  R.Valid` (the argument restrictions of the fixed rules are the argument types of the fields of
  `Rules`). "Rules with these arguments exist" is `∃ R : Rules I, R.Valid` (the Defs docstring of
  `RoundInput.chosenRules` calls this `Rules.exists_valid`; `Rules.Valid` also asks the rule of (h)
  to return a decomposition into `f(Q_l)` objects, and the other rules to list exactly the finite
  sets they order).
* (c) The groups are 0-based: group `i` (`0 ≤ i < k_h`) receives `listOf η_h i =
  {η_h(3i), η_h(3i+1), η_h(3i+2)}` (TeX, 1-based: `{η_h(3i−2), η_h(3i−1), η_h(3i)}`), as a set of
  naturals `< 4M_l`; `η_h = etaAt L h`. "A uniformly random sequence of `k_h` pairwise disjoint
  `3`-subsets of `[4M_l]`" is: every such sequence `(A_i)_{i<k_h}` has probability
  `6^{k_h} / (4M_l)_{3k_h}` (falling factorial; the number of such sequences is
  `(4M_l)_{3k_h}/6^{k_h}`, so this is the uniform law on them). "Lists of distinct hubs are
  independent" is `iIndepFun` under `listsLaw` of the family indexed by the hubs `h ∈ D_l` of the
  list maps `u ↦ R.hubList L (h, u)` (the list of the item `(h,u)`: from `η_h` if `h` is non-ultra,
  `ζ_{h,u}` if `h` is ultra); this is stated for every hub, ultra or not, which covers both
  sentences ("Lists of distinct hubs are independent", "every live item `(h,u)` is its own group,
  with list `ζ_{h,u}`").
* (e2) "Past and lists fixed" is a parameter `L : Lists I.G I.M`; the orders are random with law
  `ordersLaw I.G`. "A uniformly random injection of `E'(u)` into `C(u) := Cand_l(u) \ Used(u)`" is:
  for every injective map `f : E'(u) → C(u)`, the probability that every end `e ∈ E'(u)` receives
  the junction `f e` in (e2) (`R.e2Junc (L, O) e = some (f e)`) is `1 / (|C(u)|)_{|E'(u)|}`
  (falling factorial; the number of such injections). This is stated at every port `u ∈ I.ports`
  (at a port without live items `E'(u) = ∅` and the claim is the trivial one). "Independent over
  ports" is `iIndepFun` of the family indexed by `u ∈ I.ports` of the junction maps
  `e ↦ R.e2Junc (L, O) e` on `E'(u)`. `Used(u)` is the value after (e1), `R.used L u`.
* (f) `E[·|Past_l]` is the expectation under `roundLaw I.G I.M`; "fails" is the negation of the
  inequality of the event (`copies_l > 4E[copies_l|Past_l]`, resp. for `pay^rd_l`), and the event
  is `R.MarkovEvent`. The Defs choice `Rules.xiChosen` relies on this event having positive
  probability (the consumer-level existence statement is `OneOutcomeRoundStatement`, chunk s7b).
-/

@[expose] public section

namespace EG.Spec

open EG.Quot

/-- [s7:consRound] *Fixed rules*: "Rules with these arguments exist, for instance
lexicographically first choices for fixed orders of the finite sets involved (the greedy colouring
of (b) succeeds for every order, by part (i) of the next lemma, and a split into groups as in (c)
always exists)." With (c): "This is possible because `k_h⌈Hcd_l/8⌉ ≥ c^live_h`." -/
def RoundRulesExistStatement : Prop :=
  ∀ (V : Type) [DecidableEq V] (I : RoundInput V), I.Valid →
    (∀ h ∈ I.hubs, ¬ I.ultra h → 1 ≤ I.clive h → I.clive h ≤ I.kh h * I.groupCap) ∧
    ∃ R : Rules I, R.Valid

/-- [s7:consRound] (c) "The lists of the groups of `h` are pairwise disjoint, and, since the
groups and their numbering are functions of `Past_l` while `η_h` is independent of `Past_l`, they
form a uniformly random sequence of `k_h` pairwise disjoint `3`-subsets of `[4M_l]`. Lists of
distinct hubs are independent. For an ultra `h`, every live item `(h,u)` is its own group, with list
`ζ_{h,u}`." (Groups 0-based; `listOf η i = {η(3i), η(3i+1), η(3i+2)}`.) -/
def RoundListsLawStatement : Prop :=
  ∀ (V : Type) [DecidableEq V] (I : RoundInput V), I.Valid →
    (∀ h ∈ I.hubs, ¬ I.ultra h → 1 ≤ I.clive h →
      -- the lists of the groups of `h` are pairwise disjoint `3`-subsets of `[4M_l]`
      (∀ L : Lists I.G I.M, ∀ i < I.kh h,
          listOf (etaAt L h) i ⊆ Finset.range (4 * I.M) ∧ (listOf (etaAt L h) i).card = 3 ∧
          ∀ j < I.kh h, i ≠ j → Disjoint (listOf (etaAt L h) i) (listOf (etaAt L h) j)) ∧
      -- … and form a uniformly random sequence of `k_h` pairwise disjoint `3`-subsets
      ∀ A : ℕ → Finset ℕ,
        (∀ i < I.kh h, A i ⊆ Finset.range (4 * I.M) ∧ (A i).card = 3) →
        (∀ i < I.kh h, ∀ j < I.kh h, i ≠ j → Disjoint (A i) (A j)) →
          (listsLaw I.G I.M).prob {L | ∀ i < I.kh h, listOf (etaAt L h) i = A i} =
            (6 : ℝ) ^ I.kh h / ((4 * I.M).descFactorial (3 * I.kh h) : ℝ)) ∧
    -- lists of distinct hubs are independent (`ζ_{h,u}` for ultra `h`, from `η_h` otherwise)
    ∀ R : Rules I, R.Valid →
      (listsLaw I.G I.M).iIndepFun
        (fun (h : ↥I.hubs) (L : Lists I.G I.M) => fun u : V => R.hubList L ((h : V), u))

/-- [s7:consRound] (e2) "With `Past_l` and the lists fixed, the map `e_i ↦ w_i` is a uniformly
random injection of `E'(u)` into `Cand_l(u) \ Used(u)`, and these injections are independent over
ports". -/
def RoundInjectionStatement : Prop :=
  ∀ (V : Type) [DecidableEq V] (I : RoundInput V), I.Valid → ∀ R : Rules I, R.Valid →
    ∀ L : Lists I.G I.M,
      -- a uniformly random injection of `E'(u)` into `Cand_l(u) \ Used(u)`
      (∀ u ∈ I.ports, ∀ f : REnd V → V,
          Set.MapsTo f (R.E' L u : Set (REnd V)) (I.cand u \ R.used L u : Set V) →
          Set.InjOn f (R.E' L u : Set (REnd V)) →
            (ordersLaw I.G).prob {O | ∀ e ∈ R.E' L u, R.e2Junc (L, O) e = some (f e)} =
              (((I.cand u \ R.used L u).card.descFactorial (R.E' L u).card : ℕ) : ℝ)⁻¹) ∧
      -- independent over ports
      (ordersLaw I.G).iIndepFun
        (fun (u : ↥I.ports) (O : Orders I.G) =>
          fun e : ↥(R.E' L (u : V)) => R.e2Junc (L, O) (e : REnd V))

/-- [s7:consRound] (f) "The round randomness `ξ_l` is chosen in the event
`{copies_l ≤ 4E[copies_l|Past_l]} ∩ {pay^rd_l ≤ 4E[pay^rd_l|Past_l]}`. By Markov's inequality …,
this event has probability at least `1/2` given `Past_l` (each of the two events fails with
probability at most `1/4`)." -/
def RoundMarkovStatement : Prop :=
  ∀ (V : Type) [DecidableEq V] (I : RoundInput V), I.Valid → ∀ R : Rules I, R.Valid →
    (roundLaw I.G I.M).prob {ξ | ¬ (R.copies ξ : ℝ) ≤
        4 * (roundLaw I.G I.M).expect (fun ξ' => (R.copies ξ' : ℝ))} ≤ 1 / 4 ∧
    (roundLaw I.G I.M).prob {ξ | ¬ (R.payrd ξ : ℝ) ≤
        4 * (roundLaw I.G I.M).expect (fun ξ' => (R.payrd ξ' : ℝ))} ≤ 1 / 4 ∧
    1 / 2 ≤ (roundLaw I.G I.M).prob {ξ | R.MarkovEvent ξ}

end EG.Spec
