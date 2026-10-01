module

public import EG.Defs.Quot.Round

/-!
# Statement of Lemma "Ultra-hub copies" (manuscript s7:lemUltra)

Statement file (`EG/Spec/**`), chunk s7a (P2 Specs). Status note: `formal/work/p2s/s7a.md`.
The identity "copies of `h` in colour `κ` = `max_w m_κ(h,w)`" used in (iii) is
`EG.Spec.MultSublayerStatement` (`EG/Spec/Quot/MULT.lean`).

Manuscript v6.1, `s7.tex`, Lemma [s7:lemUltra]:
"Let the past and the lists be fixed.
(i) Let `h` be an ultra hub, `κ ∈ [4M_l]`, and let `ω_1,…,ω_N` be the junctions of the coloured
hub items of `h` of colour `κ`. These items lie at `N` distinct ports, because distinct items at
`h` are distinct edges `hu` and `G` is simple. The `ω_i` are independent, and each is uniform on a
set of size at least `Hcd_l/2`.
(ii) If `N ≥ 1` then, with `μ* := 2N/Hcd_l`, `E[max_w m_κ(h,w) | Past_l, lists] ≤ log₂N + 2eμ* + 8`.
(iii) The number of vertices of HUB sub-layers that are copies of `h` satisfies
`E[· | Past_l, lists] ≤ 4M_l(log₂ c^live_h + 8) + 4e c^live_h/Hcd_l`.
(iv) Summed over all ultra hubs, the expected number of hub copies of ultra hubs, given `Past_l`
and the lists, is at most `320 nM_l^3 (log₂ θ^ult_l + 8)/λ_{l-2}^{95}`.
The bound depends on the past only through deterministic counts, so it holds for every past and
every realized `J_l`."
Proof of (i): "The junction of the item `(h,u_i)` is the image of its end under the uniformly
random injection at `u_i`, so it is uniform on `Cand_l(u_i) \ Used(u_i)`, a set of size at least
`Hcd_l/2` by Lemma s7:lemWellDef(v)."

Formal reading (TRIAGE §2.10; design note `work/p2d/quot.md`, "Notes for Spec authors").
* "For every past" is `∀ I : RoundInput V, I.Valid → ∀ R : Rules I, R.Valid`; "the lists are
  fixed" is a parameter `L : Lists I.G I.M`; the orders are random with law `ordersLaw I.G`, and
  `E[· | Past_l, lists]` is `(ordersLaw I.G).expect (fun O => X (L, O))`.
* "`h` an ultra hub" is `h ∈ D_l = I.hubs` with `I.ultra h` (`c^live_h > θ^ult_l`); HUB colours are
  naturals `κ < 4 * I.M`. The coloured hub items of `h` of colour `κ` are the items `it = (h, u)`
  of `R.colouredHub L` with `R.hubColour L it = some κ` (`ultraItems`); `N` is their number; the
  junction of `(h, u)` is `R.junction (L, O) (.hub h u)` (`Option V`, assigned in (e2) since `h`
  is ultra).
* (i) "lie at `N` distinct ports" is injectivity of `(h,u) ↦ u` on these items; "independent" is
  `FinDist.iIndepFun` under `ordersLaw`; "uniform on a set of size at least `Hcd_l/2`" is stated
  with the set of the proof, `C(u) = Cand_l(u) \ Used(u)` (`I.cand u \ R.used L u`, `Used` after
  (e1)): `|C(u)| ≥ Hcd_l/2` and `P(junction = w) = 1/|C(u)|` for `w ∈ C(u)`, `0` otherwise.
* (ii) `max_w m_κ(h,w)` is the maximum over `w ∈ Pool_l` (`Finset.sup` over `I.pool`, as in
  `MultSublayerStatement`), `m_κ(h,w) = R.mHub (L, O) κ h w`; `log₂ = Real.logb 2`, `e = Real.exp 1`.
* (iii) "the vertices of HUB sub-layers that are copies of `h`" are the vertices of
  `R.Q (L, O)` whose tag has kind `true` (HUB) and side `true` (hub copy) and whose vertex is `h`
  (`hubCopies`); junction copies `[w]` are copies of pooled vertices, never of a hub with a live
  item (Lemma s7:lemLift (i), `Live ∩ Pool_l = ∅`). `c^live_h = I.clive h`.
* (iv) "Summed over all ultra hubs": the sum of `hubCopies` over the hubs `h ∈ I.hubs` with
  `θ^ult_l < c^live_h` (this filter predicate is the body of `I.ultra h`, written out so that the
  `Finset.filter` uses the standard `Nat` decidability instance); `n = I.G.card`,
  `θ^ult_l = I.thult`, `λ_{l-2} = I.lam`. This is the form the consumer s7:lemUHsplit (ii)
  (chunk s7b) needs: a bound for every value of the lists (UH-AVERAGE-LISTS).
-/

@[expose] public section

namespace EG.Spec

open EG.Quot

section helpers

variable {V : Type*} [DecidableEq V] {I : RoundInput V}

/-- [s7:lemUltra] (i) "the coloured hub items of `h` of colour `κ`" (for the lists `L`). -/
noncomputable def ultraItems (R : Rules I) (L : Lists I.G I.M) (h : V) (κ : ℕ) : Finset (V × V) :=
  (R.colouredHub L).filter (fun it => it.1 = h ∧ R.hubColour L it = some κ)

/-- [s7:lemUltra] (iii) "the number of vertices of HUB sub-layers that are copies of `h`": the
vertices of `Q_l` with a HUB tag, on the hub side, whose vertex is `h`. -/
noncomputable def hubCopies (R : Rules I) (ξ : Xi I.G I.M) (h : V) : ℕ :=
  ((R.Q ξ).verts.filter (fun q => q.1.1 = true ∧ q.1.2.2.2 = true ∧ q.2 = h)).card

end helpers

/-- [s7:lemUltra] (i) "Let the past and the lists be fixed. Let `h` be an ultra hub, `κ ∈ [4M_l]`,
and let `ω_1,…,ω_N` be the junctions of the coloured hub items of `h` of colour `κ`. These items
lie at `N` distinct ports, because distinct items at `h` are distinct edges `hu` and `G` is simple.
The `ω_i` are independent, and each is uniform on a set of size at least `Hcd_l/2`." (The set is
`Cand_l(u_i) \ Used(u_i)`, as in the proof.) -/
def UltraIndepStatement : Prop :=
  ∀ (V : Type) [DecidableEq V] (I : RoundInput V), I.Valid → ∀ R : Rules I, R.Valid →
    ∀ (L : Lists I.G I.M) (h : V) (κ : ℕ), h ∈ I.hubs → I.ultra h → κ < 4 * I.M →
      Set.InjOn Prod.snd (ultraItems R L h κ : Set (V × V)) ∧
      (ordersLaw I.G).iIndepFun
        (fun (it : ↥(ultraItems R L h κ)) (O : Orders I.G) =>
          R.junction (L, O) (.hub (it : V × V).1 (it : V × V).2)) ∧
      ∀ it ∈ ultraItems R L h κ,
        I.Hcd / 2 ≤ ((I.cand it.2 \ R.used L it.2).card : ℝ) ∧
        ∀ w : V, (ordersLaw I.G).prob {O | R.junction (L, O) (.hub it.1 it.2) = some w} =
          (if w ∈ I.cand it.2 \ R.used L it.2
            then 1 / ((I.cand it.2 \ R.used L it.2).card : ℝ) else 0)

/-- [s7:lemUltra] (ii) "If `N ≥ 1` then, with `μ* := 2N/Hcd_l`,
`E[max_w m_κ(h,w) | Past_l, lists] ≤ log₂N + 2eμ* + 8`." (`h` an ultra hub, `κ ∈ [4M_l]`, `N` the
number of coloured hub items of `h` of colour `κ`.) -/
def UltraMaxStatement : Prop :=
  ∀ (V : Type) [DecidableEq V] (I : RoundInput V), I.Valid → ∀ R : Rules I, R.Valid →
    ∀ (L : Lists I.G I.M) (h : V) (κ : ℕ), h ∈ I.hubs → I.ultra h → κ < 4 * I.M →
      1 ≤ (ultraItems R L h κ).card →
      (ordersLaw I.G).expect (fun O => ((I.pool.sup (fun w => R.mHub (L, O) κ h w) : ℕ) : ℝ)) ≤
        Real.logb 2 ((ultraItems R L h κ).card : ℝ) +
          2 * Real.exp 1 * (2 * ((ultraItems R L h κ).card : ℝ) / I.Hcd) + 8

/-- [s7:lemUltra] (iii) "The number of vertices of HUB sub-layers that are copies of `h` satisfies
`E[· | Past_l, lists] ≤ 4M_l(log₂ c^live_h + 8) + 4e c^live_h/Hcd_l`." (`h` an ultra hub.) -/
def UltraCopiesStatement : Prop :=
  ∀ (V : Type) [DecidableEq V] (I : RoundInput V), I.Valid → ∀ R : Rules I, R.Valid →
    ∀ (L : Lists I.G I.M) (h : V), h ∈ I.hubs → I.ultra h →
      (ordersLaw I.G).expect (fun O => (hubCopies R (L, O) h : ℝ)) ≤
        4 * (I.M : ℝ) * (Real.logb 2 (I.clive h : ℝ) + 8) +
          4 * Real.exp 1 * (I.clive h : ℝ) / I.Hcd

/-- [s7:lemUltra] (iv) "Summed over all ultra hubs, the expected number of hub copies of ultra hubs,
given `Past_l` and the lists, is at most `320 nM_l^3 (log₂ θ^ult_l + 8)/λ_{l-2}^{95}`. The bound
depends on the past only through deterministic counts, so it holds for every past and every
realized `J_l`." -/
def UltraSumStatement : Prop :=
  ∀ (V : Type) [DecidableEq V] (I : RoundInput V), I.Valid → ∀ R : Rules I, R.Valid →
    ∀ L : Lists I.G I.M,
      (ordersLaw I.G).expect (fun O =>
          ∑ h ∈ I.hubs.filter (fun h => I.thult < I.clive h), (hubCopies R (L, O) h : ℝ)) ≤
        320 * ((I.G.card : ℝ) * (I.M : ℝ) ^ 3 * (Real.logb 2 (I.thult : ℝ) + 8)) / I.lam ^ 95

end EG.Spec
