module

public import EG.Defs.Quot.Round
public import EG.Defs.Quot.Xprime

/-!
# Statement of Lemma CC: PAR copies (manuscript s7:lemCC)

Statement file (`EG/Spec/**`), chunk s7a (P2 Specs). Status note: `formal/work/p2s/s7a.md`.
The numeric facts of the proof of (iii) are the proved `EG.Spec.NumCC*Statement`
(`EG/Spec/Num/CC.lean`); the PAR-MULT identity used in (iii) is `EG.Spec.ParMultSublayerStatement`
(`EG/Spec/Quot/MULT.lean`).

Manuscript v6.1, `s7.tex`, subsection "Quotient size and payments", preamble: "In this subsection
`3 ≤ l ≤ R` and the past `Past_l` are fixed. We say that *the lists are fixed* when, in addition,
the variables `η_h` and `ζ_{h,u}` of `ξ_l` are fixed. Then steps (a)–(d) and (e1) …, the sets
`E'(u)` and their orders `e_1,…,e_q` are determined …, and only the orders `≺_u` are random. …
For a PAR colour `κ` and `w ≠ w'` in `Pool_l`, let `m_κ(w,w')` be the number of edges `[w][w']` of
`B^P_κ`."
Lemma [s7:lemCC] (Lemma CC: PAR copies): "Let the past and the lists be fixed. Fix a PAR colour `κ`
and `w ∈ Pool_l`. Condition further on the indicators
`I_x := 1[the end at x of the κ-object at x receives the junction w]`
for every port `x` carrying a PAR object of colour `κ`. Let `S_w` be the set of PAR objects of
colour `κ` with exactly one end whose junction is `w`.
(i) The partner ports `v_o` of the objects `o ∈ S_w` (the ports of the ends whose junction is not
`w`) are pairwise distinct. Under the conditioning, the junctions of the partner ends are
independent, and the junction of the partner end of `o` is uniform on
`(Cand_l(v_o) \ Used(v_o)) \ {w}`. In particular it equals a given `w'` with probability at most
`3/Hcd_l`.
(ii) For every integer `t ≥ 1`,
`E[max_{w'} m_κ(w,w') | Past_l, lists, (I_x)_x] ≤ t·1[S_w ≠ ∅] + 6e|S_w|/Hcd_l + 4e 2^{-t}|S_w|`.
(iii) With `t := t^CC_l := ⌈2log₂M_l⌉`, the number of vertices of `Q_l` lying in PAR sub-layers
satisfies `E[#{PAR copies} | Past_l, lists] ≤ 3M_l(t^CC_l+1)|Pool_l| + 44.7 nM_l/Hcd_l + 29.8 n/M_l`.
These bounds hold for every past, in particular for every realized `J_l`, and for every outcome of
the lists, the SDR and the greedy step (e1): only the orders `≺_u` are random."

Formal reading (TRIAGE §2.10; design note `work/p2d/quot.md`, "Notes for Spec authors").
* "For every past" is `∀ I : RoundInput V, I.Valid → ∀ R : Rules I, R.Valid` (the fixed rules
  obey the v6.1 restrictions by their argument types). "The lists are fixed" is a parameter
  `L : Lists I.G I.M`; the orders are random with law `ordersLaw I.G`, and
  `E[· | Past_l, lists]` is `(ordersLaw I.G).expect (fun O => X (L, O))`.
* PAR colours are naturals `κ < 3 * I.M`; `w ∈ Pool_l` is `w ∈ I.pool`.
* The indicators (T0, CC-ATOMS): the family `(I_x)_x` is indexed by the *ends* `(o, c)` of the
  PAR objects `o` of colour `κ` (`c : Bool`, `ParObj.endAt o c` its port) instead of by the ports
  `x`: every such port carries exactly one end of colour `κ` (Lemma s7:lemWellDef (i) and "a PAR
  object has its two ends at distinct ports"), so the two families are the same up to the
  bijection "end ↦ its port", and they generate the same atoms. "Conditioning on `(I_x)_x`" is
  conditioning (`FinDist.cond`) on an atom `{O | ∀ κ-ends (o,c), (junction of (o,c) = w) ↔ b o c}`
  for a value pattern `b` of positive probability (`ccAtom`); "for every value pattern of positive
  probability" is `∀ b, ∀ hb : 0 < P(atom)`.
* `S_w` is determined by the indicators: the `κ`-objects with exactly one end whose indicator is
  `1` (`ccS`, `b o false ≠ b o true`). The partner end of `o ∈ S_w` is the end `c` with
  `b o c = false`, i.e. `c = b o false` (`ccPartner`); its port is `v_o`.
* (i) "pairwise distinct" is injectivity of `o ↦ v_o` on `S_w`; "independent" is
  `FinDist.iIndepFun` of the partner junctions (`Option V`-valued) under the conditioned law;
  "uniform on `C := (Cand_l(v_o) \ Used(v_o)) \ {w}`" is: for every `w'`, the conditional
  probability that the junction is `w'` is `1/|C|` if `w' ∈ C` and `0` otherwise (this forces
  `C ≠ ∅` and "the junction is some element of `C`" almost surely). `Used(v)` is the set after
  (e1), `R.used L v`; `Cand_l(v) = I.cand v`.
* (ii) `max_{w'} m_κ(w,w')` is the maximum over `w' ∈ Pool_l \ {w}` (`Finset.sup`, `0` on the empty
  set), `m_κ(w,w') = R.mPar (L, O) κ w w'`; `e = Real.exp 1`, `2^{-t}` the integer power.
* (iii) "the number of vertices of `Q_l` lying in PAR sub-layers" is the number of vertices of
  `R.Q (L, O)` whose tag has kind `false` (PAR) (`parCopies`); `n = |V(G)| = I.G.card`,
  `t^CC_l = EG.Quot.tCC I.M` (the one shared Defs constant, TRIAGE §2.10). This is the form the
  consumer s7:lemUHsplit (ii) (chunk s7b) needs: a bound for every value of the lists, to be
  averaged over the lists afterwards (blueprint s7b UH-AVERAGE-LISTS).
-/

@[expose] public section

namespace EG.Spec

open EG.Quot

section helpers

variable {V : Type*} [DecidableEq V] {I : RoundInput V}

/-- The PAR objects of colour `κ` ([s7:lemCC] "the `κ`-objects"). -/
noncomputable def parObjsOfColour (R : Rules I) (κ : ℕ) : Finset (ParObj V) :=
  R.parObjs.filter (fun o => R.parColour o = some κ)

/-- The atom of the indicator family of Lemma CC for the value pattern `b`: the orders `O` (the
lists `L` fixed) for which, for every end `(o, c)` of a PAR object `o` of colour `κ`, "the end
receives the junction `w`" holds iff `b o c = true` ([s7:lemCC] "Condition further on the
indicators `I_x`"). -/
def ccAtom (R : Rules I) (L : Lists I.G I.M) (κ : ℕ) (w : V) (b : ParObj V → Bool → Bool) :
    Set (Orders I.G) :=
  {O | ∀ o ∈ parObjsOfColour R κ, ∀ c : Bool,
    (R.junction (L, O) (.par o c) = some w ↔ b o c = true)}

/-- [s7:lemCC] "`S_w` [is] the set of PAR objects of colour `κ` with exactly one end whose junction
is `w`", read from the value pattern `b` of the indicators. -/
noncomputable def ccS (R : Rules I) (κ : ℕ) (b : ParObj V → Bool → Bool) : Finset (ParObj V) :=
  (parObjsOfColour R κ).filter (fun o => b o false ≠ b o true)

/-- The partner end of `o ∈ S_w` ([s7:lemCC] (i) "the ends whose junction is not `w`"): the end
`c` with `b o c = false`; for `o ∈ S_w` exactly one of `b o false`, `b o true` is `true`, and the
partner end is `c = b o false`. Its port `o.endAt (ccPartner b o)` is the partner port `v_o`. -/
def ccPartner (b : ParObj V → Bool → Bool) (o : ParObj V) : Bool := b o false

/-- [s7:lemCC] (iii) "the number of vertices of `Q_l` lying in PAR sub-layers" (the vertices whose
tag has kind `false`). -/
noncomputable def parCopies (R : Rules I) (ξ : Xi I.G I.M) : ℕ :=
  ((R.Q ξ).verts.filter (fun q => q.1.1 = false)).card

end helpers

/-- [s7:lemCC] (i) "Let the past and the lists be fixed. Fix a PAR colour `κ` and `w ∈ Pool_l`.
Condition further on the indicators `I_x` … Let `S_w` be the set of PAR objects of colour `κ` with
exactly one end whose junction is `w`. (i) The partner ports `v_o` of the objects `o ∈ S_w` (the
ports of the ends whose junction is not `w`) are pairwise distinct. Under the conditioning, the
junctions of the partner ends are independent, and the junction of the partner end of `o` is
uniform on `(Cand_l(v_o) \ Used(v_o)) \ {w}`. In particular it equals a given `w'` with probability
at most `3/Hcd_l`." -/
def CCPartnerStatement : Prop :=
  ∀ (V : Type) [DecidableEq V] (I : RoundInput V), I.Valid → ∀ R : Rules I, R.Valid →
    ∀ (L : Lists I.G I.M) (κ : ℕ) (w : V), κ < 3 * I.M → w ∈ I.pool →
    ∀ (b : ParObj V → Bool → Bool) (hb : 0 < (ordersLaw I.G).prob (ccAtom R L κ w b)),
      -- the partner ports are pairwise distinct
      Set.InjOn (fun o => o.endAt (ccPartner b o)) (ccS R κ b : Set (ParObj V)) ∧
      -- under the conditioning, the partner junctions are independent
      ((ordersLaw I.G).cond (ccAtom R L κ w b) hb).iIndepFun
        (fun (o : ↥(ccS R κ b)) (O : Orders I.G) =>
          R.junction (L, O) (.par (o : ParObj V) (ccPartner b o))) ∧
      -- … each uniform on `(Cand_l(v_o) \ Used(v_o)) \ {w}`, hence each value has probability
      -- at most `3/Hcd_l`
      ∀ o ∈ ccS R κ b, ∀ w' : V,
        ((ordersLaw I.G).cond (ccAtom R L κ w b) hb).prob
            {O | R.junction (L, O) (.par o (ccPartner b o)) = some w'} =
          (if w' ∈ (I.cand (o.endAt (ccPartner b o)) \ R.used L (o.endAt (ccPartner b o))).erase w
            then 1 / (((I.cand (o.endAt (ccPartner b o)) \
                R.used L (o.endAt (ccPartner b o))).erase w).card : ℝ)
            else 0) ∧
        ((ordersLaw I.G).cond (ccAtom R L κ w b) hb).prob
            {O | R.junction (L, O) (.par o (ccPartner b o)) = some w'} ≤ 3 / I.Hcd

/-- [s7:lemCC] (ii) "For every integer `t ≥ 1`,
`E[max_{w'} m_κ(w,w') | Past_l, lists, (I_x)_x] ≤ t·1[S_w ≠ ∅] + 6e|S_w|/Hcd_l + 4e 2^{-t}|S_w|`."
(Past and lists fixed, `κ` a PAR colour, `w ∈ Pool_l`, conditioned on a value pattern of the
indicators of positive probability.) -/
def CCMaxStatement : Prop :=
  ∀ (V : Type) [DecidableEq V] (I : RoundInput V), I.Valid → ∀ R : Rules I, R.Valid →
    ∀ (L : Lists I.G I.M) (κ : ℕ) (w : V), κ < 3 * I.M → w ∈ I.pool →
    ∀ (b : ParObj V → Bool → Bool) (hb : 0 < (ordersLaw I.G).prob (ccAtom R L κ w b)),
    ∀ t : ℕ, 1 ≤ t →
      ((ordersLaw I.G).cond (ccAtom R L κ w b) hb).expect
          (fun O => (((I.pool.erase w).sup (fun w' => R.mPar (L, O) κ w w') : ℕ) : ℝ)) ≤
        (t : ℝ) * (if (ccS R κ b).Nonempty then 1 else 0) +
          6 * Real.exp 1 * ((ccS R κ b).card : ℝ) / I.Hcd +
          4 * Real.exp 1 * (2 : ℝ) ^ (-(t : ℤ)) * ((ccS R κ b).card : ℝ)

/-- [s7:lemCC] (iii) "With `t := t^CC_l := ⌈2log₂M_l⌉`, the number of vertices of `Q_l` lying in
PAR sub-layers satisfies
`E[#{PAR copies} | Past_l, lists] ≤ 3M_l(t^CC_l+1)|Pool_l| + 44.7 nM_l/Hcd_l + 29.8 n/M_l`. These
bounds hold for every past, in particular for every realized `J_l`, and for every outcome of the
lists, the SDR and the greedy step (e1): only the orders `≺_u` are random." -/
def CCCopiesStatement : Prop :=
  ∀ (V : Type) [DecidableEq V] (I : RoundInput V), I.Valid → ∀ R : Rules I, R.Valid →
    ∀ L : Lists I.G I.M,
      (ordersLaw I.G).expect (fun O => (parCopies R (L, O) : ℝ)) ≤
        3 * (I.M : ℝ) * ((tCC I.M : ℝ) + 1) * (I.pool.card : ℝ) +
          44.7 * (I.G.card : ℝ) * (I.M : ℝ) / I.Hcd + 29.8 * (I.G.card : ℝ) / (I.M : ℝ)

end EG.Spec
