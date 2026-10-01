module

public import EG.Defs.HB.Run
public import EG.Defs.Components

/-!
# Designations and class data (manuscript s6:defDesign)

PROTECTED FILE (`EG/Defs/**`): changes need the approval procedure in `APPROVALS/README.md`.

Manuscript v6.1, Definition [s6:defDesign] ("designation and class data; `𝒱 = ∅`"), quoted in
the docstrings below. Design note: `formal/work/p2d/design.md`. Namespace `EG.Chain`.

Everything is built on the locked `HB*^{τ+}` run model `EG.HB.Run` (design note
`work/p2d/hb.md`): ancestors are `EG.HB.PartId = ℕ × Addr` (round, pre-part address), round-`l`
objects are `run.Std G l`, `run.E G l a`, `run.classed G l a`, `run.anc G l u`, … .

Encoding decisions (TRIAGE §2.9 "Designation"; blueprint s6a notes DES-*):
* a designation is a **round-indexed total function** `δ : ℕ → V → PartId` (`δ l u = Y(u)` for a
  classed port `u` of round `l`; a vertex may be a classed port in several rounds). It is a
  parameter of the statements, fixed before any stage-1 law is formed ("`δ` is any deterministic
  function of the run"). `IsDesignation` constrains only the classed ports of standalone
  pre-parts of rounds `l ≥ 3`; the other values are junk and every definition below reads `δ l u`
  only at classed ports `u ∈ Q_Z`, `Z ∈ Std_l`;
* "`Z_u`, the part with `u ∈ Q_Z`" is not a function here: it is unique (Lib,
  `EG.Chain.classed_disjoint`), and the definitions quantify `∃ a ∈ Std_l, u ∈ Q_Z ∧ …`;
* the class counts are **edge counts / class counts exactly as written**; the port-counting form
  of `d_{Y,l}(h)` is a Lib lemma (`EG.Chain.classDeg_eq_card_ports`);
* for `l ≤ 2` there are no classed ports (`anc_l = ∅`), and for `l > R` no standalone pre-parts
  (`Std_l = ∅`, guarded run model), so all quantities vanish there (Lib lemmas);
* `γ_l := ⌊P_{l-2}/M_l⌋` reads `P_{l-2}` with `ℕ`-subtraction; it is used only for `l ≥ 3`.
-/

@[expose] public section

namespace EG.Chain

open EG.HB

variable {V : Type*}

/-- A designation: for every round `l` and vertex `u`, the value `δ l u = Y(u)` (the *class* of
`u` at round `l`). Only the values at classed ports are constrained (`IsDesignation`). -/
abbrev Designation (V : Type*) := ℕ → V → PartId

variable [DecidableEq V] (run : Run V) (G : FGraph V) (δ : Designation V)

/-- [s6:defDesign] "A *designation* `δ` assigns, for every round `l ≥ 3`, to every standalone
pre-part `Z ∈ Std_l` and every classed port `u ∈ Q_Z` an ancestor `Y(u) ∈ anc_l(u)`, the *class*
of `u`. Here `δ` is any deterministic function of the run." (Deterministic: `δ` is a parameter,
quantified before any stage-1 law; see the module docstring.) -/
def IsDesignation : Prop :=
  ∀ l, 3 ≤ l → ∀ a ∈ run.Std G l, ∀ u ∈ run.classed G l a, δ l u ∈ run.anc G l u

/-- [s6:defDesign] "a classed port of round `l`": the classed ports `u ∈ Q_Z` of the standalone
pre-parts `Z ∈ Std_l` ("Every classed port `u` of round `l` lies in `Q_Z` for exactly one
`Z ∈ Std_l`"; uniqueness is `EG.Chain.classed_disjoint`). -/
noncomputable def classedPorts (l : ℕ) : Finset V :=
  (run.Std G l).biUnion (run.classed G l)

/-- [s6:defDesign] "the *class-`Y` degree*
`d_{Y,l}(h) := #{hu ∈ E_l(Z) : Z ∈ Std_l, u ∈ Q_Z, Y(u) = Y}`": the number of edges `hu` of the
sets `E_l(Z)`, `Z ∈ Std_l`, whose other end `u` is a classed port of `Z` of class `Y`. (Edges are
counted; the sets `E_l(Z)` of distinct `Z` are disjoint. Counting the ports `u` instead gives the
same number: `EG.Chain.classDeg_eq_card_ports`.) -/
noncomputable def classDeg (Y : PartId) (l : ℕ) (h : V) : ℕ :=
  ((run.Std G l).biUnion (fun a => (run.E G l a).filter
    (fun e => ∃ u ∈ run.classed G l a, e = s(h, u) ∧ δ l u = Y))).card

/-- [s6:defDesign] "`m_{Y,l} := max_h d_{Y,l}(h)`, the maximum over all vertices `h` of `G`". -/
noncomputable def mY (Y : PartId) (l : ℕ) : ℕ :=
  G.verts.sup (classDeg run G δ Y l)

/-- [s6:defDesign] "`d^*_{Y,l} := #{u : u a classed port of round l, Y(u) = Y, u ∈ Dup*_r}`",
with `r = r(Y)` the round of the ancestor `Y` (`Y.1`). -/
noncomputable def dStar (Y : PartId) (l : ℕ) : ℕ :=
  ((classedPorts run G l).filter (fun u => δ l u = Y ∧ u ∈ run.DupStar G Y.1)).card

/-- [s6:defDesign] "for light `Y`, the *guest core degree*
`α_{Y,l} := max_{x ∈ S_Y} #{u ∈ Y \ Dup*_r : u a classed port of round l, Y(u) = Y,
xu ∈ E_l(Z_u)}`, with `α_{Y,l} := 0` if `S_Y = ∅`." Here `Y = V(Y)` (the light part's vertex
set, `run.ancVerts G Y`), `S_Y` its guests, `r = Y.1`, and `Z_u` the (unique) `Z ∈ Std_l` with
`u ∈ Q_Z`; the maximum over the empty set is `0` (`Finset.sup`). The definition is total; it is
meaningful (and read by s6:thmCONCL) only for light `Y`. -/
noncomputable def alphaY (Y : PartId) (l : ℕ) : ℕ :=
  (run.guests G Y.1 Y.2).sup (fun x =>
    ((run.ancVerts G Y \ run.DupStar G Y.1).filter (fun u =>
      ∃ a ∈ run.Std G l, u ∈ run.classed G l a ∧ δ l u = Y ∧ s(x, u) ∈ run.E G l a)).card)

open Classical in
/-- [s6:defDesign] "the *deterministic bead graph*
`Bead_{Y,l} := {hu ∈ E_l(Z) : Z ∈ Std_l, u ∈ Q_Z, Y(u) = Y, and h ∉ Q_Z or Y(h) ≠ Y}`"
(an edge set; its graph is `(V(Bead), Bead)`, `EG.edgeVerts`). The clause "`h ∉ Q_Z` or
`Y(h) ≠ Y`" is kept literally (it is always true on a valid run, by s2:lemEL). -/
noncomputable def Bead (Y : PartId) (l : ℕ) : Finset (Sym2 V) :=
  (run.Std G l).biUnion (fun a => (run.E G l a).filter (fun e =>
    ∃ h u, e = s(h, u) ∧ u ∈ run.classed G l a ∧ δ l u = Y ∧
      (h ∉ run.classed G l a ∨ δ l h ≠ Y)))

/-- [s6:defDesign] "`γ_l := ⌊P_{l-2}/M_l⌋`" (a natural number; `P_{l-2}` with `ℕ`-subtraction,
read only for `l ≥ 3`; equal to `P_{l-2} / M_l` in `ℕ`, `EG.Chain.gammaL_eq_div`). -/
noncomputable def gammaL (l : ℕ) : ℕ :=
  ⌊(run.P G (l - 2) : ℝ) / (run.M G l : ℝ)⌋₊

/-- [s6:defDesign] "the pair `(Y,l)` is *giant* iff some connected component of `Bead_{Y,l}` has
more than `2γ_l` edges" (components of the graph `(V(Bead), Bead)`, `EG.edgeComps`). -/
def IsGiant (Y : PartId) (l : ℕ) : Prop :=
  ∃ C ∈ edgeComps (Bead run G δ Y l), 2 * gammaL run G l < (compEdges (Bead run G δ Y l) C).card

/-- [s6:defDesign] "the *class counts* `c^agg_{h,l} := #{Y : d_{Y,l}(h) ≥ 1}`": the number of
distinct classes `Y(u)` of the classed ports `u ∈ Q_Z` (`Z ∈ Std_l`) with `hu ∈ E_l(Z)`; this is
exactly the set of `Y` with `d_{Y,l}(h) ≥ 1` (`EG.Chain.mem_cAggClasses_iff`). -/
noncomputable def cAggClasses (h : V) (l : ℕ) : Finset PartId :=
  ((run.Std G l).biUnion (fun a =>
    (run.classed G l a).filter (fun u => s(h, u) ∈ run.E G l a))).image (δ l)

/-- [s6:defDesign] "`c^agg_{h,l} := #{Y : d_{Y,l}(h) ≥ 1}`". -/
noncomputable def cAgg (h : V) (l : ℕ) : ℕ := (cAggClasses run G δ h l).card

/-- [s6:defDesign] "for `Z ∈ Std_l` and a fresh port `x ∈ F_Z`,
`c_x(Z) := #{Y(u) : u ∈ Q_Z, xu ∈ E_l(Z)}`" (the pre-part `Z` is its address `a`; total in `x`,
read only for `x ∈ F_Z`). -/
noncomputable def cFresh (l : ℕ) (a : Addr) (x : V) : ℕ :=
  (((run.classed G l a).filter (fun u => s(x, u) ∈ run.E G l a)).image (δ l)).card

/-- [s6:defDesign] "for `u ∈ Q_Z`, `c_pp(u) := #{Y(v) : v ∈ Q_Z, uv ∈ E_l(Z)}`" (total in `u`,
read only for `u ∈ Q_Z`). -/
noncomputable def cPP (l : ℕ) (a : Addr) (u : V) : ℕ :=
  (((run.classed G l a).filter (fun v => s(u, v) ∈ run.E G l a)).image (δ l)).card

end EG.Chain
