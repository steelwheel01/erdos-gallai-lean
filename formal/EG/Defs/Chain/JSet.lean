module

public import EG.Defs.Chain.Lending

/-!
# The J-interface `JPlusProps` (manuscript s6:lemJplus)

PROTECTED FILE (`EG/Defs/**`): changes need the approval procedure in `APPROVALS/README.md`.

Manuscript v6.1, Lemma [s6:lemJplus] ("Lemma J⁺: the J-interface"), quoted in the docstrings
below. Design note: `formal/work/p2d/design.md`. Namespace `EG.Chain`.

Lemma J⁺ is a statement about the set `J_l` built inside the proof of Lemma JS-LC (s6:lemJSLC).
In Lean `J_l` has no identity outside the JS-LC statement, so the properties of Lemma J⁺ are a
predicate `EG.Chain.JPlusProps run G δ S l J` on an edge set `J` (TRIAGE §2.9, blueprint s6b
JPLUS-EXISTENTIAL / JSLC-JPLUS-MERGE): the JS-LC Spec asserts `JPlusProps … l J_l` for the set it
produces, the J-consumer (s6:defJconsumer, `EG.Chain.JConsumer`) is required to work only on sets
with `JPlusProps`, and the s7 round step (`RoundInput.Valid`) reads exactly these fields.

Fields (all for the round `l`, with `Z ∈ Std_l` the standalone pre-part at address `a`):
* `types` — (i), exhaustive: every edge of `J` is a `J^par`-, `J^hub`-, `J^fr`- or `J^lost`-edge
  (the typed predicates `IsJparEdge`, `IsJhubEdge`, `IsJfrEdge`, `IsJlostEdge`; each includes
  `e ∈ E_l(Z)`, so `J ⊆ ⋃_Z E_l(Z)`); exclusivity is `J`-independent (Lib);
* `J1hub`, `J1fr`, `J1lost` — (J1), **aggregated over all parts of round `l`** (TRIAGE §1b MULT-J1:
  the filter runs over all of `J`, never over one part);
* `J2end`, `J2cap`, `J2out`, `J2card` — (J2): the end in `Q*_Z`, the per-part cap `M_l − 1`, the
  cap `M_l − 1` at every vertex outside `D_l` (the "in particular"), and `|J_l| ≤ n (M_l − 1)`;
* `freshCap` — (ii).

Also defined here: `EG.Chain.jBound`, the right side of (s6:eqJbound) of Lemma JS-LC (a conjunct of
the JS-LC Spec, blueprint s6b JSLC-EQJBOUND).

Not fields (TRIAGE §2.9; blueprint s6b JPLUS-J3-III-IV, JPLUS-V-PROB): (J3) and the exclusivity
part of (i) do not mention `J_l` and hold for every run (Lib, `EG.Lib.Chain.JSet`); (iii) is
s2:propStructure(iii) and (iv) is a property of designations (`EG.Chain.IsDesignation.mem_ancVerts`);
(v) is a property of the stage-1 law. The clause "`J_l` consists exactly of the deletions of Step 2
… for every choice … Steps 3–8 delete nothing" is about the proof of JS-LC and is not used
downstream (checked against every s7 use, blueprint s6b JPLUS-EXISTENTIAL); it is not encoded.
The factor `1.37` of (J2) is vestigial (`n(M_l − 1) ≤ 1.37 n(M_l − 1)`); the sharper `n(M_l − 1)`
is the field.
-/

@[expose] public section

namespace EG.Chain

open EG.HB

variable {V : Type*} [DecidableEq V] (run : Run V) (G : FGraph V) (δ : Designation V)
  (S : StageData V)

/-- [s6:lemJplus] "a `J^par`-edge has both ends in `Q*_Z`, with different classes" (for some
`Z ∈ Std_l`, the edge lying in `E_l(Z)`). -/
def IsJparEdge (l : ℕ) (e : Sym2 V) : Prop :=
  ∃ a ∈ run.Std G l, e ∈ run.E G l a ∧
    ∃ u v, e = s(u, v) ∧ u ∈ qs run G δ S l a ∧ v ∈ qs run G δ S l a ∧ δ l u ≠ δ l v

/-- [s6:lemJplus] "a `J^hub`-edge is an edge `hu` with `h ∈ A_Z ⊆ D_l` and `u ∈ Q*_Z`"; "The
*class* of a `J^hub`-… edge `hu` is `Y(u)`": `e` is a `J^hub`-edge of class `Y` at the hub `h`
(for some `Z ∈ Std_l`, the edge lying in `E_l(Z)`). -/
def IsJhubEdge (l : ℕ) (h : V) (Y : PartId) (e : Sym2 V) : Prop :=
  ∃ a ∈ run.Std G l, e ∈ run.E G l a ∧
    ∃ u, e = s(h, u) ∧ h ∈ run.hubs G l a ∧ u ∈ qs run G δ S l a ∧ δ l u = Y

/-- [s6:lemJplus] "a `J^fr`-edge is an edge `xu` with `x ∈ F_Z` and `u ∈ Q*_Z`"; its class is
`Y(u)`: `e` is a `J^fr`-edge of class `Y` at the fresh centre `x`. -/
def IsJfrEdge (l : ℕ) (x : V) (Y : PartId) (e : Sym2 V) : Prop :=
  ∃ a ∈ run.Std G l, e ∈ run.E G l a ∧
    ∃ u, e = s(x, u) ∧ x ∈ run.fresh G l a ∧ u ∈ qs run G δ S l a ∧ δ l u = Y

/-- [s6:lemJplus] "a `J^lost`-edge is an edge `vu` with `v ∈ Lost_Z` (a lost centre) and
`u ∈ Q*_Z`"; its class is `Y(u)`: `e` is a `J^lost`-edge of class `Y` at the lost centre `v`. -/
def IsJlostEdge (l : ℕ) (v : V) (Y : PartId) (e : Sym2 V) : Prop :=
  ∃ a ∈ run.Std G l, e ∈ run.E G l a ∧
    ∃ u, e = s(v, u) ∧ v ∈ lost run G δ S l a ∧ u ∈ qs run G δ S l a ∧ δ l u = Y

open Classical in
/-- [s6:lemJplus] "`J_l = J^lost_l ⊔ J^hub_l ⊔ J^fr_l ⊔ J^par_l`": the `J^par`-edges of `J`. -/
noncomputable def Jpar (l : ℕ) (J : Finset (Sym2 V)) : Finset (Sym2 V) :=
  J.filter (IsJparEdge run G δ S l)

open Classical in
/-- [s6:lemJplus] the `J^hub`-edges of `J`. -/
noncomputable def Jhub (l : ℕ) (J : Finset (Sym2 V)) : Finset (Sym2 V) :=
  J.filter (fun e => ∃ h Y, IsJhubEdge run G δ S l h Y e)

open Classical in
/-- [s6:lemJplus] the `J^fr`-edges of `J`. -/
noncomputable def Jfr (l : ℕ) (J : Finset (Sym2 V)) : Finset (Sym2 V) :=
  J.filter (fun e => ∃ x Y, IsJfrEdge run G δ S l x Y e)

open Classical in
/-- [s6:lemJplus] the `J^lost`-edges of `J`. -/
noncomputable def Jlost (l : ℕ) (J : Finset (Sym2 V)) : Finset (Sym2 V) :=
  J.filter (fun e => ∃ v Y, IsJlostEdge run G δ S l v Y e)

/-- [s6:lemJSLC] (s6:eqJbound) the right side of
"`|J_l| ≤ Σ_{h ∈ D_l} c^agg_{h,l} + Σ_{Z ∈ Std_l} [Σ_{x ∈ F_Z} c_x(Z) + (M_l − 1)|Lost_Z|
+ (1/2) Σ_{u ∈ Q_Z} c_pp(u)]`" ("computed from the sets `E_l(Z)`, not from the `B_Z`"; recorded in
JS-LC for completeness, not used later). A real number because of the factor `1/2`. -/
noncomputable def jBound (l : ℕ) : ℝ :=
  ∑ h ∈ run.D G l, (cAgg run G δ h l : ℝ) +
    ∑ a ∈ run.Std G l, (∑ x ∈ run.fresh G l a, (cFresh run G δ l a x : ℝ) +
      ((run.M G l : ℝ) - 1) * ((lost run G δ S l a).card : ℝ) +
      (1 / 2 : ℝ) * ∑ u ∈ run.classed G l a, (cPP run G δ l a u : ℝ))

open Classical in
/-- [s6:lemJplus] **Lemma J⁺, the J-interface**, as a predicate on the edge set `J` (= `J_l`) of
round `l`: the properties (i) (exhaustive part), (J1), (J2) and (ii). Quoted text:

"Moreover `J_l = J^lost_l ⊔ J^hub_l ⊔ J^fr_l ⊔ J^par_l`, where, for `Z ∈ Std_l`: a `J^par`-edge has
both ends in `Q*_Z`, with different classes; a `J^hub`-edge is an edge `hu` with `h ∈ A_Z ⊆ D_l`
and `u ∈ Q*_Z`; a `J^fr`-edge is an edge `xu` with `x ∈ F_Z` and `u ∈ Q*_Z`; a `J^lost`-edge is an
edge `vu` with `v ∈ Lost_Z` (a lost centre) and `u ∈ Q*_Z`. The *class* of a `J^hub`-, `J^fr`- or
`J^lost`-edge `hu` is `Y(u)`. The following properties hold.
(J1) For each hub `h ∈ D_l` and each class `Y`, `J_l` contains at most one `J^hub`-edge of class `Y`
at `h`, aggregated over all parts of round `l`. For each fresh centre `x` and each class `Y`, `J_l`
contains at most one `J^fr`-edge of class `Y` at `x`. (The same holds at lost centres.)
(J2) Every J-edge lying in `E_l(Z)` has an end in `Q*_Z`. For every `Z` and every vertex, at most
`M_l − 1` J-edges at that vertex lie in `E_l(Z)`. In particular a port or a fresh centre (a vertex
outside `D_l`) carries at most `M_l − 1` J-edges of round `l`. Also
`|J_l| ≤ n(M_l − 1) ≤ 1.37 n(M_l − 1)`. …
(i) The types above are exhaustive and exclusive.
(ii) (Size cap at fresh centres.) A fresh centre carries at most `M_l − 1` `J^fr`-edges."

(J3), exclusivity in (i), (iii), (iv), (v): see the module docstring. All counts are over the
whole of `J` (aggregated over the parts of round `l`). -/
structure JPlusProps (l : ℕ) (J : Finset (Sym2 V)) : Prop where
  /-- (i), exhaustive: every edge of `J_l` is of one of the four types. -/
  types : ∀ e ∈ J, IsJparEdge run G δ S l e ∨ (∃ h Y, IsJhubEdge run G δ S l h Y e) ∨
    (∃ x Y, IsJfrEdge run G δ S l x Y e) ∨ (∃ v Y, IsJlostEdge run G δ S l v Y e)
  /-- (J1) at hubs, aggregated over all parts of round `l`. -/
  J1hub : ∀ h ∈ run.D G l, ∀ Y : PartId, (J.filter (IsJhubEdge run G δ S l h Y)).card ≤ 1
  /-- (J1) at fresh centres (aggregated over all parts; a fresh centre lies in one part). -/
  J1fr : ∀ x ∈ freshCentres run G l, ∀ Y : PartId,
    (J.filter (IsJfrEdge run G δ S l x Y)).card ≤ 1
  /-- (J1) at lost centres (aggregated over all parts; a lost centre lies in one part). -/
  J1lost : ∀ v ∈ lostRound run G δ S l, ∀ Y : PartId,
    (J.filter (IsJlostEdge run G δ S l v Y)).card ≤ 1
  /-- (J2) "Every J-edge lying in `E_l(Z)` has an end in `Q*_Z`." -/
  J2end : ∀ a ∈ run.Std G l, ∀ e ∈ J, e ∈ run.E G l a → ∃ u ∈ qs run G δ S l a, u ∈ e
  /-- (J2) "For every `Z` and every vertex, at most `M_l − 1` J-edges at that vertex lie in
  `E_l(Z)`." -/
  J2cap : ∀ a ∈ run.Std G l, ∀ v : V,
    (J.filter (fun e => e ∈ run.E G l a ∧ v ∈ e)).card ≤ run.M G l - 1
  /-- (J2) "In particular a port or a fresh centre (a vertex outside `D_l`) carries at most
  `M_l − 1` J-edges of round `l`." -/
  J2out : ∀ v ∉ run.D G l, degE J v ≤ run.M G l - 1
  /-- (J2) "Also `|J_l| ≤ n(M_l − 1)`" (`n = |V(G)|`). -/
  J2card : J.card ≤ G.card * (run.M G l - 1)
  /-- (ii) "A fresh centre carries at most `M_l − 1` `J^fr`-edges." -/
  freshCap : ∀ x ∈ freshCentres run G l,
    (J.filter (fun e => ∃ Y, IsJfrEdge run G δ S l x Y e)).card ≤ run.M G l - 1

end EG.Chain
