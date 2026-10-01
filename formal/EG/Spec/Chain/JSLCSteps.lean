module

public import EG.Defs.Chain.JSet
public import EG.Defs.Chain.StageInst
public import EG.Defs.Gamma.Core

/-!
# Steps 1, 2 and 7 of the proof of Lemma JS-LC: types and T-avoidance, the set `J_l` with (J1)
aggregated, and the disjointness checks for HCC-P (manuscript s6:lemJSLC, proof)

Statement file of probe unit P2J (probe P-2, part 2; design note `formal/work/p2b/P2J.md`).
These are not separate manuscript lemmas: they are the checks, inside the proof of Lemma JS-LC
[s6:lemJSLC], that the hypotheses of the routing engine (Lemmas MED, EQ-LPT, HCC-P, HCCglob;
unit P2E) hold, and the construction of `J_l` that Lemma J⁺ [s6:lemJplus] describes. TRIAGE §4,
probe P-2: "the JS-LC Step 6/7 hypothesis checks (joint multiplicity `≤ 2M_l−2 ≤ t^JS`, distinct
pair ends, T-avoidance, aggregated J1)". The joint-routing claims (a), (c), (d) of Step 6 are in
`EG/Spec/Chain/JSLCRouting.lean`. Label tags `[s6:lemJSLC:proof-step-k]` (as in
`EG/Spec/Chain/EngineMult.lean`): proof-internal facts of [s6:lemJSLC], not the lemma.

* `JslcTypesStatement` (Step 1 and claim (e), **T-avoidance**): "For `u ∈ Q*_Z`, the class `Y(u)`
  is lend-good and `lab_{Y(u),l}(u) = *`"; ports lie in `V(Y(u))` and in no `T_j(Y(u),l)`; both ends
  of an edge of `E_l(Z)` lie in `Z^0 = Ret_Z ⊔ Q*_Z`; for an edge `hu ∈ E_l(Z)` with `u ∈ Q_Z`, the
  centre `h` lies outside `V(Y(u))`, hence in no `T_j(Y(u),l)` (Lemma s2:lemEL); the two ends of a
  port–port edge have different classes.
* `JslcStep2Statement` (Step 2 and Step 3, first paragraph; **aggregated (J1)**): there are
  `J_l ⊆ ⋃_Z B_Z` and the realized class-`Y` bead sets `R_Y` such that `⋃_Z B_Z = J_l ⊔ ⨆_Y R_Y`,
  every edge of `R_Y` joins a class-`Y` port of some `Q*_Z` to a centre outside `V(Y)`, every
  centre has even degree in every `R_Y` ("after the moves every centre has even degree in every
  `R_Y`", the parity is **aggregated over all parts of round `l`**: `degE (R_Y) h` counts the
  class-`Y` beads at `h` in all parts), `R_Y ⊆ Bead_{Y,l}`, and `J_l` satisfies (J1) at hubs
  aggregated over all parts, (s6:eqJbound) and `JPlusProps`.
  **Refutation target of probe P-2** (TRIAGE §4): "two `J^hub` edges of one class at one hub in
  one round (J1 aggregated)". It is the explicit conjunct
  `∀ h ∈ D_l, ∀ Y, #{e ∈ J_l : e is a J^hub-edge of class Y at h} ≤ 1` (the same as the field
  `JPlusProps.J1hub`, stated again so that the target is visible), where the filter runs over the
  whole of `J_l` (all parts `Z ∈ Std_l` containing the hub `h`), jointly with the aggregated parity
  of the `R_Y`: a per-part parity rule would move one edge per part and could violate it.
* `JslcStep7DisjStatement` (Step 7, the disjointness hypotheses of HCC-P and HCCglob): the path
  classes `LJS_{Y,l,j}` are disjoint from every bead set `E_l(Z)`, pairwise disjoint for distinct
  ancestors and for distinct junctions of one ancestor; the junction sets `T_j(Y,l)` are pairwise
  disjoint and lie in `V(Y)` ("The sets `T_j(Y,l)` are pairwise disjoint (Definition
  s3:defCOL(iv))").

Formal conventions as in `EG/Spec/Chain/JSLC.lean` (stage data `S`, designation `δ`, input
`B : Addr → Finset (Sym2 V)`, `⋃_Z B_Z = (run.Std G l).biUnion B`).
-/

@[expose] public section

namespace EG.Spec

open EG.HB EG.Chain

universe u

/-- [s6:lemJSLC:proof-step-1] (a proof-internal fact of [s6:lemJSLC], not the lemma: proof,
"two facts", Step 1 and joint-routing claim (e); **T-avoidance**) "For `u ∈ Q*_Z`, the class
`Y(u)` is lend-good and `lab_{Y(u),l}(u) = *` (Definition s6:defLending)." "Both ends lie in
`Z^0`, since `E_l(Z) ⊆ E(G[Z^0])` by (R5). Since `Z^0 = Ret_Z ⊔ Q*_Z`, there are two cases for the
other end `v` … `v ∈ Q*_Z`. Then `e` is a port–port edge, and `Y(v) ≠ Y(u)`: otherwise both ends of
`e ∈ E(G_l)` would lie in `V(Y(u))` with `l > r(Y(u))`, contrary to Lemma s2:lemEL. By the same
lemma, for every edge `hu ∈ E_l(Z)` with `u ∈ Q_Z` and `Y(u) = Y`, the vertex `h` lies outside
`V(Y)`. In particular `h ∉ T_j(Y,l)`, since `T_j(Y,l) ⊆ V(Y)`." Claim (a), (e): ports lie "in
`V(Y)` because `Y = Y(u) ∈ anc_l(u)`, and outside every `T_{j'}(Y,l)` because `lab_{Y,l}(u) = *`";
"Centres lie outside `V(Y) ⊇ T_{j'}(Y,l)` (Step 1)." -/
def JslcTypesStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (Dstar : ℝ) (run : Run V)
    (δ : Designation V) (S : StageData V) (l : ℕ) (a : Addr),
    run.Valid G Dstar → IsDesignation run G δ → 3 ≤ l → a ∈ run.Std G l →
      (∀ u ∈ qs run G δ S l a,
        δ l u ∈ lendGoodAnc run G S l ∧ S.lab (δ l u) l u = none ∧
          u ∈ run.ancVerts G (δ l u) ∧ ∀ j, u ∉ Tj run G S (δ l u) l j) ∧
      (∀ e ∈ run.E G l a, ∀ v ∈ e, v ∈ ret run G δ S l a ∨ v ∈ qs run G δ S l a) ∧
      (∀ u ∈ run.classed G l a, ∀ h : V, s(h, u) ∈ run.E G l a →
        h ∉ run.ancVerts G (δ l u) ∧ ∀ j, h ∉ Tj run G S (δ l u) l j) ∧
      (∀ u ∈ run.classed G l a, ∀ v ∈ run.classed G l a, s(u, v) ∈ run.E G l a →
        δ l u ≠ δ l v)

open Classical in
/-- [s6:lemJSLC:proof-step-2] (a proof-internal fact of [s6:lemJSLC], not the lemma: proof,
Step 2 and the first paragraph of Step 3; with [s6:lemJplus]; **aggregated (J1)**, the refutation
target of probe P-2) "(2a) For each `Z ∈ Std_l` and each unordered pair `{a,b}` of distinct
classes, let `E_ab(Z)` be the set of port–port edges of `B_Z` joining a class-`a` port of `Q*_Z` to
a class-`b` port of `Q*_Z`. … Apply Lemma s6:lemPAR … The edges of `S_a` are assigned to class
`a` … (2b) For each class `Y` let `R^0_Y` consist of all centre–port edges `hu ∈ B_Z`
(`Z ∈ Std_l`) with `Y(u) = Y`, together with all port–port edges assigned to `Y` in (2a). Every
edge of `R^0_Y` has exactly one end that is a class-`Y` port of some `Q*_Z`, its port; its other
end is its centre. … centres of class-`Y` edges lie outside `V(Y)`, while ports lie in `V(Y)` …
For each `Y` and each vertex `h` that is the centre of an odd number of edges of `R^0_Y`, move one
such edge (any one) into `J_l`. Let `R_Y` be the rest: the realized class-`Y` beads. Finally,
`J_l` consists of all edges `J'_ab(Z)` and all moved edges. … So after the moves every centre has
even degree in every `R_Y`. … This proves (s6:eqJbound)." Step 3: "Every edge `hu ∈ R_Y` lies in
`Bead_{Y,l}`". Lemma J⁺ (J1): "For each hub `h ∈ D_l` and each class `Y`, `J_l` contains at most
one `J^hub`-edge of class `Y` at `h`, aggregated over all parts of round `l`."

Conclusion: `J_l` (`J`) and the family `R_Y` (`R Y`) with `⋃_Z B_Z = J ⊔ ⨆_Y R Y`; the port/centre
structure of the edges of `R Y`; even degree of every vertex outside `V(Y)` (the centres) in
`R Y`; `R Y ⊆ Bead_{Y,l}`; (J1) at hubs, aggregated (the target, also a field of `JPlusProps`);
(s6:eqJbound); `JPlusProps`. The hypotheses are those of JS-LC used by Steps 1–2: a valid run
under `Γ2(a)` (Lemma s2:lemCap(ii) for (J2)), a designation, any stage data. -/
def JslcStep2Statement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (Dstar : ℝ) (run : Run V)
    (δ : Designation V) (S : StageData V) (l : ℕ) (B : Addr → Finset (Sym2 V)),
    Gamma2a Dstar → run.Valid G Dstar → IsDesignation run G δ → 3 ≤ l → l ≤ run.R →
    (∀ a ∈ run.Std G l, B a ⊆ run.E G l a ∧ ∀ e ∈ B a, ∃ u ∈ qs run G δ S l a, u ∈ e) →
    ∃ (J : Finset (Sym2 V)) (R : PartId → Finset (Sym2 V)),
      J ⊆ (run.Std G l).biUnion B ∧
      (∀ Y, R Y ⊆ (run.Std G l).biUnion B) ∧
      (∀ e ∈ (run.Std G l).biUnion B, e ∈ J ∨ ∃ Y, e ∈ R Y) ∧
      (∀ Y, Disjoint J (R Y)) ∧
      (∀ Y Y', Y ≠ Y' → Disjoint (R Y) (R Y')) ∧
      (∀ Y, ∀ e ∈ R Y, ∃ a ∈ run.Std G l, e ∈ run.E G l a ∧
        ∃ h u, e = s(h, u) ∧ u ∈ qs run G δ S l a ∧ δ l u = Y ∧ h ∉ run.ancVerts G Y) ∧
      (∀ Y, ∀ h ∉ run.ancVerts G Y, Even (degE (R Y) h)) ∧
      (∀ Y, R Y ⊆ Bead run G δ Y l) ∧
      (∀ h ∈ run.D G l, ∀ Y : PartId, (J.filter (IsJhubEdge run G δ S l h Y)).card ≤ 1) ∧
      (J.card : ℝ) ≤ jBound run G δ S l ∧
      JPlusProps run G δ S l J

/-- [s6:lemJSLC:proof-step-7] (a proof-internal fact of [s6:lemJSLC], not the lemma: proof,
Step 7, the disjointness hypotheses of Lemmas s6:lemHCCP and s6:lemHCCglob) "(D) … The sets
`T_j(Y,l)` are pairwise disjoint (Definition s3:defCOL(iv)). … (JC-P) … The path families for
distinct `j` lie in distinct classes `LJS_{Y,l,j}`, which are disjoint. All of them lie in
`Lend_Y ⊆ E(H_Y) ⊆ E_r(Y)`, while beads lie in `⋃_Z E_l(Z)`. These sets are disjoint by the
partition of Proposition s2:propStructure(iii). … Their path edges are pairwise disjoint: within
one `(Y,l)` and one `j`, by the joint routing …; for different `j`, because different classes are
used; for different `Y ≠ Y'`, because `E(H_Y) ∩ E(H_{Y'}) = ∅` (`E(H_Y) ⊆ E_{r(Y)}(Y)`, and these
sets are disjoint by Proposition s2:propStructure(iii)). Path edges are disjoint from beads, as
shown above."

For every round `l` (no range needed: the classes `LJS_{Y,l,j}` are empty unless
`r(Y) + 2 ≤ l ≤ R`, `j < K^JS_l`, `StageData.Coherent.ljs_eq_empty`), every ancestor `Y`: the
class `LJS_{Y,l,j}` is disjoint from every bead set `E_l(Z)`, `Z ∈ Std_l`; classes of distinct
ancestors are disjoint; classes of distinct junctions of one ancestor are disjoint; the junction
sets `T_j(Y,l)` are pairwise disjoint and lie in `V(Y)`. -/
def JslcStep7DisjStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (Dstar : ℝ) (run : Run V)
    (S : StageData V) (l : ℕ),
    run.Valid G Dstar → S.Coherent run G →
      (∀ Y ∈ run.ancestors G, ∀ j, ∀ a ∈ run.Std G l, Disjoint (S.ljs Y l j) (run.E G l a)) ∧
      (∀ Y ∈ run.ancestors G, ∀ Y' ∈ run.ancestors G, Y ≠ Y' → ∀ j j',
        Disjoint (S.ljs Y l j) (S.ljs Y' l j')) ∧
      (∀ Y j j', j ≠ j' → Disjoint (S.ljs Y l j) (S.ljs Y l j')) ∧
      (∀ Y j j', j ≠ j' → Disjoint (Tj run G S Y l j) (Tj run G S Y l j')) ∧
      (∀ Y j, Tj run G S Y l j ⊆ run.ancVerts G Y)

end EG.Spec
