module

public import EG.Proof.Chain.JSLCStep2Par
public import EG.Proof.Chain.JSLCTypes
public import EG.Lib.Chain.JSet

/-!
# JS-LC Step 2: the construction of `J_l` and of the realized beads `R_Y`
(manuscript s6:lemJSLC, proof, Step 2)

Probe unit P2J (probe P-2, part 2), proof round 1. The objects of Step 2, for fixed run `run`,
graph `G`, designation `δ`, stage data `S`, round `l` and input `B` (`B a = B_Z`, `Z ∈ Std_l`):
* `IsPP a e`: `e` is a *port–port edge* of the part `a` (both ends in `Q*_Z`);
* `Epp a p`: the port–port edges of `B_Z` whose ends have the classes `p = {a, b}` (`E_ab(Z)`);
* `parJ a p`, `parAsg a p`: the deletion `J'_ab(Z)` and the assignment `S_a ⊔ S_b` of Lemma PAR
  for `E_ab(Z)` (`EG.Chain.exists_parLocal`, "with any admissible choice of the deleted edges");
* `Jpar`: all PAR deletions `J'_ab(Z)`;
* `R0 Y`: "all centre–port edges `hu ∈ B_Z` (`Z ∈ Std_l`) with `Y(u) = Y`, together with all
  port–port edges assigned to `Y` in (2a)";
* `oddC Y`: the vertices `h ∉ V(Y)` of odd degree in `R^0_Y` ("each vertex `h` that is the centre
  of an odd number of edges of `R^0_Y`");
* `mv Y h`: the moved edge ("move one such edge (any one) into `J_l`"); `Moved Y`;
* `Jmov`: all moved edges; `J := Jpar ∪ Jmov`; `R Y := R^0_Y \ Moved Y` ("the realized class-`Y`
  beads").

The hypotheses used by the proof are bundled in `Step2Hyp` (they are the hypotheses of JS-LC,
Lemma EL through `EG.jslcTypes`, and Lemma s2:lemCap(ii)).
-/

public section

namespace EG.Chain.Step2

open EG.HB

variable {V : Type*} [DecidableEq V] (run : Run V) (G : FGraph V) (δ : Designation V)
  (S : StageData V) (l : ℕ) (B : Addr → Finset (Sym2 V))

/-- The facts used by Step 2: the hypotheses of JS-LC (round `l ≥ 3`, a designation, the input
`B`), the Step 1 facts (`EG.jslcTypes`: ends in `Ret_Z ∪ Q*_Z`, Lemma EL, classes of port–port
edges differ), and Lemma s2:lemCap(ii) (degree at most `M_l − 1` in every `E_l(Z)`). -/
structure Step2Hyp : Prop where
  l3 : 3 ≤ l
  hδ : IsDesignation run G δ
  hB : ∀ a ∈ run.Std G l, B a ⊆ run.E G l a ∧ ∀ e ∈ B a, ∃ u ∈ qs run G δ S l a, u ∈ e
  ends : ∀ a ∈ run.Std G l, ∀ e ∈ run.E G l a, ∀ v ∈ e,
    v ∈ ret run G δ S l a ∨ v ∈ qs run G δ S l a
  el : ∀ a ∈ run.Std G l, ∀ u ∈ run.classed G l a, ∀ h : V, s(h, u) ∈ run.E G l a →
    h ∉ run.ancVerts G (δ l u)
  pp : ∀ a ∈ run.Std G l, ∀ u ∈ run.classed G l a, ∀ v ∈ run.classed G l a,
    s(u, v) ∈ run.E G l a → δ l u ≠ δ l v
  cap : ∀ a ∈ run.Std G l, ∀ v : V, degE (run.E G l a) v ≤ run.M G l - 1

/-- `e` is a port–port edge of the part `a`: both ends lie in `Q*_Z`. -/
@[expose] def IsPP (a : Addr) (e : Sym2 V) : Prop := ∀ w ∈ e, w ∈ qs run G δ S l a

open Classical in
/-- "`E_ab(Z)`: the set of port–port edges of `B_Z` joining a class-`a` port of `Q*_Z` to a
class-`b` port of `Q*_Z`", for the unordered pair of classes `p = {a, b}`. -/
@[expose] noncomputable def Epp (a : Addr) (p : Sym2 PartId) : Finset (Sym2 V) :=
  (B a).filter (fun e => IsPP run G δ S l a e ∧ e.map (δ l) = p)

/-- The PAR deletion `J'_ab(Z)` (any admissible choice). -/
@[expose] noncomputable def parJ (a : Addr) (p : Sym2 PartId) : Finset (Sym2 V) :=
  (exists_parLocal (δ l) (Epp run G δ S l B a p) p).choose

/-- The PAR assignment of the edges of `E_ab(Z) \ J'_ab(Z)` to the classes `a`, `b`. -/
@[expose] noncomputable def parAsg (a : Addr) (p : Sym2 PartId) : Sym2 V → PartId :=
  (exists_parLocal (δ l) (Epp run G δ S l B a p) p).choose_spec.choose

theorem parJ_spec (a : Addr) (p : Sym2 PartId) :
    parJ run G δ S l B a p ⊆ Epp run G δ S l B a p ∧
      ((∀ e ∈ Epp run G δ S l B a p, e.map (δ l) = p) → ¬ p.IsDiag →
        2 * (parJ run G δ S l B a p).card ≤ (edgeVerts (Epp run G δ S l B a p)).card ∧
        (∀ e ∈ Epp run G δ S l B a p, parAsg run G δ S l B a p e ∈ p) ∧
        ∀ v Y, δ l v ≠ Y → Even ((Epp run G δ S l B a p \ parJ run G δ S l B a p).filter
          (fun e => v ∈ e ∧ parAsg run G δ S l B a p e = Y)).card) :=
  (exists_parLocal (δ l) (Epp run G δ S l B a p) p).choose_spec.choose_spec

open Classical in
/-- All PAR deletions: `⋃_Z ⋃_{a,b} J'_ab(Z)`. -/
@[expose] noncomputable def Jpar : Finset (Sym2 V) :=
  (run.Std G l).biUnion (fun a => (B a).filter (fun e =>
    IsPP run G δ S l a e ∧ e ∈ parJ run G δ S l B a (e.map (δ l))))

/-- An edge of `B_Z` (address `a`) is in `R^0_Y`: a centre–port edge whose port has class `Y`,
or a port–port edge not deleted by PAR and assigned to `Y`. -/
@[expose] def InR0 (Y : PartId) (a : Addr) (e : Sym2 V) : Prop :=
  (¬ IsPP run G δ S l a e ∧ ∃ u ∈ qs run G δ S l a, u ∈ e ∧ δ l u = Y) ∨
  (IsPP run G δ S l a e ∧ e ∉ parJ run G δ S l B a (e.map (δ l)) ∧
    parAsg run G δ S l B a (e.map (δ l)) e = Y)

open Classical in
/-- "`R^0_Y`: all centre–port edges `hu ∈ B_Z` (`Z ∈ Std_l`) with `Y(u) = Y`, together with all
port–port edges assigned to `Y` in (2a)". -/
@[expose] noncomputable def R0 (Y : PartId) : Finset (Sym2 V) :=
  (run.Std G l).biUnion (fun a => (B a).filter (InR0 run G δ S l B Y a))

open Classical in
/-- The vertices outside `V(Y)` of odd degree in `R^0_Y` ("each vertex `h` that is the centre of
an odd number of edges of `R^0_Y`"). -/
@[expose] noncomputable def oddC (Y : PartId) : Finset V :=
  (edgeVerts (R0 run G δ S l B Y)).filter (fun h =>
    h ∉ run.ancVerts G Y ∧ Odd (degE (R0 run G δ S l B Y) h))

open Classical in
/-- The moved edge at `(h, Y)` ("move one such edge (any one) into `J_l`"). -/
@[expose] noncomputable def mv (Y : PartId) (h : V) : Sym2 V :=
  if hx : ∃ e ∈ R0 run G δ S l B Y, h ∈ e then hx.choose else s(h, h)

/-- The moved edges of class `Y`. -/
@[expose] noncomputable def Moved (Y : PartId) : Finset (Sym2 V) :=
  (oddC run G δ S l B Y).image (mv run G δ S l B Y)

/-- The classes of the classed non-lost ports of round `l`. -/
@[expose] noncomputable def classes : Finset PartId := (qsRound run G δ S l).image (δ l)

/-- All moved edges. -/
@[expose] noncomputable def Jmov : Finset (Sym2 V) :=
  (classes run G δ S l).biUnion (Moved run G δ S l B)

/-- "Finally, `J_l` consists of all edges `J'_ab(Z)` and all moved edges." -/
@[expose] noncomputable def J : Finset (Sym2 V) := Jpar run G δ S l B ∪ Jmov run G δ S l B

/-- "Let `R_Y` be the rest: the *realized class-`Y` beads*." -/
@[expose] noncomputable def R (Y : PartId) : Finset (Sym2 V) :=
  R0 run G δ S l B Y \ Moved run G δ S l B Y

/-! ### Basic facts -/

variable {run G δ S l B}

theorem mem_Epp {a : Addr} {p : Sym2 PartId} {e : Sym2 V} :
    e ∈ Epp run G δ S l B a p ↔ e ∈ B a ∧ IsPP run G δ S l a e ∧ e.map (δ l) = p := by
  classical
  unfold Epp
  rw [Finset.mem_filter]

theorem mem_Jpar {e : Sym2 V} :
    e ∈ Jpar run G δ S l B ↔ ∃ a ∈ run.Std G l, e ∈ B a ∧ IsPP run G δ S l a e ∧
      e ∈ parJ run G δ S l B a (e.map (δ l)) := by
  classical
  unfold Jpar
  simp only [Finset.mem_biUnion, Finset.mem_filter]

theorem mem_R0 {Y : PartId} {e : Sym2 V} :
    e ∈ R0 run G δ S l B Y ↔ ∃ a ∈ run.Std G l, e ∈ B a ∧ InR0 run G δ S l B Y a e := by
  classical
  unfold R0
  simp only [Finset.mem_biUnion, Finset.mem_filter]

theorem mem_oddC {Y : PartId} {h : V} :
    h ∈ oddC run G δ S l B Y ↔ h ∈ edgeVerts (R0 run G δ S l B Y) ∧
      h ∉ run.ancVerts G Y ∧ Odd (degE (R0 run G δ S l B Y) h) := by
  classical
  unfold oddC
  rw [Finset.mem_filter]

theorem mv_spec {Y : PartId} {h : V} (hx : ∃ e ∈ R0 run G δ S l B Y, h ∈ e) :
    mv run G δ S l B Y h ∈ R0 run G δ S l B Y ∧ h ∈ mv run G δ S l B Y h := by
  classical
  unfold mv
  rw [dif_pos hx]
  exact hx.choose_spec

theorem exists_mem_of_mem_oddC {Y : PartId} {h : V} (hh : h ∈ oddC run G δ S l B Y) :
    ∃ e ∈ R0 run G δ S l B Y, h ∈ e := by
  obtain ⟨hv, -, -⟩ := mem_oddC.1 hh
  unfold edgeVerts at hv
  obtain ⟨e, he, hhe⟩ := Finset.mem_biUnion.1 hv
  exact ⟨e, he, Sym2.mem_toFinset.1 hhe⟩

theorem mem_J {e : Sym2 V} : e ∈ J run G δ S l B ↔ e ∈ Jpar run G δ S l B ∨
    e ∈ Jmov run G δ S l B := Finset.mem_union

theorem mem_Jmov {e : Sym2 V} : e ∈ Jmov run G δ S l B ↔
    ∃ Y ∈ classes run G δ S l, ∃ h ∈ oddC run G δ S l B Y, mv run G δ S l B Y h = e := by
  unfold Jmov Moved
  simp only [Finset.mem_biUnion, Finset.mem_image]

theorem mem_classes {Y : PartId} : Y ∈ classes run G δ S l ↔
    ∃ a ∈ run.Std G l, ∃ u ∈ qs run G δ S l a, δ l u = Y := by
  unfold classes qsRound
  simp only [Finset.mem_image, Finset.mem_biUnion]
  constructor
  · rintro ⟨u, ⟨a, ha, hu⟩, rfl⟩; exact ⟨a, ha, u, hu, rfl⟩
  · rintro ⟨a, ha, u, hu, rfl⟩; exact ⟨u, ⟨a, ha, hu⟩, rfl⟩

end EG.Chain.Step2
