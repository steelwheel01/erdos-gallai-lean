module

public import EG.Defs.Quot.Round

/-!
# Statement of Lemma MULT and of the PAR-MULT identity (manuscript s7:lemMULT) — probe P-1

Statement file (`EG/Spec/**`), unit P1 (probe P-1). Design note: `formal/work/p2b/P1.md`. Proof
(stage 2): `EG/Proof/Quot/MULT.lean`.

Manuscript v6.1, `s7.tex`, before Lemma [s7:lemMULT]: "For a HUB colour `κ`, a hub `h` and
`w ∈ Pool_l`, let `m_κ(h,w)` be the number of edges `h[w]` of `B^H_κ`, that is, the number of
coloured hub items `(h,u)` of colour `κ` with junction `w`."
Lemma [s7:lemMULT] (Lemma MULT): "Let `3 ≤ l ≤ R`, `κ ∈ [4M_l]`, let `h` be a hub and let
`w ∈ Pool_{l,r}`. Then `m_κ(h,w) ≤ mult_r(w) ≤ μ_r(w)`. Moreover, the number of sub-layers
`B^{H,(ι)}_κ` (`ι ≥ 1`) in which `[w]` is not isolated equals `max_h m_κ(h,w)`, and the number of
those in which `h` is not isolated equals `max_w m_κ(h,w)`."
Preamble of the subsection "Quotient size and payments" (the PAR-MULT identity, TRIAGE §1b
S7-UNLABELLED-PAR-MULT): "For a PAR colour `κ` and `w ≠ w'` in `Pool_l`, let `m_κ(w,w')` be the
number of edges `[w][w']` of `B^P_κ`. As in Lemma s7:lemMULT, `[w]` is not isolated in exactly
`max_{w'} m_κ(w,w')` of the sub-layers `B^{P,(ι)}_κ`."

Formal reading.
* Round level (`MultStatement`, `MultSublayerStatement`, `ParMultSublayerStatement`): every valid
  past `I`, every valid choice `R` of the fixed rules and every `ξ`. `m_κ(h,w) = R.mHub ξ κ h w`,
  `m_κ(w,w') = R.mPar ξ κ w w'` (Defs). `Pool_{l,r} = {w ∈ I.pool : I.poolRound w = r}`,
  `mult_r(w) = I.multAt r w` (the number of ancestors `Y ∈ I.ancs` of round `r` with
  `w ∈ V(Y)`). "`max_h`" is `Finset.sup` over the hubs `I.hubs`, "`max_w`" over `Pool_l`, and
  "`max_{w'}`" over `Pool_l \ {w}` (all `0` on an empty set).
* "The number of sub-layers `B^{(ι)}` in which the copy `x` is not isolated" is the number of ranks
  `ι` such that the copy `(t ι, x)` is a vertex of `Q_l` (isolated copies are deleted from `Q_l`,
  so "not isolated in the sub-layer" is "a vertex of `Q_l`"), `t ι` being the tag of the copy in
  the sub-layer of rank `ι`: `hubTag κ ι false` for `[w]`, `hubTag κ ι true` for `h`,
  `parTag κ ι` for a PAR copy `[w]` (`subLayerRanks` below).
* Run level (`MultRunStatement`): the second inequality `mult_r(w) ≤ μ_r(w)` concerns the run
  (`run.mult`, `run.mu`, s2:defAncestors). The past is `RoundInput.ofPast run G δ S π l J`;
  J⁺ enters as the hypothesis `(RoundInput.ofPast …).Valid` (probe P-1 assumes J⁺; the
  instantiation `ofPast_valid` is deferred, TRIAGE §4 row P-1). `Pool_{l,r} = Stage1.poolSet G π l r`,
  the hubs are `D_l = run.D G l`.
-/

@[expose] public section

namespace EG.Spec

open EG.Quot

/-- The ranks `ι` of the sub-layers in which the copy `(t ι, x)` of `x` is a vertex of the
quotient `Q` (for a tag family `t : ℕ → QTag`, e.g. `fun ι => hubTag κ ι false` for the junction
copies `[w]` of the HUB layer of colour `κ`): "the sub-layers `B^{(ι)}` in which `[x]` is not
isolated". Every vertex of `Q` has a tag `(kind, κ, ι, side)`, and the filter keeps the copies of
`x` whose tag is `t` of their own rank `ι`. -/
def subLayerRanks {V : Type*} [DecidableEq V] (Q : FGraph (QVert V)) (t : ℕ → QTag) (x : V) :
    Finset ℕ :=
  (Q.verts.filter (fun q => q.1 = t q.1.2.2.1 ∧ q.2 = x)).image (fun q => q.1.2.2.1)

/-- [s7:lemMULT] (first inequality, round level) "Let `3 ≤ l ≤ R`, `κ ∈ [4M_l]`, let `h` be a hub
and let `w ∈ Pool_{l,r}`. Then `m_κ(h,w) ≤ mult_r(w)`." -/
def MultStatement : Prop :=
  ∀ (V : Type) [DecidableEq V] (I : RoundInput V), I.Valid → ∀ R : Rules I, R.Valid →
    ∀ (ξ : Xi I.G I.M) (κ : ℕ) (h w : V) (r : ℕ), κ < 4 * I.M → h ∈ I.hubs →
      w ∈ I.pool → I.poolRound w = r → R.mHub ξ κ h w ≤ I.multAt r w

/-- [s7:lemMULT] (second statement) "Moreover, the number of sub-layers `B^{H,(ι)}_κ` (`ι ≥ 1`)
in which `[w]` is not isolated equals `max_h m_κ(h,w)`, and the number of those in which `h` is not
isolated equals `max_w m_κ(h,w)`." (`h` a hub, `w ∈ Pool_l`, `κ ∈ [4M_l]`.) -/
def MultSublayerStatement : Prop :=
  ∀ (V : Type) [DecidableEq V] (I : RoundInput V), I.Valid → ∀ R : Rules I, R.Valid →
    ∀ (ξ : Xi I.G I.M) (κ : ℕ), κ < 4 * I.M →
      (∀ w ∈ I.pool, (subLayerRanks (R.Q ξ) (fun ι => hubTag κ ι false) w).card =
          I.hubs.sup (fun h => R.mHub ξ κ h w)) ∧
      (∀ h ∈ I.hubs, (subLayerRanks (R.Q ξ) (fun ι => hubTag κ ι true) h).card =
          I.pool.sup (fun w => R.mHub ξ κ h w))

/-- [s7] (PAR-MULT identity, preamble of "Quotient size and payments"; TRIAGE §1b
S7-UNLABELLED-PAR-MULT) "For a PAR colour `κ` and `w ≠ w'` in `Pool_l`, let `m_κ(w,w')` be the
number of edges `[w][w']` of `B^P_κ`. As in Lemma s7:lemMULT, `[w]` is not isolated in exactly
`max_{w'} m_κ(w,w')` of the sub-layers `B^{P,(ι)}_κ`." (`κ ∈ [3M_l]`, `w ∈ Pool_l`, the maximum
over `w' ∈ Pool_l \ {w}`.) -/
def ParMultSublayerStatement : Prop :=
  ∀ (V : Type) [DecidableEq V] (I : RoundInput V), I.Valid → ∀ R : Rules I, R.Valid →
    ∀ (ξ : Xi I.G I.M) (κ : ℕ), κ < 3 * I.M → ∀ w ∈ I.pool,
      (subLayerRanks (R.Q ξ) (fun ι => parTag κ ι) w).card =
        (I.pool.erase w).sup (fun w' => R.mPar ξ κ w w')

/-- [s7:lemMULT] (both inequalities, run level) "Let `3 ≤ l ≤ R`, `κ ∈ [4M_l]`, let `h` be a hub
and let `w ∈ Pool_{l,r}`. Then `m_κ(h,w) ≤ mult_r(w) ≤ μ_r(w)`." The past of round `l` is
`RoundInput.ofPast run G δ S π l J`; the J⁺ properties (and the other properties of the past that
the round step uses) are the hypothesis `(RoundInput.ofPast …).Valid` (probe P-1 assumes J⁺).
**Conditional statement** (fix round 1, review issue M1): the hypothesis `(ofPast …).Valid`
bundles s6:lemJplus, s7:lemCand (iv) and s2:propStructure (iii); its discharge, `ofPast_valid`, is an
open obligation of the joint s6/s7 unit (work/p2b/P1.md §3, §6, OBL-P1-1) that no Spec states yet,
and the hypotheses of this statement have not been shown satisfiable for `3 ≤ l ≤ R` (P1.md H4).
This is the TeX's run-level claim only modulo `ofPast_valid`.
The hypothesis `w ∈ Stage1.poolSet G π l r` does not require `1 ≤ r` and `r + 2 ≤ l` (the range of
`Pool_l = ⋃_{r=1}^{l-2} Pool_{l,r}`), because `π` is arbitrary. For such an `r` the vertex `w` is
outside `Pool_l`, so it is never a junction and `m_κ(h,w) = 0`; the statement is then harmlessly
stronger than the TeX. Adding the two bounds as hypotheses would only weaken it, so they are not
added (second review of P1, cosmetic C3). -/
def MultRunStatement : Prop :=
  ∀ (V : Type) [DecidableEq V] (run : HB.Run V) (G : FGraph V) (δ : Chain.Designation V)
    (S : Chain.StageData V) (π : ↥G.verts → Option (ℕ × ℕ)) (l : ℕ) (J : Finset (Sym2 V)),
    3 ≤ l → l ≤ run.R → (RoundInput.ofPast run G δ S π l J).Valid →
    ∀ R : Rules (RoundInput.ofPast run G δ S π l J), R.Valid →
    ∀ (ξ : Xi G (run.M G l)) (κ : ℕ) (h w : V) (r : ℕ), κ < 4 * run.M G l → h ∈ run.D G l →
      w ∈ Stage1.poolSet G π l r →
        R.mHub ξ κ h w ≤ run.mult G r w ∧ run.mult G r w ≤ run.mu G r w

end EG.Spec
