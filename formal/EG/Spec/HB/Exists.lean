module

public import EG.Defs.HB.Run
public import EG.Defs.Gamma.Core

/-!
# Statements of Proposition "existence and termination" (manuscript s2:propExists)

Statement file (`EG/Spec/**`) of the P2 s2b Spec unit (`formal/work/p2s/s2b.md`); blueprint s2b,
node s2:propExists. Definitions: `EG/Defs/HB/Witness.lean`, `SplitTree.lean`, `Round.lean`,
`Run.lean`, `EG/Defs/Gamma/Core.lean` (locked).

Manuscript v6.1, `s2.tex`, Proposition [s2:propExists]:
"For every graph `G` a valid `HB*^{τ+}` run exists, and every sequence of admissible choices
terminates. More precisely: within a round, (R1) and the first level of (R3) terminate; the
`τ`-runs terminate with any witnesses (`U' ≠ ∅` and `n_1, n_2 < m` at every split); (GC) is a
deterministic relabelling that feeds back into neither `D_l` nor `home` nor the guest sets; and
`d_{l+1} < d_l` while `d_l ≥ D_*`, so `R` is finite."
and, from the proof: "The proofs of Lemma s2:lemCap(ii), Proposition s2:propOV and Proposition
s2:propDegRec use only the data of the round `l` in question and `d_l ≥ D_*`; so they apply to
every round `l` with `d_l ≥ D_*` of any (possibly unfinished) execution of the procedure." (This
is the round-level form of those Specs: `CapRoundStatement`, `OVRoundStatement`,
`DegRecRoundStatement`, `DegRecKindsRoundStatement`; TRIAGE §2.2.)

Where each part is stated (five statements, this file).
* "within a round, (R1) and the first level of (R3) terminate": `RoundStepsStatement`. With
  finite lists and trees in the data model, "terminates for every admissible choice" becomes
  "for every rule choosing the admissible objects, the finite object exists": (R1) a maximal
  family of edge-disjoint long cycles exists (TRIAGE §2.12 "(R1) as any maximal family"; greedy
  deletion terminates because each step deletes an edge); for every rule `W` choosing a witness
  with parameter `0` at every graph that is not an `(ε,0)`-expander, the `s = 0` recursion that
  uses these witnesses and stops exactly at `(ε,0)`-expanders is a finite tree (the same shape as
  (T2) of `EG.Spec.L14TermStatement`).
* "the `τ`-runs terminate with any witnesses (`U' ≠ ∅` and `n_1, n_2 < m` at every split)":
  `RoundTauTermStatement`, for a round whose (R1) and first level of (R3) are done (valid cycles,
  valid `s = 0` recursion) with `d_l ≥ D_*`: at every big piece `𝒫` the hypotheses of Lemma
  14^τ hold (`s_l ≥ 1`, `τ_l ≥ 128 s_l log²|𝒫|`), every `τ`-rule split of a graph `K` with
  `2 ≤ |K| ≤ |𝒫|` has `U' ≠ ∅` and both children with fewer than `|K|` vertices
  (`n_1 = |U' ∪ N''| = |splitFst|`, `n_2 = m − |U'| = |splitSnd|`), and for every witness rule the
  `τ`-run using it exists. The `τ`-run trees are not yet chosen at this point, so the hypothesis is
  not `Round.Valid` (which contains them) but its first-level part.
* "(GC) is a deterministic relabelling that feeds back into neither `D_l` nor `home` nor the guest
  sets": a property of the definitions, not a proposition. `EG.HB.Round.D`, `home`, `guests`,
  `prePartAddrs`, `Z0`, `X0` do not mention `isL1`, `isL2`, `isGC`, `isLight` (checked in
  `EG/Defs/HB/Round.lean`; blueprint EX-GC-DEFINITIONAL, TRIAGE §2.2 design constraint). No Spec.
* "All required choices (witnesses, vertex orders, home orders) exist. So each round is a finite
  procedure" (proof): `RoundExistsStatement` (a valid round exists on every input graph with
  `d ≥ D_*`).
* "`d_{l+1} < d_l` while `d_l ≥ D_*`, so `R` is finite" and "every sequence of admissible choices
  terminates": `RunTerminatesStatement`: for every list of round choices each of which is a valid
  round on the graph produced by the previous ones, with `d_l ≥ D_*` at every listed round (an
  execution that has not stopped yet, not a valid run), `d_{l+1} < d_l` at every listed round and
  the number of rounds is at most `|E(G)|`.
* "For every graph `G` a valid `HB*^{τ+}` run exists": `ExistsRunStatement`.

Formal reading.
* Condition on `D_*`. The statement has no hypothesis on `D_*`, but it is false without Γ1
  (blueprint EX-GAMMA-NEEDED, TRIAGE §1b "EX-GAMMA-NEEDED, MAIN-PROPEXISTS-HYPS", class T0: for
  `D_* = 2^{117}` and `G = K_m`, `m = 2^{117} + 1`, every round passes all edges down and the
  procedure never stops). `D_*` is by definition a constant satisfying Γ1–Γ4, and the proof uses
  Γ1 through Proposition s2:propDegRec (`d_{l+1} < d_l`) and Γ2(a) through Lemma s2:lemCap(ii)
  (`τ_l ≥ 128 s_l log²|𝒫|`). So: `RunTerminatesStatement` and `ExistsRunStatement` carry
  `Gamma1core Dstar`; `RoundTauTermStatement` and `RoundExistsStatement` need only lemCap(ii) and
  carry `Gamma2a Dstar` (a weaker hypothesis, so a stronger statement); `RoundStepsStatement`
  needs no condition on `D_*`.
* "graph `G`": an `FGraph V` (finite, simple, loopless) on any type `V` with decidable equality;
  `n = |V(G)|` may be `0` (then `d_1 = 0 < D_*` and the empty run is valid).
* Witness rules are functions `W : Addr → FGraph V → Finset V × Finset (Sym2 V)` (the choice may
  depend on the address of the node); "admissible" = `W a K` is a witness at `K` whenever `K` is
  not an expander with the relevant parameter. `ε = EG.epsC = 2^{-5}`.
* Rounds of a choice list `cs` are those of the run `Run.mk cs` (`R = cs.length`); the choices of
  round `l` are `(Run.mk cs).choice l = cs[l-1]`.
-/

@[expose] public section

namespace EG.Spec

open EG.HB

universe u

/-- [s2:propExists] "within a round, (R1) and the first level of (R3) terminate" (with any
admissible choices): (R1) a family of long cycles as required by (R1) exists (a maximal family of
pairwise edge-disjoint well-formed cycles of length `≥ T_l` in `G_l`, after whose deletion no such
cycle is left); and for every rule `W` that picks a witness with parameter `0` at every graph that
is not an `(ε,0)`-expander, there is an `s = 0` recursion on any root graph `K` (= `G'_l`) that
stops exactly at `(ε,0)`-expanders and uses the witnesses of `W` at all its non-leaf nodes. -/
def RoundStepsStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V],
    (∀ H : FGraph V, ∃ cyc : List (List V),
      Round.CyclesValid H (⟨cyc, .nil, fun _ => .nil, []⟩ : RoundChoice V)) ∧
    ∀ (K : FGraph V) (W : Addr → FGraph V → Finset V × Finset (Sym2 V)),
      (∀ (a : Addr) (K' : FGraph V), ¬ K'.IsExpander epsC 0 →
        IsWitness K' epsC 0 (W a K').1 (W a K').2) →
      ∃ t : STree V, t.IsS0Rec epsC K ∧ t.StopsAt K (fun Q => Q.IsExpander epsC 0) ∧
        ∀ a ∈ t.internalAddrs,
          t.labelAt a = some ((W a (t.graphAtD K a)).1,
            (t.graphAtD K a).nbrSet (W a (t.graphAtD K a)).1)

/-- [s2:propExists] "the `τ`-runs terminate with any witnesses (`U' ≠ ∅` and `n_1, n_2 < m` at
every split)", for a round with input graph `H = G_l`, `d_l ≥ D_*` (and `Γ2(a)`, through Lemma
s2:lemCap(ii)), whose (R1) and first level of (R3) are done: at every big piece `𝒫`
(`|𝒫| ≥ P_l`), `s_l ≥ 1` and `τ_l ≥ 128 s_l log²|𝒫|`; every split by the `τ`-rules (threshold
`τ_l`) of a graph `K` with `2 ≤ |K| ≤ |𝒫|`, by a witness with parameter `s_l`, has `U' ≠ ∅` and
children with fewer than `|K|` vertices; and for every witness rule `W` (parameter `s_l`) the
`τ`-run of `𝒫` using the witnesses of `W` exists. -/
def RoundTauTermStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (H : FGraph V) (c : RoundChoice V) (Dstar : ℝ),
    Gamma2a Dstar → Dstar ≤ Round.d H → Round.CyclesValid H c →
    c.tree0.IsS0Rec epsC (Round.graph' H c) →
    c.tree0.StopsAt (Round.graph' H c) (fun Q => Q.IsExpander epsC 0) →
    ∀ q ∈ Round.bigPieceAddrs H c,
      1 ≤ sOf (Round.d H) ∧
      128 * (sOf (Round.d H) : ℝ) * Real.logb 2 (Round.piece H c q).card ^ 2 ≤
        (tauOf (Round.d H) : ℝ) ∧
      (∀ (K : FGraph V) (U N : Finset V) (F : Finset (Sym2 V)),
        2 ≤ K.card → K.card ≤ (Round.piece H c q).card →
        IsWitness K epsC (sOf (Round.d H)) U F → N = witN K U F →
          0 < (tauU1 K U N (tauOf (Round.d H))).card ∧
          (splitFst K (tauU1 K U N (tauOf (Round.d H)))
            (tauN2 K U N (tauOf (Round.d H)))).card < K.card ∧
          (splitSnd K (tauU1 K U N (tauOf (Round.d H)))
            (tauN2 K U N (tauOf (Round.d H)))).card < K.card) ∧
      ∀ W : Addr → FGraph V → Finset V × Finset (Sym2 V),
        (∀ (a : Addr) (K : FGraph V), ¬ K.IsExpander epsC (sOf (Round.d H)) →
          IsWitness K epsC (sOf (Round.d H)) (W a K).1 (W a K).2) →
        ∃ t : STree V,
          t.IsTauRun epsC (sOf (Round.d H)) (tauOf (Round.d H)) (Round.piece H c q) ∧
          ∀ a ∈ t.internalAddrs,
            t.labelAt a = some
              (tauU1 (t.graphAtD (Round.piece H c q) a)
                  (W a (t.graphAtD (Round.piece H c q) a)).1
                  (witN (t.graphAtD (Round.piece H c q) a)
                    (W a (t.graphAtD (Round.piece H c q) a)).1
                    (W a (t.graphAtD (Round.piece H c q) a)).2)
                  (tauOf (Round.d H)),
                tauN2 (t.graphAtD (Round.piece H c q) a)
                  (W a (t.graphAtD (Round.piece H c q) a)).1
                  (witN (t.graphAtD (Round.piece H c q) a)
                    (W a (t.graphAtD (Round.piece H c q) a)).1
                    (W a (t.graphAtD (Round.piece H c q) a)).2)
                  (tauOf (Round.d H)))

/-- [s2:propExists] (proof) "All required choices (witnesses, vertex orders, home orders) exist.
So each round is a finite procedure": on every input graph `H` with `d(H) ≥ D_*` (and `Γ2(a)`)
there are round choices satisfying all conditions of (R1)–(R4) (`Round.Valid`). -/
def RoundExistsStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (H : FGraph V) (Dstar : ℝ),
    Gamma2a Dstar → Dstar ≤ Round.d H → ∃ c : RoundChoice V, Round.Valid H c

/-- [s2:propExists] "every sequence of admissible choices terminates … and `d_{l+1} < d_l` while
`d_l ≥ D_*`, so `R` is finite": for every list `c_1, …, c_k` of round choices such that each `c_l`
is a valid round on the graph `G_l` produced by `c_1, …, c_{l-1}` and `d_l ≥ D_*`, we have
`d_{l+1} < d_l` for every `l ≤ k`, and `k ≤ |E(G)|` (under `Γ1` (a)–(e)). -/
def RunTerminatesStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (Dstar : ℝ) (cs : List (RoundChoice V)),
    Gamma1core Dstar →
    (∀ l ∈ Finset.Icc 1 cs.length, Dstar ≤ (Run.mk cs).d G l ∧
      Round.Valid ((Run.mk cs).graph G l) ((Run.mk cs).choice l)) →
    (∀ l ∈ Finset.Icc 1 cs.length, (Run.mk cs).d G (l + 1) < (Run.mk cs).d G l) ∧
    cs.length ≤ G.edges.card

/-- [s2:propExists] "For every graph `G` a valid `HB*^{τ+}` run exists" (under `Γ1` (a)–(e), the
standing assumption on `D_*`; module docstring). -/
def ExistsRunStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (Dstar : ℝ),
    Gamma1core Dstar → ∃ run : Run V, run.Valid G Dstar

end EG.Spec
