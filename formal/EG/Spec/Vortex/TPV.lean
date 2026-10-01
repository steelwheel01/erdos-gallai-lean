module

public import EG.Defs.Probe.S4.TPV

/-!
# Statement of Lemma TPV, the transparent P-vortex, deterministic form (manuscript s4:lemTPV)

Statement file (`EG/Spec/**`) of the P2 s4 Spec unit (`formal/work/p2s/s4.md`); blueprint s4,
node s4:lemTPV. Hypotheses and conclusion as named predicates: `EG/Defs/Probe/S4/TPV.lean`.

Manuscript v6.1, `s4.tex`, Lemma [s4:lemTPV] (Lemma TPV (transparent P-vortex)):
"Let `Z` be a set of `N ≥ N_0` vertices and `L := log₂N`. Let `O` be a spanning
`(ε_O,s)`-expander on `Z` with `ε_O ∈ [2^{-7},2^{-5}]` (only `ε_O ≥ 2^{-7}` is used in the proof)
and `s ≥ 2^{150}L^{42}`, and let `Z = P ⊔ Q` be a partition. Put `J := ⌊log₂(L/6)⌋`,
`k := 3J+1`, `m := ⌈L^6⌉`, `b := ⌈2^8L^2m⌉`, `t := 2^{10}L^8`, (`b` is the bound of Lemma HB at
the worst case `ε_O = 2^{-7}`), and fix, as a function of `O` only, sets `A(w) ⊆ N_O(w)` (`w ∈ Z`)
with `|A(w)| = m` such that every vertex lies in at most `b` of them (they exist by Lemma
s3:lemHB; see the proof). The *labels* of the run are the following independent random variables:
(a) a uniform colouring of `E(O)` with the `k` colours `R_{j,c}` (`0 ≤ j < J`, `c ∈ [3]`) and
`M`; …
(b) for every `v ∈ P` a level `lev(v) ∈ {0,1,…,J}` with `P(lev(v) ≥ j) = 2^{-j}` for `0 ≤ j ≤ J`
(…);
(c) for every `v ∈ Z` a label `κ(v) ∈ {0,1,2,3}` with `P(κ(v) = 0) = 1/2` and `P(κ(v) = c) = 1/6`
for `c ∈ [3]`.
Put `U_j := Q ∪ {v ∈ P : lev(v) ≥ j}`, `W_j := {v ∈ P : lev(v) = j}`,
`Z_j := {u ∈ U_{j+1} : κ(u) = 0}` and `V_{j,c} := {u ∈ U_{j+1} : κ(u) = c}`. There is an event
`𝒢_TPV`, determined by `(Z,O,P)` and the labels only, with
(s4:eqTPVprob) `P(𝒢_TPV) ≥ 1/2 − η_TPV(N)`,
`η_TPV(N) := 2LN^{-5} + 2^{96}L^{31}N^{-3} + NL e^{-3L^4/8} ≤ 1/100`,
such that on `𝒢_TPV` the following holds for *every* edge set `E` with `E(O) ⊆ E` all of whose
edges have both ends in `Z`: there is a partition `E = E^V ⊔ E^Q` with the properties
(T1) every edge of `E` with both ends in `P` lies in `E^V`;
(T2) every edge of `E^V` with an end in `Q` is an edge of `O`;
(T3) `E^V` decomposes into at most `169|P|` objects, and `E^V = ∅` if `P = ∅`;
(T4) (no arcs) all objects of (T3) consist of edges of `E`; every path formed during the run is
closed into a cycle within the step in which it is formed, so the run leaves no path ("arc") to be
closed by any other device.
The partition and the decomposition are obtained from `E` and the labels by a deterministic
procedure."

Formal reading (TRIAGE §2.8 and §2.12, decision TPV-DET-SPEC "TPV, PV and VX⁺ are
deterministic"; blueprint s4 lemTPV).
* **Deterministic form.** The conclusion (T1)–(T4) does not mention the labels, and
  `P(𝒢_TPV) ≥ 1/2 − η_TPV(N) ≥ 1/2 − 1/100 > 0` forces `𝒢_TPV ≠ ∅`; so the lemma implies "for every
  admissible `E` there is a partition with (T1)–(T4)". Conversely that statement gives the lemma
  with `𝒢_TPV` := the whole label space (probability `1 ≥ 1/2 − η_TPV(N)`). Hence, given the
  hypotheses, the two are equivalent. The consumers (s6:thmMIXC, s7:lemOneOutcome) use only
  non-emptiness of `𝒢_TPV`. The parameters `J, k, m, b, t`, the family `A(w)`, the labels, the
  sets `U_j, …, V_{j,c}` and the event `𝒢_TPV` with its probability bound are proof internals
  (Lib); the meta-claims "determined by `(Z,O,P)` and the labels" and "obtained … by a
  deterministic procedure" are not stated (as for Lemma PV, `EG.Spec.PVStatement`).
* **Hypotheses** `EG.Vortex.TPVHyp Z O P εO s` (`N ≥ N_0` as `TPVSize Z.card`; `O.verts = Z`,
  `O.IsExpander εO s`, `2^{-7} ≤ εO ≤ 2^{-5}`, `2^{150}L^{42} ≤ s`, `P ⊆ Z`, `Q = Z \ P`).
* **Admissible edge sets** `EG.Vortex.TPVAdm Z O E` (loopless, ends in `Z`, `E(O) ⊆ E`).
* **Conclusion** `EG.Vortex.TPVConcl Z O P E` ((T1)–(T4); module docstring of
  `EG/Defs/Probe/S4/TPV.lean`).
* Consumer form (TRIAGE §2.8, blueprint s6b MixC `S4.TPVGood (Z) (O) (P)`): MIX-C applies the
  Spec at `(Z^0_Z, O_Z, Ret_Z)` and needs, for every admissible `E`, the partition `E^V ⊔ E^Q`
  with (T1)–(T3); `∀ E, TPVAdm Z O E → TPVConcl Z O P E` is that predicate (with the loopless
  hypothesis, which every `E ⊆ E(G)` meets).
-/

@[expose] public section

namespace EG.Spec

universe u

/-- [s4:lemTPV] Lemma TPV (transparent P-vortex), deterministic form: if `Z` has `N ≥ N_0`
vertices (`TPVSize`), `O` is a spanning `(ε_O,s)`-expander on `Z` with `ε_O ∈ [2^{-7},2^{-5}]`
and `s ≥ 2^{150}L^{42}`, and `Z = P ⊔ (Z \ P)`, then for every edge set `E ⊇ E(O)` inside `Z`
there is a partition `E = E^V ⊔ E^Q` with (T1)–(T4) (module docstring). -/
def TPVStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (Z : Finset V) (O : FGraph V) (P : Finset V) (εO s : ℝ),
    Vortex.TPVHyp Z O P εO s →
    ∀ E : Finset (Sym2 V), Vortex.TPVAdm Z O E → Vortex.TPVConcl Z O P E

end EG.Spec
