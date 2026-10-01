module

public import EG.Defs.Probe.P2J.PreSystem
public import EG.Defs.Chain.StageInst

/-!
# Step 6 of the proof of Lemma JS-LC: the joint-routing claims (a), (c), (d)
(manuscript s6:lemJSLC, proof)

Statement file of probe unit P2J (probe P-2, part 2; design note `formal/work/p2b/P2J.md`).
These are not separate manuscript lemmas: they are the parts of the claim "the joint-routing
facts" in Step 6 of the proof of Lemma JS-LC [s6:lemJSLC] that check the hypotheses of the
path-connectivity property (Definition 7 of B–M, `EG.FGraph.IsPathConnected`) and of Lemma HCC-P
before the paths exist. TRIAGE §4, probe P-2: "joint multiplicity `≤ 2M_l−2 ≤ t^JS`, distinct pair
ends". Label tags `[s6:lemJSLC:proof-claim-x]`: proof-internal facts of [s6:lemJSLC], not the
lemma. Claim (b) is a construction fact of Steps 4–5 (it becomes hypotheses of
`JslcJointMultStatement`); claim (e) is in `JslcTypesStatement` (`EG/Spec/Chain/JSLCSteps.lean`).

Manuscript v6.1, proof of [s6:lemJSLC], Step 6 (the definition of the junction pairs is quoted in
`EG/Defs/Probe/P2J/PreSystem.lean`) and:
"Claim (the joint-routing facts). For every lend-good `Y` with `R_Y ≠ ∅` and every `j < K^JS`:
(a) The bijections exist. Every pair consists of two distinct vertices of
`V(Y) \ ⋃_{j'} T_{j'}(Y,l)`.
(b) Every edge of `R_Y` is a bead of exactly one system of `(Y,l)`. Every port of `R_Y` is a port of
`𝒮_0(Y,l)` or of cherry systems, never of both. A port is an end of at most `M_l − 1` cherries,
and so lies in at most `M_l − 1` cherry systems.
(c) Every vertex lies in at most `max(2M_l − 2, (M_l − 1) + ⌈M_l/2⌉) = 2M_l − 2 ≤ t` pairs of
`𝔓_j(Y,l)`. …
(d) There are pairwise edge-disjoint paths in `LJS_{Y,l,j}`, one for each pair of `𝔓_j(Y,l)` and
joining its two vertices. Each has length at most `2^{12}L_Y^4` and all its interior vertices in
`T_j(Y,l)`.
(e) No port or centre of a system of `(Y,l)` lies in any `T_{j'}(Y,l)`."
Proof of the claim: "(a) In a system of depth `k ≥ 2`, the padded loads of all layers are equal
(Steps 4 and 5). By Lemma s6:lemMED(b), `Σ_{LayP_j} exc^- = Σ_{LayP_j} exc^+`. So the number of
out-units of layer `j` equals its padded load, which equals the padded load of layer `j+1`, which
is the number of its in-units. For depth `1`, `Σ exc^- = Σ exc^+`. The two vertices of a pair are
distinct: for `k ≥ 2`, the layers `j` and `j+1` consist of different, pairwise vertex-disjoint
clusters (for `k = 2`, layer `j+1` is layer `j−1 ≠ j`); for `k = 1`, `X^out ∩ X^in = ∅`. …
(c) … So at a fixed junction a port occurs in at most `max(dem⁻, dem⁺)` pairs of each system
containing it. Centres occur in no pair. By Steps 4 and 5 and part (b), a port occurs in at most
`(M_l − 1) + ⌈M_l/2⌉` pairs (if it belongs to `𝒮_0`) or at most `2(M_l − 1)` pairs (if it belongs
to cherry systems). For `M_l ≥ 2`, `⌈M_l/2⌉ ≤ M_l − 1`, so both are at most `2M_l − 2 < t = 2M_l + 2`.
(d) `Y` is lend-good. By Definition s6:defLending and Lemma s3:lemCOL(b), `LJS_{Y,l,j}` is
`(2^{12}L_Y^4, t)`-path connected through `T_j(Y,l)`, as a graph on `V(Y)`. By Cited result
s1:citDef7 (see Remark s3:remMultiset) this is a statement about every multiset of pairs of
distinct vertices of `V(Y)` in which every vertex lies in at most `t` pairs, with endpoints
unrestricted. By Lemma s3:lemMonotone(iii), the property depends only on `(LJS_{Y,l,j}, T_j(Y,l))`,
so the multiset may be chosen after the stage-1 outcome and after Steps 1–5. … Apply this to
`𝔓_j(Y,l)`, which is admissible by (a) and (c)." Step 4: "`|exc(u)| ≤ M_l − 1`", "`pad(u) ≤
⌈(M_l − 1)/2⌉ ≤ ⌈M_l/2⌉`"; Step 5: cherry systems have `exc = ±1` at their ports and "`pad ≤ 1`".

Formal reading.
* A system of `(Y,l)` before routing is `S : EG.Chain.HccpData V` with `S.PreValid G` (the HCC-P
  hypotheses without (JC-P); the path field is not read). Its junction-`j` pairs contain the
  vertex `u` exactly `S.junctionOcc j u` times.
* `JslcPairsBalanceStatement` (claim (a), "The bijections exist"): if all padded loads `Φ_j` of a
  system are equal, the number of out-units of layer `j`, `Σ_{u∈LayP_j} dem⁻(u)`, equals the number
  of in-units of layer `j+1`, `Σ_{v∈LayP_{j+1}} dem⁺(v)` (uniformly in `k`; for `k = 1` the sums are
  `Σ_{X^out} exc^-` and `Σ_{X^in} exc^+`, since `pad ≡ 0`).
* `JslcPairsDistinctStatement` (claim (a), distinct ends): an out-unit `u ∈ LayP_j`
  (`dem⁻(u) > 0`) and an in-unit `v ∈ LayP_{j+1}` (`dem⁺(v) > 0`) are distinct vertices. (That the
  ends lie in `V(Y) \ ⋃ T_{j'}(Y,l)` is `JslcTypesStatement`, first conjunct.)
* `JslcJointMultStatement` (claim (c), the **joint multiplicity**, the aggregated form handed off
  by unit P2E): for an integer `M ≥ 2` and the systems `Sys s` (`s < q`) of `(Y,l)`, with
  `cherry s` telling whether `Sys s` is a cherry system; hypotheses from Steps 4, 5 and claim (b):
  at most one non-cherry system (`𝒮_0`); at its ports `|exc| ≤ M − 1` and `pad ≤ ⌈M/2⌉`; at the
  ports of cherry systems `|exc| ≤ 1`, `pad ≤ 1`; a port of `𝒮_0` is a port of no cherry system;
  every vertex is a port of at most `M − 1` cherry systems. Conclusion: every vertex `v` lies in at
  most `2M − 2` pairs of `𝔓_j(Y,l)` (`Σ_s junctionOcc (Sys s) j v ≤ 2M − 2`), and
  `2M − 2 < 2M + 2 = t^JS` (`EG.tJS_eq_two_mul_add_two`).
* `JslcRoutingStatement` (claim (d)): for a lend-good ancestor `Y` of a round `≤ l − 2`
  (`Y ∈ lendGoodAnc run G S l`), `l ≤ R`, `j < K^JS_l`, coherent stage data, and every finite
  family of pairs of distinct vertices of `V(Y)` in which every vertex lies in at most
  `t^JS_l = Stage1.tJS G run l` pairs, there are pairwise edge-disjoint paths in `LJS_{Y,l,j}`
  (the edge set `S.ljs Y l j`), one per pair, joining its two vertices, of length at most
  `2^{12} L_Y^4`, with all interior vertices in `T_j(Y,l)`. The pairs are an indexed family (a
  multiset), chosen after the stage data (s3:lemMonotone(iii) is automatic: the statement
  quantifies over all families).
-/

@[expose] public section

namespace EG.Spec

open EG.HB EG.Chain

universe u

/-- [s6:lemJSLC:proof-claim-a] (a proof-internal fact of [s6:lemJSLC], not the lemma: proof,
joint-routing claim (a), first sentence) "The bijections exist. … In a system of depth `k ≥ 2`,
the padded loads of all layers are equal (Steps 4 and 5). By Lemma s6:lemMED(b),
`Σ_{LayP_j} exc^- = Σ_{LayP_j} exc^+`. So the number of out-units of layer `j` equals its padded
load, which equals the padded load of layer `j+1`, which is the number of its in-units. For depth
`1`, `Σ exc^- = Σ exc^+`."

For a system `S` with the HCC-P hypotheses other than (JC-P) and equal padded loads `Φ_j`: the
out-units of layer `j` and the in-units of layer `j+1` (mod `k`) are equally many. -/
def JslcPairsBalanceStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (S : HccpData V), S.PreValid G →
    (∀ j j', S.Phi j = S.Phi j') →
    ∀ j, ∑ u ∈ S.layP j, S.demMinus u = ∑ v ∈ S.layP (S.succ j), S.demPlus v

/-- [s6:lemJSLC:proof-claim-a] (a proof-internal fact of [s6:lemJSLC], not the lemma: proof,
joint-routing claim (a), **distinct pair ends**) "Every pair consists of two distinct vertices …
The two vertices of a pair are distinct: for `k ≥ 2`, the layers `j` and `j+1` consist of
different, pairwise vertex-disjoint clusters (for `k = 2`, layer `j+1` is layer `j−1 ≠ j`); for
`k = 1`, `X^out ∩ X^in = ∅`."

For a system `S` with the HCC-P hypotheses other than (JC-P): every out-unit `u ∈ LayP_j`
(`dem⁻(u) > 0`) differs from every in-unit `v ∈ LayP_{j+1}` (`dem⁺(v) > 0`). -/
def JslcPairsDistinctStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (S : HccpData V), S.PreValid G →
    ∀ j, ∀ u ∈ S.layP j, ∀ v ∈ S.layP (S.succ j), 0 < S.demMinus u → 0 < S.demPlus v → u ≠ v

open Classical in
/-- [s6:lemJSLC:proof-claim-c] (a proof-internal fact of [s6:lemJSLC], not the lemma: proof,
joint-routing claim (c), **joint multiplicity**, aggregated over all systems of `(Y,l)`) "(c)
Every vertex lies in at most `max(2M_l − 2, (M_l − 1) + ⌈M_l/2⌉) = 2M_l − 2 ≤ t` pairs of
`𝔓_j(Y,l)`. … So at a fixed junction a port occurs in at most `max(dem⁻, dem⁺)` pairs of each
system containing it. Centres occur in no pair. By Steps 4 and 5 and part (b), a port occurs in
at most `(M_l − 1) + ⌈M_l/2⌉` pairs (if it belongs to `𝒮_0`) or at most `2(M_l − 1)` pairs (if it
belongs to cherry systems). For `M_l ≥ 2`, `⌈M_l/2⌉ ≤ M_l − 1`, so both are at most
`2M_l − 2 < t = 2M_l + 2`." With (b): "Every port of `R_Y` is a port of `𝒮_0(Y,l)` or of cherry
systems, never of both. A port … lies in at most `M_l − 1` cherry systems", Step 4: "`|exc(u)| ≤
M_l − 1`", "`pad(u) ≤ ⌈(M_l − 1)/2⌉ ≤ ⌈M_l/2⌉`", Step 5: "`pad ≤ 1`" (and `exc = ±1` at the ends of a
cherry).

The systems of `(Y,l)` are `Sys s`, `s < q`; `cherry s` says whether `Sys s` is a cherry class
(otherwise it is `𝒮_0`, at most one). Conclusion for every junction `j` and vertex `v`:
`Σ_s junctionOcc (Sys s) j v ≤ 2M − 2`, and `2M − 2 < 2M + 2`. -/
def JslcJointMultStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (M : ℕ), 2 ≤ M →
    ∀ (q : ℕ) (Sys : Fin q → HccpData V) (cherry : Fin q → Bool),
      (∀ s, (Sys s).PreValid G) →
      (∀ s s', cherry s = false → cherry s' = false → s = s') →
      (∀ s, cherry s = false → ∀ u, (Sys s).IsPort u →
        ((Sys s).pexc u).natAbs ≤ M - 1 ∧ (Sys s).pad u ≤ ⌈(M : ℝ) / 2⌉₊) →
      (∀ s, cherry s = true → ∀ u, (Sys s).IsPort u →
        ((Sys s).pexc u).natAbs ≤ 1 ∧ (Sys s).pad u ≤ 1) →
      (∀ u s s', cherry s = false → cherry s' = true → (Sys s).IsPort u → ¬ (Sys s').IsPort u) →
      (∀ u, (Finset.univ.filter (fun s => cherry s = true ∧ (Sys s).IsPort u)).card ≤ M - 1) →
      ∀ (j : ℕ) (v : V),
        ∑ s, (Sys s).junctionOcc j v ≤ 2 * M - 2 ∧ 2 * M - 2 < 2 * M + 2

/-- [s6:lemJSLC:proof-claim-d] (a proof-internal fact of [s6:lemJSLC], not the lemma: proof,
joint-routing claim (d)) "There are pairwise edge-disjoint paths in `LJS_{Y,l,j}`, one for each
pair of `𝔓_j(Y,l)` and joining its two vertices. Each has length at most `2^{12}L_Y^4` and all its
interior vertices in `T_j(Y,l)`. … `Y` is lend-good. By Definition s6:defLending and Lemma
s3:lemCOL(b), `LJS_{Y,l,j}` is `(2^{12}L_Y^4, t)`-path connected through `T_j(Y,l)`, as a graph on
`V(Y)`. By Cited result s1:citDef7 (see Remark s3:remMultiset) this is a statement about every
multiset of pairs of distinct vertices of `V(Y)` in which every vertex lies in at most `t` pairs,
with endpoints unrestricted. By Lemma s3:lemMonotone(iii), the property depends only on
`(LJS_{Y,l,j}, T_j(Y,l))`, so the multiset may be chosen after the stage-1 outcome and after
Steps 1–5. By the hypothesis of the lemma, no edge of `LJS_{Y,l,j}` has been used, so the whole
class is available. Apply this to `𝔓_j(Y,l)`, which is admissible by (a) and (c)."

For coherent stage data, a lend-good ancestor `Y` of a round `≤ l − 2`, `l ≤ R`, `j < K^JS_l`,
and any finite family `P` of pairs of distinct vertices of `V(Y)` in which every vertex lies in at
most `t^JS_l` pairs: pairwise edge-disjoint paths `Q i` in `LJS_{Y,l,j}` from `(P i).1` to
`(P i).2`, through `T_j(Y,l)`, of length at most `2^{12} L_Y^4`. -/
def JslcRoutingStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (run : Run V) (S : StageData V) (l : ℕ)
    (Y : PartId) (j : ℕ),
    S.Coherent run G → Y ∈ lendGoodAnc run G S l → l ≤ run.R → j < Stage1.KJS G run l →
    ∀ (ι : Type) [Fintype ι] (P : ι → V × V),
      (∀ i, (P i).1 ∈ run.ancVerts G Y ∧ (P i).2 ∈ run.ancVerts G Y ∧ (P i).1 ≠ (P i).2) →
      (∀ v : V, ((Finset.univ.filter (fun i => (P i).1 = v ∨ (P i).2 = v)).card : ℝ) ≤
        (Stage1.tJS G run l : ℝ)) →
      ∃ Q : ι → List V,
        (∀ i, IsPathBetween (S.ljs Y l j) (P i).1 (P i).2 (Q i) ∧
          IsThrough (Tj run G S Y l j) (Q i) ∧ (pathLength (Q i) : ℝ) ≤ 2 ^ 12 * run.LY G Y ^ 4) ∧
        ∀ i i', i ≠ i' → (walkEdges (Q i)).Disjoint (walkEdges (Q i'))

end EG.Spec
