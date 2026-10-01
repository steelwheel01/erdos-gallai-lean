module

public import EG.Defs.Chain.HCCP
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# The engine's multiplicity bounds feeding JS-LC (probe P-2 refutation target)

Statement file of probe unit P2E (probe P-2, part 1; design note `formal/work/p2b/P2E.md`).
These are not separate manuscript lemmas: they are the engine-level multiplicity facts that the
proof of Lemma JS-LC [s6:lemJSLC] draws from Lemmas MED and HCC-P when it checks the path
multiplicity against `t = t^JS_l = 2M_l + 2` (TRIAGE §4, probe P-2: "joint multiplicity
`≤ 2M_l − 2 ≤ t^JS`"). Stating them separately makes the probe hit this refutation target.

Manuscript v6.1, proof of [s6:lemJSLC], Step 4 (last paragraph):
"A port `u` of layer `j` has demand `dem⁻(u)` at junction `j` and `dem⁺(u)` at junction `j−1`.
Both are at most `|exc(u)| + pad(u) ≤ (M_l − 1) + ⌈M_l/2⌉`."
Joint-routing claim, part (c), and its proof:
"(c) Every vertex lies in at most `max(2M_l − 2, (M_l − 1) + ⌈M_l/2⌉) = 2M_l − 2 ≤ t` pairs of
`𝔓_j(Y,l)`. ... In a system of depth `k ≥ 2`, a port of layer `j_u` occurs in junction-`j_u`
pairs (`dem⁻` times) and in junction-`(j_u − 1)` pairs (`dem⁺` times), and `j_u ≠ j_u − 1` modulo
`k`. In a system of depth `1` it occurs only as a member of `X^out` or of `X^in`. So at a fixed
junction a port occurs in at most `max(dem⁻, dem⁺)` pairs of each system containing it. Centres
occur in no pair. By Steps 4 and 5 and part (b), a port occurs in at most
`(M_l − 1) + ⌈M_l/2⌉` pairs (if it belongs to `𝒮_0`) or at most `2(M_l − 1)` pairs (if it
belongs to cherry systems). For `M_l ≥ 2`, `⌈M_l/2⌉ ≤ M_l − 1`, so both are at most
`2M_l − 2 < t = 2M_l + 2`."
Step 4: "`|exc(u)| ≤ M_l − 1`" comes from Lemma MED(b), `|exc(u)| ≤ deg_{B_𝒦}(u)`, and
"`pad(u) ≤ ⌈(M_l − 1)/2⌉ ≤ ⌈M_l/2⌉`".

* `HccpEndMultStatement` (engine part, one system, one junction): in a valid HCC-P system, every
  vertex `u` is an end (first or last vertex) of at most `max(dem⁻(u), dem⁺(u))` paths of `𝒫_j`;
  this maximum is `|exc(u)| + pad(u)`; and `|exc(u)| ≤ deg_{B_𝒦}(u)` for a port `u` of `𝒦`. In the
  HCC-P encoding the pairs of junction `j` of a system are the (first, last) vertices of the
  paths of `𝒫_j`; a vertex that is no port of the system (a centre, a junction vertex) has
  `exc = 0` and occurs as an end of no path, so its bound is `pad(u)`, and `pad` is read only
  at ports (a path end is always a port, `Valid.path_ends`).
* `JsMultNumStatement` (numeric part): for every integer `M ≥ 2`,
  `⌈(M−1)/2⌉ ≤ ⌈M/2⌉ ≤ M − 1`, `2(M − 1) = 2M − 2`,
  `max(2M − 2, (M − 1) + ⌈M/2⌉) = 2M − 2` and `2M − 2 < 2M + 2` (`t^JS_l = 2M_l + 2` is
  `EG.Stage1.tJS`; `M_l ≥ 2^40` by (R2), so `M_l ≥ 2` holds at every use). All in `ℕ`, with
  `⌈x⌉₊` for the ceiling of the real `x`.

Label tag: both statements carry the tag `[s6:lemJSLC:proof-claim-c]`, not `[s6:lemJSLC]`: they
are facts used inside the proof of JS-LC (Step 4 and claim (c)), not Lemma JS-LC itself, whose
Spec belongs to probe P-2 part 2.

Scope (review round 1, R2): these two statements hit the refutation target per system and per
junction only. The aggregated claim (c), "every vertex lies in at most `2M_l − 2 ≤ t` pairs of
`𝔓_j(Y,l)`", sums over all systems of `(Y,l)`. It also needs the `𝒮_0`/cherry exclusivity, at
most `M_l − 1` cherry systems per port each with demand `≤ 2`, and Step 4's pad bound
`pad ≤ ⌈(M_l − 1)/2⌉`. These are JS-LC-level data (part 2). Part 2 must state the aggregated
bound as its own Spec and prove it from `HccpEndMultStatement`, `JsMultNumStatement` and
`EG.jsMult_lt_tJS` (open hand-off, re-confirmed by review round 2).
The second conjunct of `HccpEndMultStatement`, `max(dem⁻, dem⁺) = |exc| + pad`, is an identity
of the definitions (one of `exc⁻`, `exc⁺` is zero). It is kept because it links the demand
bound to the TeX's "`|exc(u)| + pad(u)`". The bridge `t^JS_l = 2M_l + 2` to
`EG.Stage1.tJS` is `EG.tJS_eq_two_mul_add_two` (`EG.Proof.Chain.EngineMultTJS`).
-/

@[expose] public section

namespace EG.Spec

open EG.Chain

universe u

/-- [s6:lemJSLC:proof-claim-c] (a proof-internal fact of [s6:lemJSLC], not the lemma: proof,
Step 4 last paragraph and joint-routing claim (c), engine part; uses
[s6:lemMED](b) and [s6:lemHCCP]) "A port `u` of layer `j` has demand `dem⁻(u)` at junction `j`
and `dem⁺(u)` at junction `j−1`. Both are at most `|exc(u)| + pad(u)` ... So at a fixed junction
a port occurs in at most `max(dem⁻, dem⁺)` pairs of each system containing it. Centres occur in
no pair." and (Step 4, from Lemma MED(b)) "`|exc(u)| ≤ deg_{B_𝒦}(u)`".

For a valid HCC-P system `S`, a junction `j` and any vertex `u`: the number of paths of `𝒫_j`
with first or last vertex `u` is at most `max(dem⁻(u), dem⁺(u))`, which equals
`|exc(u)| + pad(u)`; and if `u` is a port of the cluster `𝒦_i`, then `|exc(u)| ≤ deg_{B_{𝒦_i}}(u)`. -/
def HccpEndMultStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (S : HccpData V), S.Valid G →
    ∀ (j : Fin S.k) (u : V),
      (S.P j).countP (fun p => p.head? = some u ∨ p.getLast? = some u) ≤
          max (S.demMinus u) (S.demPlus u) ∧
      max (S.demMinus u) (S.demPlus u) = (S.pexc u).natAbs + S.pad u ∧
      ∀ i, u ∈ (S.K i).ports → (S.pexc u).natAbs ≤ degE (S.K i).beads u

/-- [s6:lemJSLC:proof-claim-c] (a proof-internal fact of [s6:lemJSLC], not the lemma: proof,
joint-routing claim (c), numeric part) "Every vertex lies in at most
`max(2M_l − 2, (M_l − 1) + ⌈M_l/2⌉) = 2M_l − 2 ≤ t` pairs ... a port occurs in at most
`(M_l − 1) + ⌈M_l/2⌉` pairs (if it belongs to `𝒮_0`) or at most `2(M_l − 1)` pairs (if it belongs
to cherry systems). For `M_l ≥ 2`, `⌈M_l/2⌉ ≤ M_l − 1`, so both are at most
`2M_l − 2 < t = 2M_l + 2`", with Step 4's "`pad(u) ≤ ⌈(M_l − 1)/2⌉ ≤ ⌈M_l/2⌉`". -/
def JsMultNumStatement : Prop :=
  ∀ M : ℕ, 2 ≤ M →
    ⌈((M : ℝ) - 1) / 2⌉₊ ≤ ⌈(M : ℝ) / 2⌉₊ ∧
    ⌈(M : ℝ) / 2⌉₊ ≤ M - 1 ∧
    2 * (M - 1) = 2 * M - 2 ∧
    max (2 * M - 2) ((M - 1) + ⌈(M : ℝ) / 2⌉₊) = 2 * M - 2 ∧
    2 * M - 2 < 2 * M + 2

end EG.Spec
