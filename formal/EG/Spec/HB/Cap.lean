module

public import EG.Defs.Expander
public import EG.Defs.Objects

/-!
# Statement of the Lemma-25 size cap (manuscript s2:lemCap, part (i), remark, core of (ii))

PROTECTED FILE (`EG/Spec/**`): statement file. `EG/Proof/HB/Cap.lean` proves it.

Manuscript, Lemma [s2:lemCap] ("Lemma-25 size cap"), s2.tex:
"(i) If `m ≥ 2^{40}`, `T ≥ 2^{117}` and `m < 18432 T log⁴ m`, then `m ≤ 2^{16} T log⁴ T`.
(ii) In every round `l ≤ R` of a valid `HB^tp` run, every `s = 0` piece `𝒫` satisfies
`|𝒫| ≤ M_l`. …
*Remark (not used).* Part (i) is false for small `T`: for `T = 2^{20}` and `m = 2^{55}` we have
`m ≥ 2^{40}` and `18432 T log⁴ m = 2^{57.29…} > m`, but `2^{16} T log⁴ T = 2^{53.28…} < m`. The
uniform form `m ≤ max(2^{40}, 2^{16} T (log T + 40)^4)` holds for all `T ≥ 1`."

Formal reading.
* `CapStatement` is part (i) verbatim: `m T : ℝ` are real numbers and `log = Real.logb 2`
  ([s1:convGraphs] (b)); `log⁴ m = (Real.logb 2 m)^4`.
* `CapUniformStatement` is the remark's uniform form: for every real `T ≥ 1`, `m < 18432 T log⁴ m`
  implies `m ≤ max(2^{40}, 2^{16} T (log T + 40)^4)`. The hypothesis `m ≥ 2^{40}` of (i) is not
  assumed (it is not used in the manuscript's argument). The two readings are logically
  equivalent: for `m < 2^{40}` the conclusion `m ≤ max(2^{40}, …)` holds trivially.
* `CapGraphStatement` is the graph-level step of the proof of (ii): "the graph of `𝒫` is an
  `(ε,0)`-expander … with `ε = 2^{-5}` on `m ≥ 2^{40} = 2^{30}/ε²` vertices, so by Cited result
  [s1:citLem25] it contains a cycle of length at least `ε² m/(18 log⁴ m) = m/(18432 log⁴ m)`. This
  cycle lies in `G'_l`, which has no cycle of length at least `T` by (R1). Hence
  `m < 18432 T log⁴ m`, and (i) gives `m ≤ 2^{16} T log⁴ T`." Here "no cycle of length at least
  `T`" is said of the expander `G` itself (a cycle of the graph of `𝒫` is a cycle of `G'_l`): every
  vertex list `c` that is a well-formed cycle object with all edges in `E(G)` has
  `c.length < T`. Part (ii) itself needs the hierarchy (`HB^tp` runs, pieces, `M_l`, (R1)–(R5)),
  which is not defined yet; it is not formalized here.
-/

@[expose] public section


namespace EG.Spec

universe u

/-- [s2:lemCap] (i) "If `m ≥ 2^{40}`, `T ≥ 2^{117}` and `m < 18432 T log⁴ m`, then
`m ≤ 2^{16} T log⁴ T`." (`m T : ℝ`, `log = log₂`.) -/
def CapStatement : Prop :=
  ∀ m T : ℝ, 2 ^ 40 ≤ m → 2 ^ 117 ≤ T → m < 18432 * T * Real.logb 2 m ^ 4 →
    m ≤ 2 ^ 16 * T * Real.logb 2 T ^ 4

/-- [s2:lemCap] (Remark, not used) "The uniform form `m ≤ max(2^{40}, 2^{16} T (log T + 40)^4)`
holds for all `T ≥ 1`": for real `T ≥ 1`, `m < 18432 T log⁴ m` implies
`m ≤ max(2^{40}, 2^{16} T (log T + 40)^4)` (without the hypothesis `m ≥ 2^{40}`; see the module
docstring). -/
def CapUniformStatement : Prop :=
  ∀ m T : ℝ, 1 ≤ T → m < 18432 * T * Real.logb 2 m ^ 4 →
    m ≤ max (2 ^ 40) (2 ^ 16 * T * (Real.logb 2 T + 40) ^ 4)

/-- [s2:lemCap] (ii), graph-level step of the proof: an `m`-vertex `(2^{-5},0)`-expander `G` with
`m ≥ 2^{40}` that contains no cycle of length at least `T`, where `T ≥ 2^{117}`, has
`m ≤ 2^{16} T log⁴ T`. ("the graph of `𝒫` is an `(ε,0)`-expander … with `ε = 2^{-5}` on
`m ≥ 2^{40} = 2^{30}/ε²` vertices, so by Cited result [s1:citLem25] it contains a cycle of length at
least `ε² m/(18 log⁴ m) = m/(18432 log⁴ m)`. This cycle lies in `G'_l`, which has no cycle of
length at least `T` by (R1). Hence `m < 18432 T log⁴ m`, and (i) gives `m ≤ 2^{16} T log⁴ T`.")
A cycle is a well-formed cycle object (`EG.Obj.WF`) with all edges in `E(G)`; its length is
`c.length`. -/
def CapGraphStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : EG.FGraph V) (T : ℝ),
    2 ^ 117 ≤ T → 2 ^ 40 ≤ (G.card : ℝ) → G.IsExpander ((2 : ℝ) ^ (-5 : ℤ)) 0 →
    (∀ c : List V, (EG.Obj.cycle c).WF → (∀ e ∈ EG.cycleEdges c, e ∈ G.edges) →
      (c.length : ℝ) < T) →
    (G.card : ℝ) ≤ 2 ^ 16 * T * Real.logb 2 T ^ 4

end EG.Spec
