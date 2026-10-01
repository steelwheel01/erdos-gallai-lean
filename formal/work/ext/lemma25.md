# Design note: proof of B–M Lemma 25, explicit form (s1:citLem25), task [lemma25]

Target: `EG.bmLemma25 : EG.Spec.BMLemma25Statement` (Spec LOCKED, not changed).
Notation: `n = |G|`, `L = log₂ n > 0` (`n ≥ 2`), `β = ε / L²`, `a = ε² n / (18 L⁴) = β² n / 18`.

## Files
* `EG/Lib/Ext/DFS.lean` — the DFS as an invariant relation and the "moment |U| = |R|".
* `EG/Lib/Ext/DFSCycle.lean` — cycles from vertex lists; the X/Y/Z argument on a path.
* `EG/Proof/Ext/BMLemma25.lean` — numerics and assembly.

## 1. DFS as an invariant relation (`EG/Lib/Ext/DFS.lean`)
State `(U, R, P)`: `U R : Finset V` (unexplored, processed), `P : List V` the DFS stack path,
stored with the active end `t(P)` at the HEAD (so a DFS step is `cons` / `tail`).
`DFSInv G U R P`:
1. `U ⊆ V(G)`, `R ⊆ V(G)`, `∀ v ∈ P, v ∈ V(G)`;
2. `U`, `R`, `P` pairwise disjoint, `P.Nodup`;
3. `|U| + |R| + |P| = |G|` (with 1–2 this makes them a partition of `V(G)`);
4. `P.IsChain G.Adj` (consecutive vertices adjacent: a path of `G`);
5. no edge between `U` and `R`.
Steps (each keeps `DFSInv` and lowers `|U| - |R|` by exactly one):
* `P = []`, `u ∈ U`: `(U.erase u, R, [u])` (restart; B–M instead use connectivity, which we avoid:
  with restarts the DFS needs no connectivity, and the rest of the argument never uses it);
* `P = t :: P'`, `v ∈ U` with `t ~ v`: `(U.erase v, R, v :: P)`;
* `P = t :: P'`, no neighbour of `t` in `U`: `(U, insert t R, P')` (5 is kept since `t` has no
  neighbour in `U`).
Discrete intermediate value: by induction on `d = |U| - |R|` (ℕ, with `|R| ≤ |U|`): if `d > 0`
then `U ≠ ∅`, a step applies, and `d` drops by one. Start `(V(G), ∅, [])`.
Result `exists_dfs_balanced`: ∃ U R P, `DFSInv G U R P ∧ |U| = |R|`.
Consequence `nbrSet_subset_path`: `Nbr_G(U) ⊆ set(P)` (a neighbour of `U` is not in `U`, not in `R`).

## 2. The cycle (`EG/Lib/Ext/DFSCycle.lean`)
`cycle_of_chain`: `c.Nodup`, `3 ≤ |c|`, `c.IsChain G.Adj`, `G.Adj (last c) (head c)` ⇒
`(Obj.cycle c).WF ∧ ∀ e ∈ cycleEdges c, e ∈ E(G)` (via `mem_cycleEdges`: edge `i` is
`s(c[i], c[(i+1) % |c|])`).

`long_cycle_of_path` (the X/Y/Z step, purely combinatorial):
`P` a path of `G` (nodup, chain, in `V(G)`), `x k : ℕ`, `1 ≤ k`, `2x + k ≤ |P|`, and
(expansion) `∀ S ⊆ V(G), x ≤ |S| → 2|S| ≤ |G| → k < |Nbr_G(S)|`. Then ∃ cycle `c` of `G` with
`k + 2 ≤ |c|`.
Proof: `X = P.take x`, `Y = (P.drop x).take k`, `Z = P.drop (x+k)` (as finsets; `|Z| ≥ x`).
`W = V(G) \ set(P)`. `HW` = the `SimpleGraph` with the edges of `G` inside `W`.
`X* = X ∪ {w ∈ W : ∃ x₀ ∈ X, ∃ w₀ ∈ W, x₀ ~ w₀, HW.Reachable w₀ w}` (replaces B–M's shortest
X–Z path: X* is the part of `G - Y` reachable from `X` through `W`).
* Case A: some `v ∈ X*`, `z ∈ Z`, `v ~ z`. With `x₀ = P[i]` (`i < x`), `z = P[j]` (`j ≥ x+k`),
  `S = P[i..j]` (`|S| ≥ k + 2`). If `v ∈ X` (`v = x₀`): `c = S`. Otherwise take a Mathlib path
  `Q : HW.Walk w₀ v` (`toPath`) and `c = S ++ reverse (support Q)`; `support Q ⊆ W` is disjoint
  from `P`; closing edge `w₀ x₀`.
* Case B: no such edge. Then `Nbr(X*) ⊆ Y` (a neighbour in `W` would be in `X*`, one in `X` is
  in `X*`, one in `Z` is excluded). Put `T = V(G) \ (X* ∪ Y) ⊇ Z`; then `Nbr(T) ⊆ Y` too.
  `X* ∩ T = ∅`, so one of them, `S`, has `2|S| ≤ |G|`, and `|S| ≥ min(|X|,|Z|) = x`; expansion
  gives `k < |Nbr(S)| ≤ |Y| = k`, contradiction.
  (No connectivity of `G` and no shortest path needed; `2|S| ≤ n` gives `|S| ≤ 2n/3`.)

## 3. Numerics and assembly (`EG/Proof/Ext/BMLemma25.lean`)
* `β ≤ 1`: apply expansion to any `U` with `|U| = ⌈n/2⌉` (`≤ 2n/3` for `n ≥ 2`):
  `β|U| ≤ |Nbr(U)| ≤ n - |U| ≤ |U|`.
* `a ≥ 4/3`, i.e. `24 L⁴ ≤ ε² n`: from `ε² n ≥ 2^30` and `ε² n ≥ n / 2^10` (`ε ≥ 2^-5`).
  If `n < 2^40`: `L < 40`, `24 · 40⁴ < 2^30`. If `n ≥ 2^40`: `y ↦ y / log⁴ y` is non-decreasing
  (`EG.div_logb_pow_le_div_logb_pow`), so `n / L⁴ ≥ 2^40 / 40^4 ≥ 24 · 2^10`.
* DFS moment: `u = |U| = |R|`, `p = |P| = n - 2u`, `βu ≤ |Nbr(U)| ≤ p` if `u ≥ 1`
  (`u ≤ n/2 ≤ 2n/3`). Hence `p ≥ βn/3` (if `3u ≥ n`: `p ≥ βu`; else `p > n/3 ≥ βn/3`, `β ≤ 1`).
* `k = ⌈a⌉₊` (`a ≤ k < a + 1`, `k ≥ 2`), `x = (p - k) / 2`. Need `βx > k`:
  `2βx ≥ β(p - k - 1) ≥ βp - (k + 1) ≥ 6a - (k+1) > 2k` iff `6a > 3k + 1`, true as
  `3k + 1 < 3a + 4 ≤ 6a` (`a ≥ 4/3`). Also `k ≤ p` (`p ≥ βn/3 ≥ β²n/3 = 6a`).
* Expansion hypothesis of `long_cycle_of_path`: `S ⊆ V(G)`, `|S| ≥ x`, `2|S| ≤ n` ⇒
  `k < βx ≤ β|S| ≤ |Nbr(S)|` (`|S| ≥ x ≥ 1`, `|S| ≤ n/2 ≤ 2n/3`).
* Cycle length `≥ k + 2 > a = ε²n/(18L⁴)`.  **The constant 18 is achieved exactly** (with slack:
  the proof gives length `≥ ⌈a⌉ + 2`).

## Status (task [lemma25])
Done, no `sorry`: `EG.bmLemma25 : EG.Spec.BMLemma25Statement` (axioms: propext,
Classical.choice, Quot.sound). Files: `EG/Lib/Ext/DFS.lean` (215 lines),
`EG/Lib/Ext/DFSCycle.lean` (~295), `EG/Proof/Ext/BMLemma25.lean` (~240).
Constant: 18 exactly as stated (the proof yields length `≥ ⌈ε²m/(18 log⁴m)⌉ + 2`).
Deviations from [BM]'s text (none affect the statement): DFS restarts instead of connectivity;
the reachable set `X*` instead of a shortest `X–Z` path; `|X| = ⌊(|P|-|Y|)/2⌋ ≤ |Z|` instead of
`|X|,|Z| ≥ |P|/3`; the side of size `≤ m/2` is `X*` or `V \ (X* ∪ Y)`.
Note for the integrator: the module docstring of the locked `EG/Spec/Ext/BMLemma25.lean` still
says the proof is `sorry`; it is now proved.
