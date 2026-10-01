# Clean-room review: group `findist`, reviewer `opus`

Date: 2026-09-26. Reviewer: Claude Opus 5.5, an independent clean-room agent. I reviewed from
scratch. I did not read or rely on the earlier reviews (`work/p1b/findist.review1.md`,
`findist.review2.md`) or on earlier approvals. I read the design note `work/p1b/findist.md` only
to learn the intended idioms. I only read repository files; this review is the one file I wrote.

Reviewed file: `EG/Defs/Prob/FinDist.lean` (sha256
`376a05b396cf30486015ba759cecad0574519e3a5836e6447513fb698490e161`, unchanged since commit
`f18e1c2`; working tree clean for this file).

Scratch file: `/tmp/claude-0/-home-user-Erdos-Proof/ab92a43f-e615-5aab-870d-cceae4796e61/scratchpad/FinDistReviewOpus.lean`.
It was compiled with `lake env lean` from `formal/` and gives rc = 0, 0 errors and 0 warnings. It
`#print`s every definition to confirm how it elaborates, and it holds the independent tests quoted
below. `#print axioms` on the Lib faithfulness theorems this review relies on gives only
`propext`, `Classical.choice` and `Quot.sound`. Those theorems are `isRSubset_iff`,
`indepFun_iff_map_eq_prod`, `iIndepFun_iff_map_eq_pi`, `randColouring_eq_uniform`,
`indepSubset_w`, `rsubset_w`, `map_selectSet_randColouring`, `IsRSubset.cond_of_indepFun` and
`IndepFun.map_cond`.

**Overall verdict: APPROVE, with notes.** Every definition is the textbook object it claims to
be. In every case the manuscript uses, the probabilities built from them are the exact
probabilities the manuscript means. I found no mismatch. The notes N1–N8 at the end are
limits and conventions that `Spec` authors and reviewers must respect. The most important is
N1: the finite-support design cannot express the geometric level law of s4 literally, so those
Specs must truncate. None of the notes is a defect of the definitions.

---

## Manuscript text used

* `s1:citChernoff` (s1 l. 419–429): "Let n be an integer, 0≤δ,p≤1, X∼Bin(n,p) and μ:=E X=np.
  Then P(X>(1+δ)μ)≤e^{−δ²μ/3} and P(X<(1−δ)μ)≤e^{−δ²μ/2}."
* `s1:citChernoffGen` (l. 784–797): "Let X=∑_{i=1}^m I_i be a sum of independent indicator
  variables with P(I_i=1)=p_i …"
* `s1:citMarkov` (l. 819–834): "If X≥0 and a>0 then P(X≥a)≤E X/a. Consequently: (a) for X≥0,
  P(X≤3E X)≥2/3; (b) … P(X₁≤4E X₁ and X₂≤4E X₂)≥1/2; (c) (a) and (b) hold with P and E replaced
  by the conditional probability and expectation given any event of positive probability, or
  given any fixed outcome of variables that are independent of the variables being drawn." The
  derivation of (c) says: "the conditional law of the latter is their unconditional law."
* `s1:citThm16` (l. 614–618): "let V⊆V(G) contain each vertex independently with probability
  1/3".
* s3 conventions (s3 l. 29–31): "For ρ∈[0,1], a ρ-random subset of a finite set S is a random
  subset of S that contains each element of S independently with probability ρ."
* `s3:lemL15p` (l. 100–108): "let k≥1 be an integer … Give every edge of X a colour from [k],
  independently and uniformly at random, and for i∈[k] let X_i be the graph with vertex set V(X)
  whose edges are the edges of colour i. Then for each i∈[k], X_i is an (ε′,s/(2k))-expander with
  probability at least 1−2N^{−5}."
* `s3:thmT16s` (l. 773–790): "Let ρ∈(0,1] and t≥1, and let V be a ρ-random subset of V(X). Here
  X is fixed; if X was itself produced at random, V is independent of that randomness. … Then,
  with probability at least 1−2^{86} t L^{19} ρ^{−3} N^{−3}, the graph X is
  (2^{12}L^4,t)-path connected through V."
* `s3:defCOL` (l. 966–1025): per-edge "fair bit, a lent index and an own label" (uniform), JS
  labels with "P(lab_{Y,l}(y)=j)=ρ_l … P(lab=∗)=1−M_l^{−2}". "Consequently: colours of distinct
  edges are independent; … the labels are independent of the colours; … for fixed (l,j), the set
  T_j(Y,l) is a ρ_l-random subset of V(Y), independent of the colouring."
* `s4:lemTPV` (s4 l. 99–131): "The labels of the run are the following independent random
  variables: (a) a uniform colouring of E(O) with the k colours R_{j,c} (0≤j<J, c∈[3]) and M;
  (b) for every v∈P a level lev(v)∈{0,1,2,…} with P(lev(v)≥j)=2^{−j} for all j≥0; (c) for every
  v∈Z a label κ(v)∈{0,1,2,3} with P(κ(v)=0)=1/2 and P(κ(v)=c)=1/6 for c∈[3]." It continues:
  "There is an event G_TPV … with P(G_TPV) ≥ 1/2 − η_TPV(N)". Proof (G2) (l. 176–178): "Using
  auxiliary independent coins, keep each v∈V_{j,c} independently with probability
  (1/L)/P(v∈V_{j,c}); the kept set V′ is a (1/L)-random subset of Z …, independent of the
  colouring". The same level law appears in `s4:lemPV` (l. 347–352) and `s4:thmVXp`
  (l. 572–575).
* `s7:defSchedule` (s7 l. 158–200), checked for completeness of the layer. It lists "a uniformly
  random bijection η_h:[4M_l]→[4M_l] …; a uniformly random 3-subset ζ_{h,u}⊆[4M_l] …; a
  uniformly random linear order ≺_u of V(G)", plus "fix a stage-1 outcome in the event
  {X′≤3E X′}".

---

## Definitions

### `FinDist Ω` (structure, `@[ext]`)
Back-translation: a function w : Ω → ℝ with w ≥ 0 such that for some finite s ⊆ Ω, w = 0
outside s and ∑_{ω∈s} w(ω) = 1. So it is exactly a finitely supported probability mass function
on Ω, and the total mass is exactly 1, not a sub-probability. The `@[ext]` lemma compares only
`w`, since the other fields are propositions, so two distributions are equal iff they have the
same weights. The type carries no `Fintype`/`DecidableEq` instance, so no instance diamond can
split `FinDist Ω` into several types. There are no universe constraints (`Ω : Type u`). No
`FinDist ∅` exists, which is correct because there is no probability measure on ∅.
Expressiveness: every distribution the manuscript uses is on a finite set, except the level of
s4 (see N1). **approve**

### `finite_support`, `supp`, `mem_supp`, `supp_subset`, `sum_supp_eq_of_subset`, `sum_w_supp`
`supp μ` = {ω : w ω ≠ 0} as a Finset, which is the canonical support. The lemmas are proved and
are correct statements (the weights sum to 1 over the support). **approve**

### `prob μ A`
Back-translation: P(A) = ∑_{ω∈supp, ω∈A} w(ω), for every `A : Set Ω`. In a discrete space every
set is an event, so there are no measurability conditions to lose. `Set.indicator` needs no
decidability. Tests: on `Ω = ℕ`, which is infinite, `(dirac 5).prob {n | 3 ≤ n} = 1` and
`… {n | n ≤ 3} = 0`. For a fair coin, `P(univ) = 1`. **approve**

### `expect μ X`
Back-translation: E X = ∑_{ω∈supp} w(ω) X(ω). This is finite for every `X : Ω → ℝ`, with no
integrability side conditions, because the support is finite. Test: E[3·1_true + 1·1_false] = 2
for a fair coin. **approve**

### `ofFinset`, `ofFintype`
They build a distribution from explicit nonnegative weights that sum to 1 over a finite set, or
over `univ` for `ofFintype`. They store no instance. **approve** (see N4: this is how Specs
build non-uniform label laws.)

### `dirac a`
w = 1_{a}. This is the point mass. **approve**

### `compProd μ K`
w(a,b) = w_μ(a)·w_{K a}(b). This is the two-stage experiment "draw a ∼ μ, then b ∼ K a", the
manuscript's "fix a prefix / given a fixed outcome". Test: with a kernel that is `dirac true`
after `true`, the outcome (true,false) has weight 0. **approve**

### `prod μ ν`
`compProd μ (fun _ => ν)`, so w(a,b) = w_μ(a) w_ν(b). This is the independent product.
Independence of the coordinates is `indepFun_fst_snd` (proved; I used it in the tests).
**approve**

### `pi μ` (`[Fintype ι]`, dependent `κ`)
w(f) = ∏_{i} w_{μ i}(f i). This is the independent product of a finite family. Edge case ι = ∅:
the unique function gets weight 1 (empty product), which is correct; tested with `Fin 0`. The
`Fintype ι` instance is data, but `Finset.univ` is instance-independent up to propositional
equality, so the value is well defined. The coordinates are mutually independent
(`iIndepFun_eval_pi`, proved; tested on `randColouring (Fin 5) 3`). **approve**

### `map f μ`
w'(b) = P_μ(f⁻¹{b}). This is the pushforward (the law of f). It is correct for non-injective f
(test: collapsing a coin to `Unit` gives weight 1). The codomain needs no `Fintype`. **approve**

### `bind μ K`
`(compProd μ K).map Prod.snd`, so w'(b) = ∑_a w_μ(a) w_{K a}(b). This is the mixture. **approve**

### `uniform Ω` (`[Finite Ω] [Nonempty Ω]`)
w ≡ 1/|Ω| with |Ω| = `Nat.card Ω`, which is the true cardinality for a finite type. Both
instance arguments are `Prop` classes, so there are no diamonds. Test: `(uniform (Fin 3)).w x =
1/3`. The manuscript's "uniformly random bijection / 3-subset / linear order" (s7) are all
uniform laws on finite nonempty types, so they are expressible (N8 covers nonemptiness).
**approve**

### `bernoulli p h0 h1`
w(true) = p, w(false) = 1 − p, with p ∈ [0,1] required. I checked the one risk. Inside
`namespace FinDist`, `cond` could have meant `FinDist.cond`. `#print` shows `bif b then p else
1 - p` (`Bool.cond`), and `(bernoulli p _ _).w true = p` holds by `rfl`. Orientation: `true` is
"success". **approve**

### `FinDist.cond μ A hA` (protected)
w'(ω) = 1_A(ω) w(ω) / P(A), and it requires `0 < P(A)`. This is exactly "conditional probability
given an event of positive probability" (s1:citMarkov(c)). Test: conditioning a fair coin on
`{true}` gives weight 1 on `true`. `protected`, so it does not shadow `Bool.cond`. **approve**

### `selectSet S f`
{a ∈ S : f ⟨a, _⟩ = true}, as a `Finset α` via `attach`/`filter`/`map subtype`. **approve**

### `indepSubset S p h0 h1`
The law of {a ∈ S : coin_a = true}, where the coins are independent Bernoulli(p a), a ∈ S. This
is the random subset of S that contains each a independently with probability p(a). The
element-dependent p covers the thinning of s4:lemTPV (G2), "keep each v … independently with
probability (1/L)/P(v∈V_{j,c})", and the "1/3" sets of s1:citThm16. p only has to lie in [0,1]
on S, and values off S are irrelevant. Evidence:
* the proved weight formula `indepSubset_w`: P(T) = ∏_{a∈T} p(a) · ∏_{a∈S∖T}(1−p(a)) for T ⊆ S,
  and 0 otherwise;
* my test: with S = {0,1}, p(0) = 1/2 and p(1) = 1/4, P({0}) = 1/2·3/4. That confirms
  true = "included".

**approve**

### `rsubset S ρ h0 h1`
`indepSubset S (fun _ => ρ)`, with ρ ∈ [0,1] required. This is exactly the s3 convention "For
ρ∈[0,1], a ρ-random subset of a finite set S … contains each element of S independently with
probability ρ". Evidence:
* proved: `rsubset_w` (P(T) = ρ^{|T|}(1−ρ)^{|S∖T|}) and `prob_mem_rsubset` (P(a∈T) = ρ);
* my tests: the weight of {0,2} ⊆ {0,1,2} is ρ²(1−ρ), which is not the same as ρ²;
* edge cases: ρ = 1 gives weight 1 on S (using 0⁰ = 1, correct), ρ = 0 gives weight 1 on ∅,
  and S = ∅ gives weight 1 on ∅. All three are correct.

**approve**

### `randColouring ι k` (`[Fintype ι] [NeZero k]`)
`pi (fun _ : ι => uniform (Fin k))`: every element of ι independently gets a uniform colour
from {0,…,k−1}. This is s3:lemL15p's "Give every edge of X a colour from [k], independently and
uniformly at random" (with ι = ↥E(X)). `NeZero k` is the manuscript's k ≥ 1. The colours are
0-based (Fin k, not [k]); that is a relabelling, and the distribution is the same. Evidence:
* proved: `randColouring_eq_uniform` (uniform on ι → Fin k) and `map_selectSet_randColouring`
  (the colour-j class is a (1/k)-random subset of E, which is exactly Step 3 of the proof of L15⁺:
  "Each of them lies in H independently with probability 1/k");
* my test: every 3-colouring of a 2-set has weight 1/9, and the coordinates are `iIndepFun`.

**approve**

### `IndepFun μ X Y`
Back-translation: for all A ⊆ γ and B ⊆ δ, P(X∈A, Y∈B) = P(X∈A)·P(Y∈B). This is the standard
definition. In a discrete space, quantifying over all sets is the same as quantifying over
singletons (`indepFun_iff_map_eq_prod`, proved: joint law = product of marginals). This is the
meaning in s3:defCOL "the labels are independent of the colours", in s3:thmT16s "V is independent
of that randomness", and in s1:citMarkov(c). `IndepFun.map_cond` (proved) is exactly Markov (c)'s
"the conditional law of the latter is their unconditional law".

Non-vacuity: a fair coin is *not* independent of itself (test: 1/2 ≠ 1/4), while the
coordinates of `coin.prod coin` are independent. **approve**

### `iIndepFun μ X` (index type U, dependent value types β u)
Back-translation: for every finite set s of indices and all events A_u,
P(∀u∈s, X_u∈A_u) = ∏_{u∈s} P(X_u∈A_u). This is standard *mutual* independence. Infinite U is
allowed, and the condition is on finite subfamilies. For s = ∅ it says P(Ω) = 1, which is true.

My test shows it is genuinely mutual and not pairwise. Take two fair coins and their XOR: XOR is
independent of the first coin (tested with `IndepFun`), but the family (fst, snd, xor) is *not*
`iIndepFun` (P(all true) = 0 ≠ 1/8). `iIndepFun_iff_map_eq_pi` (proved) gives the law form for
finite U. This matches s1:citChernoffGen "independent indicator variables" and s3:defCOL
"colours of distinct edges are independent". **approve**

### `IsRSubset μ V S ρ`
Back-translation: ρ ∈ [0,1] and the law of the random set V is the ρ-random subset law on S.
`isRSubset_iff` (proved) gives the elementwise reading: V ⊆ S almost surely, the indicators
[a ∈ V], a ∈ S, are mutually independent, and each has probability ρ. That is word for word the
s3 convention. A downstream "with probability ≥ q" statement about an event that depends only on
V therefore has the same value for every (Ω, μ, V) with `IsRSubset`. I tested the identity
`μ.prob {ω | P (V ω)} = (rsubset S ρ _ _).prob {T | P T}`, so quantifying over all such
(Ω, μ, V) is equivalent to using the canonical `rsubset`.

Non-vacuity:
* `(dirac ∅).IsRSubset id {0} (1/2)` is false (weight 0 vs 1/2 at {0});
* ρ = 2 is rejected;
* `rsubset S (1/3)` with V = id satisfies it.

**approve**

---

## "Probability ≥ p" statements

With these definitions, "with probability at least 1 − η, 𝒫 holds" is written
`1 - η ≤ μ.prob {ω | 𝒫 ω}`. Three things make this mean what the manuscript means:
* `prob` is the exact probability of the set;
* the total mass is exactly 1, so `prob_compl` gives `P(¬𝒫) ≤ η` ⇔ `P(𝒫) ≥ 1 − η`;
* all conclusions in the manuscript are ultimately deterministic existence statements, and
  `exists_of_prob_pos` turns positive probability into an outcome of positive weight.

The manuscript's patterns are all expressible:
* "X fixed, V ρ-random": the Spec quantifies over `μ` with `μ.IsRSubset V X.verts ρ`, or uses
  `rsubset` directly (equivalent, as tested above).
* "V independent of the colouring c": `μ.IsRSubset V S ρ ∧ μ.IndepFun c V`. Conditioning on a
  fixed colouring (s3:lemCOL(b),(c), "The labels are independent of the colouring, so … T_j(Y,l)
  is still a ρ_l-random subset") is `IsRSubset.cond_of_indepFun`.
* "for each i ∈ [k], X_i is an expander with probability ≥ 1 − 2N^{−5}" (L15⁺): an event on
  `randColouring ↥E k`.

---

## Notes for Spec authors and Spec reviewers (not defects of the definitions)

**N1 (finite support vs. the geometric level; most important).** s4:lemTPV(b), s4:lemPV and
s4:thmVXp draw "a level lev(v)∈{0,1,2,…} with P(lev(v)≥j)=2^{−j} for all j≥0". That law has
infinite support. No `FinDist` has it: I proved `no_geometric : ¬ ∀ j, μ.prob {n | j ≤ n} =
(1/2)^j` for every `μ : FinDist ℕ` in the scratch file. The Specs of these three results must
therefore use the truncated level lev′ = min(lev, J), which has P(lev′=j) = 2^{−(j+1)} for j < J,
P(lev′=J) = 2^{−J}, and hence P(lev′≥j) = 2^{−j} for 0 ≤ j ≤ J.

I checked the three statements and proofs. Every object built from the level depends only on
min(lev, J):
* U_j for 0 ≤ j ≤ J, including U_J in (G5)/(G3) and the finish;
* W_j for j < J;
* Z_j and V_{j,c} for j < J (they use U_{j+1} with j+1 ≤ J).

So the truncation is lossless, and s5 l. 171 uses the levels only through G_PV. A Spec reviewer
of TPV/PV/VX⁺ must check that the truncation is written exactly this way (in particular that
P(lev′ = J) is 2^{−J} and not 2^{−(J+1)}).

**N2 (ρ > 0 and the "independent of that randomness" clause).** `IsRSubset` allows ρ = 0 (as
the s3 convention does). s3:thmT16s requires ρ ∈ (0,1], so its Spec must add `0 < ρ`.
`IsRSubset` fixes only the *law* of V. Independence from other randomness (T16*'s "V is
independent of that randomness", COL's "independent of the colouring") must be stated
separately with `IndepFun`.

**N3 (colour sets).** `randColouring` uses `Fin k` (0-based). For TPV's named colours R_{j,c}
(0 ≤ j < J, c ∈ [3]) and M, a Spec can use `pi fun _ => uniform C` with a colour type C of size
3J+1, or `randColouring` with an explicit bijection. The two agree up to relabelling. The Spec
reviewer must check that the bijection covers all k = 3J+1 colours.

**N4 (non-uniform label laws are built in the Spec).** The label κ of s4 (P(0)=1/2, P(c)=1/6),
the κ of PV (1/2, 1/8×4), the JS labels of s3:defCOL(iv) (ρ_l each, ∗ with 1 − M_l^{−2}) and the
truncated level (N1) have no named constructor in Defs. They will be built with
`ofFintype`/`ofFinset` or as `map`s of `uniform`/`pi`. The Spec reviewer must check those
weights; the Defs give no protection there.

**N5 (Lib definitions in statements).** `FinDist.IndepEvents` and the binomial law used for
s1:citChernoff live in `EG/Lib/Prob/Chernoff.lean`, which is not a locked Defs file (and is
currently untracked). That is fine for proved lemmas. A locked Spec statement, however, must use
only the vocabulary of this file (`iIndepFun`, `IsRSubset`, `randColouring`, …) and not these
Lib definitions.

**N6 (name clashes are loud, not silent).** `IndepFun`, `iIndepFun`, `pi`, `map`, `prod`,
`expect`, `bind` and `uniform` share names with Mathlib (`ProbabilityTheory.IndepFun`,
`Finset.pi`, `Finset.expect`, …). With both namespaces open, Lean reports ambiguity or picks the
only overload that typechecks, so no silent change of meaning is possible. Specs should still
write `μ.IndepFun`, `μ.prob`, `FinDist.pi` explicitly.

**N7 (`pi` needs a finite index).** Independence of an infinite family must use `iIndepFun`, which
allows infinite U. `pi` needs `Fintype ι`. Every family in the manuscript is finite (edges,
vertices, ancestors, rounds).

**N8 (`uniform` needs `Nonempty`).** The uniform 3-subset ζ_{h,u} ⊆ [4M_l] of s7 needs
4M_l ≥ 3 for its type to be nonempty. This holds (M_l ≥ 1), but the Spec must supply the
instance and must not silently change the type.

---

## Per-item verdicts
`FinDist`, `supp` (+ lemmas), `prob`, `expect`, `ofFinset`, `ofFintype`, `dirac`, `compProd`,
`prod`, `pi`, `map`, `bind`, `uniform`, `bernoulli`, `cond`, `selectSet`, `indepSubset`,
`rsubset`, `randColouring`, `IndepFun`, `iIndepFun`, `IsRSubset`: **all approve**. Notes N1–N8
are for downstream Spec work.
