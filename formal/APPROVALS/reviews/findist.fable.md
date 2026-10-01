# Clean-room review: group `findist`, reviewer `fable`

Date: 2026-09-26. Reviewer: Claude Fable 5.1, an independent clean-room agent.

Scope: `EG/Defs/Prob/FinDist.lean` (sha256
`376a05b396cf30486015ba759cecad0574519e3a5836e6447513fb698490e161`, identical to HEAD `f18e1c2`;
the file is unmodified in the working tree). Every definition and predicate in that file:
`FinDist`, `supp` (+ its four lemmas), `prob`, `expect`, `ofFinset`, `ofFintype`, `dirac`,
`compProd`, `prod`, `pi`, `map`, `bind`, `uniform`, `bernoulli`, `cond`, `selectSet`,
`indepSubset`, `rsubset`, `randColouring`, `IndepFun`, `iIndepFun`, `IsRSubset`.

Disclosure. I read `APPROVALS/reviews/findist.opus.md` at the start to learn the expected format
of a review file, and `work/p1b/findist.md` to learn the intended idioms. I did not take any
verdict or test from either: every back-translation, edge case and scratch test below is my own,
and I compared each definition against the manuscript text myself. I read
`EG/Lib/Prob/{Basic,Named,Indep}.lean` to know which characterisations of the definitions are
already *proved* (I checked their axioms; none is assumed). I did not edit any repository file
other than writing this review.

Scratch file: `/tmp/claude-0/-home-user-Erdos-Proof/ab92a43f-e615-5aab-870d-cceae4796e61/scratchpad/FinDistReviewFable.lean`
(319 lines), compiled from `formal/` with `lake env lean`: rc = 0, 0 errors, 0 warnings. It
`#print`s every definition to see how it elaborates, and contains the tests quoted below.
`#print axioms` on the Lib theorems I cite (`isRSubset_iff`, `indepFun_iff_map_eq_prod`,
`iIndepFun_iff_map_eq_pi`, `randColouring_eq_uniform`, `indepSubset_w`, `rsubset_w`,
`map_selectSet_randColouring`, `IsRSubset.cond_of_indepFun`, `IndepFun.map_cond`,
`iIndepFun_eval_pi`, `prob_compl`, `exists_of_prob_pos`) gives only `propext`,
`Classical.choice`, `Quot.sound`.

**Overall verdict: APPROVE (with notes).** Every definition is the textbook object its docstring
names, the weights of every construction sum to 1 (this is the `exists_finset` field, proved in
each construction, not assumed), the independence built into `prod`/`pi`/`indepSubset`/
`randColouring` is genuine (verified both by the proved product formulas and by my own numeric
tests), and a statement `1 - η ≤ μ.prob {ω | 𝒫 ω}` built from these means exactly the
manuscript's "𝒫 holds with probability at least 1 − η". I found no mismatch with the manuscript.
The notes N1–N8 are limits of the layer and conventions that Spec authors and Spec reviewers must
respect; none is a defect of a definition.

---

## Manuscript text compared against

* s3, "Conventions for this section" (s3.tex l. 29–31): "For ρ∈[0,1], a *ρ-random subset* of a
  finite set S is a random subset of S that contains each element of S independently with
  probability ρ."
* `s3:lemL15p` (l. 100–108): "let k≥1 be an integer with s≥40kL. Give every edge of X a colour
  from [k], independently and uniformly at random, and for i∈[k] let X_i be the graph with vertex
  set V(X) whose edges are the edges of colour i. Then for each i∈[k], X_i is an
  (ε′,s/(2k))-expander with probability at least 1−2N^{−5}." Proof, Step 3 (l. 149–150): "Each
  of them lies in H independently with probability 1/k. So Z … ∼ Bin(e,1/k)".
* `s3:thmT16s` (l. 773–790): "Let ρ∈(0,1] and t≥1, and let V be a ρ-random subset of V(X). Here
  X is fixed; if X was itself produced at random, V is independent of that randomness. … Then,
  with probability at least 1−2^{86} t L^{19} ρ^{−3} N^{−3}, the graph X is (2^{12}L^4,t)-path
  connected through V." Proof Step 1 (l. 826–828): "Colour E(X) with K_* colours, uniformly and
  independently of V"; Step 2: "Condition on a colouring in which all classes are such
  expanders; V is still ρ-random."; Step 3: "|V|∼Bin(N,ρ)".
* `s3:defCOL` (l. 966–1025): "(i) Every edge of H_Y independently lies in Own_Y or in Lend_Y,
  with probability 1/2 each. … (iv) … draw a label lab_{Y,l}(y)∈{∗}∪{0,…,K_l−1} with
  P(lab=j)=ρ_l … Formally, every edge e of H_Y carries three independent uniform random
  variables …. Consequently: colours of distinct edges are independent; … the labels are
  independent of the colours; … for fixed (l,j), the set T_j(Y,l) is a ρ_l-random subset of
  V(Y), independent of the colouring".
* `s1:citChernoff` (s1.tex l. 419–426): "Let n be an integer, 0≤δ,p≤1, X∼Bin(n,p) and
  μ:=E X=np. Then P(X>(1+δ)μ)≤e^{−δ²μ/3} and P(X<(1−δ)μ)≤e^{−δ²μ/2}."
* `s1:citChernoffGen` (l. 784–786): "Let X=∑_{i=1}^m I_i be a sum of independent indicator
  variables with P(I_i=1)=p_i".
* `s1:citMarkov` (l. 819–839): "If X≥0 and a>0 then P(X≥a)≤E X/a. Consequently: (a) for X≥0,
  P(X≤3E X)≥2/3; (b) for X₁,X₂≥0, P(X₁≤4E X₁ and X₂≤4E X₂)≥1/2; (c) (a) and (b) hold with P and
  E replaced by the conditional probability and expectation given any event of positive
  probability, or given any fixed outcome of variables that are independent of the variables
  being drawn." Derivation of (c): "if the conditioning fixes variables independent of those
  being drawn, the conditional law of the latter is their unconditional law."
* `s1:citThm16` (l. 614–618): "let V⊆V(G) contain each vertex independently with probability
  1/3".
* `s4:lemTPV` (s4.tex l. 99–131): "The *labels* of the run are the following independent random
  variables: (a) a uniform colouring of E(O) with the k colours R_{j,c} (0≤j<J, c∈[3]) and M;
  (b) for every v∈P a level lev(v)∈{0,1,2,…} with P(lev(v)≥j)=2^{−j} for all j≥0; (c) for every
  v∈Z a label κ(v)∈{0,1,2,3} with P(κ(v)=0)=1/2 and P(κ(v)=c)=1/6 for c∈[3]." … "P(G_TPV) ≥
  1/2 − η_TPV(N)". Proof (G2) (l. 176–179): "Using auxiliary independent coins, keep each
  v∈V_{j,c} independently with probability (1/L)/P(v∈V_{j,c}); the kept set V′ is a (1/L)-random
  subset of Z (each vertex independently with probability exactly 1/L), independent of the
  colouring, and V′⊆V_{j,c}." (G4): "the variables I_u (u∈A_w(w)) depend on pairwise distinct
  edges wu and distinct vertices u, so they are independent".
* `s5:lemE1` proof of (c) (s5.tex l. 134): "contains each vertex of Y independently with
  probability ρ_Y … independently of the colouring of Y."
* PLAN_FORMALIZATION.md §3 decision 3 ("Every random object is a finite family of independent
  labels with real parameters … Every conclusion is deterministic existence … 'Conditioning' is
  always fixing a prefix of coordinates") and R5 ("Truncate vortex levels at J … Every probability
  space becomes finite").

I also checked that every manuscript sentence quoted in a docstring of the file is a verbatim
quote of the manuscript source (s3 conventions, s3:lemL15p, s1:citThm16, s4:lemTPV (G2),
s3:defCOL, s1:citMarkov(c), s1:citChernoffGen, s5:lemE1(c)); they are.

---

## Definitions

### `FinDist Ω` (structure, `@[ext]`)
Elaborates as `w : Ω → ℝ`, `∀ ω, 0 ≤ w ω`, `∃ s : Finset Ω, (∀ ω ∉ s, w ω = 0) ∧ ∑ ω ∈ s, w ω = 1`.
Back-translation: a finitely supported probability mass function on `Ω`, total mass exactly 1
(not a sub-probability, not a signed measure). `@[ext]` gives `x.w = y.w → x = y` (checked with
`#check`), so distributions are equal iff their weights are. The type is universe polymorphic
(`Type u → Type u`, checked) and carries no `Fintype`/`DecidableEq` instance, so no instance
diamond can produce two different `FinDist Ω` types. Edge cases: `Ω` empty has no `FinDist`
(I proved `IsEmpty (FinDist Empty)`), which is right, since ∅ carries no probability measure;
infinite `Ω` is allowed, with finite support. Expressiveness against the manuscript: every random
object is finite except the geometric level of s4 (N1). **approve**

### `finite_support`, `supp`, `mem_supp`, `supp_subset`, `sum_supp_eq_of_subset`, `sum_w_supp`
`supp μ = {ω | w ω ≠ 0}` as a `Finset` (via `Set.Finite.toFinset`), and `w ≠ 0 ↔ 0 < w` because
`w ≥ 0`. The four lemmas are correct statements with proofs (the weights sum to 1 over the
support). **approve**

### `prob μ A = ∑ ω ∈ μ.supp, A.indicator μ.w ω`
Back-translation: P(A) = ∑_{ω ∈ A} w(ω), for an arbitrary `A : Set Ω`; the sum can be restricted
to the support because the weights vanish off it. In a discrete space every subset is an event,
so nothing is lost by taking all `Set Ω`; `Set.indicator` is classical, so no `DecidablePred`
enters the definition. Tests: on the infinite type ℕ, `(dirac 5).prob {n | 3 ≤ n} = 1` and
`(dirac 5).prob {n | n ≤ 3} = 0`; a fair coin has `prob univ = 1`; on a `Fintype` it equals
`∑ ω, A.indicator μ.w ω` (`prob_eq_sum`). **approve**

### `expect μ X = ∑ ω ∈ μ.supp, μ.w ω * X ω`
E X for any real `X`, with no integrability condition, since the support is finite. Test: for a
fair coin, E[3·1_true + 1·1_false] = 2. **approve**

### `ofFinset`, `ofFintype`
Explicit constructors from nonnegative weights summing to 1 over `s`, resp. over `univ`. They
store no instance. **approve** (N4: this is how Specs will build the non-uniform label laws.)

### `dirac a`
`w = 1_{{a}}` (indicator of `{a}` applied to the constant function `1`). Tests: `w a = 1`,
`w 4 = 0` for `a = 3`. **approve**

### `compProd μ K`
`w (a, b) = μ.w a * (K a).w b`. This is the two-stage experiment "draw a ∼ μ, then b ∼ K a", the
manuscript's "fix a prefix"/"given a fixed outcome" structure (PLAN decision 3). The kernel may
genuinely depend on the first coordinate: my test kernel is `dirac true` after `true` and a fair
coin after `false`, giving `w (true, false) = 0` and `w (false, false) = 1/4`. Total mass 1 is
proved in the definition. **approve**

### `prod μ ν = compProd μ (fun _ => ν)`
`w (a, b) = μ.w a * ν.w b`: the independent product. Test: two fair coins give `w (true, false)
= 1/4`; `indepFun_fst_snd` (proved) says the coordinates are `IndepFun`. **approve**

### `pi μ` (`[Fintype ι]`, dependent `κ`)
`w f = ∏ i, (μ i).w (f i)`: the independent product of a finite family. The `Fintype ι` is a
data argument, but `Subsingleton (Fintype ι)` is a Mathlib instance
(`Mathlib/Data/Fintype/Defs.lean:258`), and I proved `@pi ι i₁ κ μ = @pi ι i₂ κ μ` for any two
instances, so the value does not depend on the instance (see N5 for the engineering caveat).
Edge case `ι = Fin 0`: the unique function has weight 1 (empty product), which is correct.
Test: over `Fin 3` fair coins every `f` has weight 1/8. Mutual independence of the coordinates
is `iIndepFun_eval_pi` (proved), which I used on `randColouring (Fin 5) 3`. **approve**

### `map f μ`
`w b = μ.prob (f ⁻¹' {b})`: the pushforward (law of `f`). It needs no `Fintype` on either side,
so laws on `Finset α` work for infinite `α`. Non-injective `f` is handled by summing the fibre:
tests `(coin.map fun _ => ()).w () = 1` and `(coin.map fun _ => true).w false = 0`. **approve**

### `bind μ K = (compProd μ K).map Prod.snd`
`w b = ∑_a μ.w a · (K a).w b`: the mixture. **approve**

### `uniform Ω` (`[Finite Ω] [Nonempty Ω]`)
`w ≡ (Nat.card Ω)⁻¹` in ℝ. `Nat.card` is the true cardinality of a finite type and is ≥ 1 by
`Nonempty`, so no division by zero happens. Both instance arguments are `Prop`s, so no diamonds.
Test: `(uniform (Fin 3)).w x = 1/3`; `Fin k` is nonempty from `[NeZero k]` alone (core instance
`Fin.instInhabited`). Expressiveness: s7's "uniformly random bijection / 3-subset / linear order"
are uniform laws on finite nonempty types, so they are expressible (N8). **approve**

### `bernoulli p h0 h1`
The one place where a name could silently change the meaning: inside `namespace FinDist`, `cond`
might have referred to `FinDist.cond`. `#print bernoulli` shows `w := fun b => bif b then p else
1 - p`, i.e. `Bool.cond` (the protected `FinDist.cond` is defined later and is `protected`
anyway). I checked by `rfl`: `w true = p`, `w false = 1 - p`, so `true` = "success" with
probability `p`. The domain `p ∈ [0,1]` is required by the two proof arguments and is exactly
the manuscript's range; proof irrelevance makes `bernoulli p h0 h1 = bernoulli p h0' h1'` by
`rfl`. **approve**

### `FinDist.cond μ A hA` (`protected`)
`w ω = 1_A(ω) μ.w ω / μ.prob A`, requiring `0 < μ.prob A`. This is conditioning on an event of
positive probability, s1:citMarkov(c) first clause. Test: a fair coin conditioned on `{true}` has
`w true = 1`. **approve**

### `selectSet S f`
`{a ∈ S | f ⟨a, _⟩ = true}` as a `Finset α` (`attach`, `filter`, `map` along the subtype
embedding). No `DecidableEq α` is needed. Test: `selectSet {0,1,2} (fun a => decide (a.1 ≠ 1))
= {0, 2}` by `decide`. **approve**

### `indepSubset S p h0 h1`
The law of `{a ∈ S | coin_a = true}` where `(coin_a)_{a ∈ S}` are independent Bernoulli(`p a`)
coins: "each `a ∈ S` independently with probability `p a`". `p` is constrained to `[0,1]` only on
`S`, and values off `S` do not enter (the `pi` is indexed by `↥S`). This is the element-dependent
form needed for s4:lemTPV (G2) ("keep each v … independently with probability
(1/L)/P(v∈V_{j,c})") and for s1:citThm16 ("each vertex independently with probability 1/3").
Evidence: the proved weight formula `indepSubset_w` (`P(T) = ∏_{a∈T} p a · ∏_{a∈S∖T} (1 − p a)`
for `T ⊆ S`, else 0); my test with `S = {0,1}`, `p 0 = 1/2`, `p 1 = 1/4`: `w {0} = 1/2 · 3/4` and
`P(0 ∈ T) = 1/2`, which pins the orientation `true` = "included". **approve**

### `rsubset S ρ h0 h1 = indepSubset S (fun _ => ρ)`
Exactly the s3 convention: "a random subset of S that contains each element of S independently
with probability ρ", with "ρ ∈ [0,1]" enforced by the proof arguments. Evidence: `rsubset_w`
(`P(T) = ρ^{|T|}(1−ρ)^{|S∖T|}` for `T ⊆ S`) and `prob_mem_rsubset` (`P(a ∈ T) = ρ`), both
proved; my tests: for `S = {0,1,2}`, ρ = 1/3, `w {0,2} = (1/3)²·(2/3)` (so it is not ρ^{|T|}
alone) and `w {3} = 0`. Edge cases, each proved as an equality of distributions: ρ = 1 gives
`dirac S`, ρ = 0 gives `dirac ∅`, `S = ∅` gives `dirac ∅` for every ρ. All three are the correct
laws. **approve**

### `randColouring ι k` (`[Fintype ι] [NeZero k]`)
`pi (fun _ : ι => uniform (Fin k))`: every element of `ι` independently receives a uniform
colour from `{0, …, k−1}`. This is s3:lemL15p's "Give every edge of X a colour from [k],
independently and uniformly at random" with `ι = ↥E(X)`, and s4:lemTPV(a)'s "uniform colouring
of E(O) with the k colours". `NeZero k` is the manuscript's `k ≥ 1`. Colours are 0-based instead
of `[k] = {1,…,k}`, a relabelling that changes no probability (N3). Evidence: straight from the
definition, `w c = ∏_{i} k⁻¹` (my test without Lib lemmas), every 3-colouring of a 2-set has
weight 1/9, `P(c e = j) = 1/3`, the coordinates are `iIndepFun`, and `ι = Fin 0` gives weight 1
to the unique colouring. The proved `map_selectSet_randColouring` says the colour-`j` class
`{e ∈ E | c e = j}` is a `(1/k)`-random subset of `E`, which is precisely L15⁺ Step 3 "Each of
them lies in H independently with probability 1/k". **approve**

### `IndepFun μ X Y`
`∀ A B, P(X ∈ A ∧ Y ∈ B) = P(X ∈ A) · P(Y ∈ B)`: the textbook definition, quantifying over all
subsets (all subsets are events here). `X ⁻¹' A ∩ Y ⁻¹' B` parses as `(X ⁻¹' A) ∩ (Y ⁻¹' B)`
(checked in `#print`). Equivalent to "joint law = product of marginals"
(`indepFun_iff_map_eq_prod`, proved), and `IndepFun.map_cond` (proved) is exactly Markov (c)'s
"the conditional law of the latter is their unconditional law". This is the meaning of
s3:defCOL "the labels are independent of the colours", s3:thmT16s "V is independent of that
randomness", s5:lemE1(c) "independently of the colouring of Y".
Non-vacuity: a fair coin is not independent of itself (`¬ coin.IndepFun id id`, 1/2 ≠ 1/4),
while the coordinates of `coin.prod coin` are. **approve**

### `iIndepFun μ X` (index `U`, dependent values `β u`)
`∀ (s : Finset U) (A : ∀ u, Set (β u)), P(∀ u ∈ s, X u ∈ A u) = ∏_{u∈s} P(X u ∈ A u)`: standard
*mutual* independence, on finite subfamilies, so `U` may be infinite. `s = ∅` reads `P(Ω) = 1`
(checked). It is mutual, not merely pairwise: with two fair coins and `X = (fst, snd, xor)`, I
proved `IndepFun (X 0) (X 2)` but `¬ iIndepFun X` (P(all true) = 0 ≠ 1/8). Law form for a
`Fintype` index: `iIndepFun_iff_map_eq_pi` (proved). This matches s1:citChernoffGen "independent
indicator variables", s3:defCOL "colours of distinct edges are independent" and s4:lemTPV (G4).
**approve**

### `IsRSubset μ V S ρ`
`∃ (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1), μ.map V = rsubset S ρ h0 h1`: ρ ∈ [0,1] and the *law* of the
random set `V` is the ρ-random-subset law on `S`. The elementwise reading, proved as an `iff`
(`isRSubset_iff`): `V ⊆ S` almost surely, the indicators `[a ∈ V]` (`a ∈ S`) are `iIndepFun`,
and each has probability ρ. That is word for word the s3 convention. Non-vacuity, all proved:
`(dirac ∅).IsRSubset id {0} (1/2)` is false; `IsRSubset _ _ {0} 2` and `IsRSubset _ _ {0} (-1)`
are false for every `μ`, `V`; `(dirac {5}).IsRSubset id {0} 1` is false (a set that leaves `S`
with positive probability is never ρ-random in `S`); `rsubset S (1/3)` with `V = id` satisfies
it. Model independence: for every `(Ω, μ, V)` with `IsRSubset V S ρ` and every property `P`,
`μ.prob {ω | P (V ω)} = (rsubset S ρ _ _).prob {T | P T}` (proved via `prob_preimage`), so a
Spec quantifying over all such models is equivalent to one about the canonical `rsubset`.
**approve**

---

## "Probability ≥ p" statements

The manuscript's "with probability at least 1 − η, 𝒫" becomes `1 - η ≤ μ.prob {ω | 𝒫 ω}`, or
equivalently `μ.prob {ω | ¬ 𝒫 ω} ≤ η` (via `prob_compl`, which needs total mass exactly 1 and
has it). Nothing in the definitions can make such a statement mean something else:
* `prob` is the exact total weight of the event; no measurability or decidability condition is
  hidden in it;
* the total mass is exactly 1, so complements behave;
* the manuscript's conclusions are deterministic existence statements, and
  `exists_of_prob_pos : 0 < μ.prob A → ∃ ω ∈ A, 0 < μ.w ω` (proved) delivers a witness of
  positive weight, which is the only kind of witness the manuscript ever uses.

The manuscript patterns are all expressible with the locked vocabulary alone:
* "X fixed, V ρ-random" (T16*): quantify over `μ V` with `μ.IsRSubset V X.verts ρ`, or state it
  for `rsubset` directly; equivalent by the model-independence test above.
* "V independent of the colouring c" (COL(c), E1(c), T16* "independent of that randomness"):
  `μ.IsRSubset V S ρ ∧ μ.IndepFun c V`; conditioning on a colouring (T16* Step 2 "Condition on
  a colouring …; V is still ρ-random") is `IsRSubset.cond_of_indepFun`.
* "for each i ∈ [k], X_i is an expander with probability ≥ 1 − 2N^{−5}" (L15⁺): an event on
  `randColouring ↥E k`, with the class `selectSet E (fun e => decide (c e = i))`.
* "|V| ∼ Bin(N, ρ)", "Z ∼ Bin(e, 1/k)" (Chernoff uses): counts of the mutually independent
  membership indicators given by `IsRSubset.iIndepFun_mem`/`isRSubset_iff`.
* Markov (a)–(c): `expect`, `prob`, `cond`, and `IndepFun.map_cond` for the second clause of
  (c).

---

## Notes for Spec authors and Spec reviewers (not defects of the definitions)

**N1 (finite support vs the geometric level; most important).** s4:lemTPV(b), s4:lemPV and
s4:thmVXp draw "a level lev(v)∈{0,1,2,…} with P(lev(v)≥j)=2^{−j} for all j≥0", an infinitely
supported law. No `FinDist` has it: I proved `no_geometric : ∀ μ : FinDist ℕ, ¬ ∀ j,
μ.prob {n | j ≤ n} = (1/2)^j` in the scratch file. The s4.tex in the repository still states the
untruncated law, so the Specs must implement PLAN R5: the truncated level lev′ = min(lev, J)
with P(lev′ = j) = 2^{−(j+1)} for j < J and P(lev′ = J) = 2^{−J}, hence P(lev′ ≥ j) = 2^{−j} for
0 ≤ j ≤ J. I checked in the s4 text that every derived object depends on the level only through
min(lev, J): U_j only for j ≤ J (including U_J in (G5)), W_j only for j < J, and Z_j, V_{j,c}
only for j < J (through U_{j+1}, j+1 ≤ J). So the truncation is lossless. A Spec reviewer of
TPV/PV/VX⁺ must check the truncated weights, in particular P(lev′ = J) = 2^{−J} (not 2^{−(J+1)}).

**N2 (ρ > 0, and independence is a separate clause).** `IsRSubset` allows ρ = 0, as the s3
convention does; s3:thmT16s needs ρ ∈ (0,1], so its Spec must add `0 < ρ`. `IsRSubset` fixes
only the law of `V`; "independent of that randomness" / "independent of the colouring" must be
stated separately with `IndepFun`.

**N3 (colour sets).** `randColouring` colours with `Fin k` (0-based). s4:lemTPV's named colours
R_{j,c} (0 ≤ j < J, c ∈ [3]) and M need either `pi fun _ => uniform C` with an explicit colour
type `C` of size 3J+1, or `randColouring` with a bijection; a Spec reviewer must check the
bijection covers exactly the k = 3J+1 colours.

**N4 (non-uniform label laws are built in the Spec).** κ of TPV (1/2, 1/6, 1/6, 1/6), κ of PV
(1/2, 1/8 × 4), the JS labels of s3:defCOL(iv) (ρ_l each, ∗ with 1 − M_l^{−2}) and the truncated
level (N1) have no named constructor here; they will be `ofFintype`/`ofFinset` terms or `map`s
of `uniform`/`pi`. The Defs give no protection there; the Spec reviewer must check the weights.

**N5 (`pi`/`randColouring` take `Fintype ι` as data).** Any two instances give propositionally
equal distributions (proved above via `Subsingleton (Fintype ι)`), but `rw`/`simp` match
syntactically, so a Spec should use the canonical instance (e.g. the `Finset` coe-sort instance
for `↥E`) and never introduce a second one. This is an engineering hazard, not a semantic one.

**N6 ("almost surely" means "on outcomes of positive weight").** `prob` ignores weight-0
outcomes, and `IsRSubset` gives `V ω ⊆ S` only for `0 < μ.w ω` (`IsRSubset.subset_ae`). A Spec
that asserts a pointwise property for *every* `ω : Ω` (rather than `∀ ω, 0 < μ.w ω → …` or a
`prob` statement) is stronger than the manuscript on weight-0 outcomes and may be unprovable
from `IsRSubset`/`IndepFun` hypotheses. Conversely, the existence principles return outcomes
with `0 < μ.w ω`, which is what downstream deterministic statements should consume.

**N7 (Lib definitions are not locked).** `FinDist.IndepEvents` and the Chernoff statements live
in `EG/Lib/Prob/Chernoff.lean` (currently modified in the working tree by other work). Proved
lemmas there are fine to use in proofs, but a locked Spec statement must be phrased with the
vocabulary of this file only (`iIndepFun`, `IsRSubset`, `IndepFun`, `randColouring`, `rsubset`,
`pi`, `prob`, `expect`).

**N8 (`uniform` needs `Nonempty`).** s7's "uniformly random 3-subset ζ ⊆ [4M_l]" needs
4M_l ≥ 3 to have a nonempty type; the Spec must supply the instance from the hypothesis and not
change the type to make it nonempty.

Two smaller observations. (i) Name overloads: `pi`, `map`, `prod`, `expect`, `IndepFun`,
`iIndepFun`, `uniform`, `bind` exist in Mathlib namespaces too; with both open, Lean either
reports an ambiguity or picks the unique overload that typechecks, so no silent change of
meaning is possible; `FinDist.cond` is `protected` and `bernoulli` provably uses `Bool.cond`.
(ii) The `[s3:…]`/`[s1:…]` docstring tags on `rsubset`, `randColouring`, `indepSubset`,
`IndepFun`, `iIndepFun`, `IsRSubset` quote the manuscript verbatim (checked against the .tex).

---

## Per-item verdicts

`FinDist`, `finite_support`/`supp`/`mem_supp`/`supp_subset`/`sum_supp_eq_of_subset`/
`sum_w_supp`, `prob`, `expect`, `ofFinset`, `ofFintype`, `dirac`, `compProd`, `prod`, `pi`,
`map`, `bind`, `uniform`, `bernoulli`, `cond`, `selectSet`, `indepSubset`, `rsubset`,
`randColouring`, `IndepFun`, `iIndepFun`, `IsRSubset`: **approve**, all of them. Notes N1–N8
are for downstream Spec work and do not block locking this file.
