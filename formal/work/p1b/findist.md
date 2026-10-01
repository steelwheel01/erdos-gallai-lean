# P1b task [findist]: FinDist, finite probability spaces with real weights (design note)

## Files and modules (all new)
- `EG/Defs/Prob/FinDist.lean` (module `EG.Defs.Prob.FinDist`, protected Defs, `@[expose]`): the
  structure, `supp`, `prob`, `expect`, and all constructions.
- `EG/Lib/Prob/Basic.lean` (module `EG.Lib.Prob.Basic`): the general API (task list).
- `EG/Lib/Prob/Named.lean` (module `EG.Lib.Prob.Named`): lemmas about the named distributions
  (uniform, Bernoulli, random colourings, random subsets). It is a separate file so that
  `Basic.lean` stays about 1000 lines.
- `EG/Lib/Prob/Indep.lean` (module `EG.Lib.Prob.Indep`, added in fix round 1): API for the
  vocabulary predicates `IndepFun`, `iIndepFun`, `IsRSubset`.
- `EGTest/Prob.lean` (module `EGTest.Prob`, non-module file): sanity checks.

All four compile with 0 errors and 0 warnings. `scripts/lint.py`: 0 findings. Axiom scan of
`EG.Lib.Prob.Named` (prefix EG, which covers the three EG modules): 302 constants, 0 use sorryAx,
0 violations. There is no `sorry`.

## Definitions (EG/Defs/Prob/FinDist.lean)
- `structure FinDist (Ω : Type*)`: `w : Ω → ℝ`, `w_nonneg : ∀ ω, 0 ≤ w ω`,
  `exists_finset : ∃ s : Finset Ω, (∀ ω ∉ s, w ω = 0) ∧ ∑ ω ∈ s, w ω = 1`; `@[ext]` on `w`.
- `supp μ : Finset Ω` is the canonical support `{ω | w ω ≠ 0}` (`Set.Finite.toFinset`), and
  `mem_supp : ω ∈ μ.supp ↔ μ.w ω ≠ 0`.
- `prob μ (A : Set Ω) := ∑ ω ∈ μ.supp, A.indicator μ.w ω`, and
  `expect μ X := ∑ ω ∈ μ.supp, μ.w ω * X ω`. On a `Fintype` these equal the sums over `univ`
  (`prob_eq_sum`, `prob_eq_sum_filter`, `expect_eq_sum`), and for any finite superset of the
  support as well (`*_eq_sum_of_supp_subset`).
- Constructors: `ofFinset`, `ofFintype` (`∑ ω, w ω = 1`).
- Constructions:
  - `dirac a`, the point mass;
  - `compProd μ K` on `α × β`, with `(a, b) ↦ μ.w a * (K a).w b` (the kernel `K` depends on the
    prefix);
  - `prod μ ν := compProd μ (fun _ => ν)`;
  - `pi (μ : ∀ i, FinDist (κ i))` for `[Fintype ι]`, with `f ↦ ∏ i, (μ i).w (f i)` (dependent
    coordinates);
  - `map f μ`, with `b ↦ μ.prob (f ⁻¹' {b})` (the codomain needs no `Fintype`);
  - `bind μ K := (compProd μ K).map Prod.snd`;
  - `uniform Ω` for `[Finite Ω] [Nonempty Ω]`, with weight `(Nat.card Ω)⁻¹`;
  - `bernoulli p h0 h1` on `Bool` (`true ↦ p`, `false ↦ 1 - p`);
  - `cond μ A (hA : 0 < μ.prob A)`, with `ω ↦ 1_A(ω) w(ω) / P(A)`;
  - `selectSet S f` (the subset of `S` selected by `f : S → Bool`);
  - `indepSubset S p h0 h1 := (pi fun a : S => bernoulli (p a) …).map (selectSet S)`, which puts
    each `a ∈ S` in the subset independently with probability `p a`;
  - `rsubset S ρ h0 h1 := indepSubset S (fun _ => ρ) …`, the ρ-random subset of s3's conventions
    (the manuscript sentence is quoted in the docstring);
  - `randColouring ι k [NeZero k] := pi fun _ : ι => uniform (Fin k)` ([s3:lemL15p], quoted). For
    edges, take `ι = ↥E` with `E : Finset (Sym2 V)`.

## Design decisions / deviations from the plan
1. **`FinDist Ω` has no `[Fintype Ω]` parameter.** The plan says "FinDist Ω for [Fintype Ω]". The
   distribution is instead *finitely supported*, and `prob` and `expect` are sums over the
   canonical support. The reason is instance robustness. A structure indexed by `[Fintype Ω]`
   makes `@FinDist (S → Bool) inst₁` and `@FinDist (S → Bool) inst₂` different types whenever two
   `Fintype`/`DecidableEq` instances are not defeq, which happens with `classical` vs. concrete
   `DecidableEq`, since `Pi.instFintype` needs `DecidableEq` of the domain. That gives hard type
   errors in dozens of downstream files. Here the type, `prob` and `expect` carry no instances at
   all, and every `Fintype`-dependent lemma is stated for an arbitrary instance. On a `Fintype`
   nothing changes for users: `sum_w : ∑ ω, μ.w ω = 1`, `prob_eq_sum`, `expect_eq_sum`. The only
   defs with instance arguments are `pi` (`[Fintype ι]`, needed for `∏ i`) and
   `randColouring`/`uniform` (only `Finite`/`Nonempty` Props and `NeZero`). `map` needs no
   `Fintype` of either side, so a random `Finset α` works without `Fintype α`. Computing
   probabilities *on* `Finset α` via `prob_eq_sum` still needs `Fintype (Finset α)`, but most
   lemmas (`prob_map`, `prob_mem_rsubset`, …) do not.
2. **Events are `Set Ω`**, written `μ.prob {ω | P ω}`. `Set.indicator` avoids `DecidablePred`
   arguments. `prob_coe_finset` handles Finset events.
3. **Almost-sure hypotheses and existence outputs use `0 < μ.w ω`**, for example
   `exists_of_prob_pos : 0 < μ.prob A → ∃ ω ∈ A, 0 < μ.w ω`, and
   `exists_le_expect : ∃ ω, 0 < μ.w ω ∧ X ω ≤ μ.expect X`.
4. **Conditioning.** "Fixing a prefix" (PLAN decision 3) appears in three forms:
   - `compProd`/`prod`, with `prob_prod_eq_sum : (μ.prod ν).prob A = ∑ a, μ.w a * ν.prob (A_a)`
     and the general `prob_compProd`, where the second stage may depend on the first;
   - `pi`, with `pi_eq_map_prod p` / `prob_pi_split p`, which fix the coordinates in `p` of a
     finite product;
   - `cond μ A hA` for conditioning on an event (Markov (c), "given any event of positive
     probability").

   `cond_prod_fst` / `map_snd_cond_prod_fst` formalize Markov (c)'s "given a fixed outcome of
   independent variables, the conditional law of the latter is their unconditional law".
5. **Markov [s1:citMarkov]**:
   - `prob_le_expect_div` (the cited statement) and `mul_prob_le_expect`;
   - general `one_sub_inv_le_prob_le_mul_expect` (`P(X ≤ cEX) ≥ 1 - 1/c`), including the
     case `EX = 0` that the manuscript handles separately;
   - (a) `two_thirds_le_prob_le_three_mul_expect`;
   - (b) `half_le_prob_le_four_mul_expect_and`, and the general
     `one_sub_inv_sub_inv_le_prob_and`;
   - (c) `two_thirds_mul_prob_le_prob_inter_cond` and `half_mul_prob_le_prob_inter_cond`,
     which are (a) and (b) applied to `μ.cond A hA`, together with `cond_prod_fst`.

   The hypothesis is `X ≥ 0` everywhere, as in the manuscript.
6. **Independence API**:
   - `prob_prod_set_prod`, `expect_prod_mul` and `expect_prod_mul_of_dependsOn` for two
     factors;
   - for finite products: `expect_pi_prod` / `expect_pi_prod_finset` (the product form needed
     for Chernoff/mgf), `prob_pi_forall_mem`, and `prob_pi_inter_of_dependsOn` /
     `expect_pi_mul_of_dependsOn` (events depending on disjoint sets of coordinates are
     independent, which covers "the labels are independent of the colours").
7. **Random subsets** are pushforwards of Bernoulli products, so the product structure is
   available for concentration (`prob_indepSubset` / `expect_indepSubset`). The manuscript's
   "each element independently with probability ρ" is characterised by
   `prob_indepSubset_superset_disjoint`, `P(A ⊆ T ∧ B ∩ T = ∅) = ∏_A p · ∏_B (1-p)`, and by the
   weight formula `rsubset_w : w T = ρ^|T| (1-ρ)^|S∖T|` for `T ⊆ S`. The general
   element-dependent `indepSubset` covers the thinning in [s4:lemTPV] proof, item (G2), and the
   "1/3" sets of s1:citThm16/citLem17.
8. **Colour classes**: `map_colourClass_randColouring` proves that the colour-`j` class of a
   uniform `k`-colouring is a `(1/k)`-random subset of all elements. This is the link used by
   L15⁺, where X_i is the set of edges of colour i.
9. Colours are `Fin k = {0, …, k-1}`, not `[k]`, and `k ≥ 1` is the instance `[NeZero k]`. A user
   with `hk : 1 ≤ k` writes `haveI : NeZero k := ⟨by omega⟩`.

## Lemma inventory (EG/Lib/Prob/Basic.lean)
- Weights: `mem_supp_iff_pos`, `w_eq_zero_of_notMem_supp`, `sum_w_of_supp_subset`, `sum_w`,
  `w_le_one`, `supp_nonempty`, `exists_w_pos`, `FinDist.nonempty`.
- Expectation:
  - `expect_eq_sum(_of_supp_subset)`, `expect_congr`;
  - `expect_const/zero/add/neg/sub/const_mul/mul_const/div_const/sum`;
  - `expect_mono(_ae)`, `expect_nonneg`, `expect_le_of_le`, `le_expect_of_le`,
    `expect_eq_zero_iff`.
- Probability:
  - `prob_eq_sum(_of_supp_subset)`, `prob_eq_sum_filter`, `prob_eq_expect`, `prob_coe_finset`,
    `prob_singleton`;
  - `prob_nonneg/univ/empty/congr/mono/mono_ae/le_one`;
  - `prob_union_add_inter`, `prob_union_le`, `prob_union_of_disjoint`, `prob_add_prob_compl`,
    `prob_compl`, `prob_inter_add_diff`, `prob_diff_ge`, `prob_inter_ge`;
  - `prob_biUnion_le`, `prob_iUnion_le`, `prob_biInter_ge`;
  - `prob_eq_zero_iff`, `prob_pos_iff`, `prob_eq_one_iff`;
  - `expect_sum_indicator`, `expect_card_filter` (first moment).
- Existence: `exists_of_prob_pos`, `nonempty_of_prob_pos`, `exists_le_expect`,
  `exists_ge_expect`, `exists_mem_inter_of_one_lt_add`, `exists_forall_notMem_of_sum_lt_one`,
  `exists_mem_le_mul_expect`, `exists_mem_le_expect_div`.
- Markov: see item 5.
- Conditioning on an event: `cond_w`, `supp_cond_subset`, `cond_w_pos_iff`, `expect_cond`,
  `prob_cond`, `prob_cond_self`.
- Dirac: `dirac_w`, `dirac_w_self`, `dirac_w_of_ne`, `supp_dirac`, `expect_dirac`, `prob_dirac`,
  `prob_dirac_of_mem`, `prob_dirac_of_notMem`.
- Map: `map_w`, `supp_map_subset`, `expect_map`, `prob_map`, `map_map`, `map_id(')`,
  `map_equiv_w`, `map_dirac`.
- compProd: `compProd_w`, `mem_supp_compProd`, `supp_compProd_subset`, `expect_compProd`
  (Fubini), `prob_compProd`, `prob_compProd_eq_sum`, `exists_le_prob_section` (fix a good prefix),
  `prob_compProd_le_of_forall`, `le_prob_compProd_of_forall`, `map_fst_compProd`,
  `prob_compProd_fst`.
- prod: `prod_w(')`, `expect_prod`, `expect_prod_swap`, `prob_prod`, `prob_prod_eq_sum`,
  `expect_prod_fst/snd`, `expect_prod_mul`, `map_fst_prod`, `map_snd_prod`, `prob_prod_fst/snd`,
  `prob_prod_set_prod`, `map_swap_prod`, `expect_prod_mul_of_dependsOn`, `cond_prod_fst`,
  `map_snd_cond_prod_fst`.
- bind: `expect_bind`, `prob_bind`, `bind_w`.
- pi: `pi_w`, `mem_supp_pi`, `supp_pi_subset`, `expect_pi_prod`, `expect_pi_prod_finset`,
  `prob_pi_forall_mem`, `prob_pi_univ_pi`, `expect_pi_eval`, `prob_pi_eval`, `map_eval_pi`,
  `pi_eq_map_prod`, `prob_pi_split`, `expect_pi_mul_of_dependsOn`, `prob_pi_inter_of_dependsOn`.

## Lemma inventory (EG/Lib/Prob/Named.lean)
- Uniform: `uniform_w`, `uniform_w_eq`, `uniform_w_pos`, `prob_uniform` (`|A|/|Ω|`),
  `expect_uniform`.
- Bernoulli: `bernoulli_w_true/false`, `expect_bernoulli`, `prob_bernoulli_true/false/eq_true`.
- Colourings: `randColouring_w`, `randColouring_eq_uniform`, `prob_randColouring_apply` (`1/k`),
  `prob_randColouring_forall_mem`, `map_colourClass_randColouring`.
- Random subsets:
  - `mem_selectSet(_coe)`, `selectSet_subset`;
  - `expect_indepSubset`, `prob_indepSubset`, `prob_indepSubset_subset`,
    `subset_of_indepSubset_w_pos`;
  - `prob_indepSubset_superset_disjoint`, `indepSubset_w`, `prob_superset_indepSubset`,
    `prob_disjoint_indepSubset`, `prob_mem_indepSubset`, `prob_notMem_indepSubset`,
    `expect_card_inter_indepSubset`;
  - `rsubset_w`, `prob_rsubset_subset`, `prob_mem_rsubset`, `prob_superset_rsubset`,
    `prob_disjoint_rsubset`, `prob_rsubset_superset_disjoint`, `expect_card_inter_rsubset`,
    `expect_card_rsubset`.

## Tests (EGTest/Prob.lean)
- Bernoulli(1/2): weights from the definition, `P{true} = P{false} = 1/2`, and an expectation.
- Two fair coins:
  - every weight is 1/4, and `P{(T,T)} = 1/4`;
  - the first coin is fair;
  - `P({T} × {T}) = 1/4`;
  - `P(coins agree) = 1/2`, by conditioning on the first coin;
  - `P(some head) = 3/4`, by complement;
  - one Fubini computation.
- Three coins with p = 1/10:
  - the coordinate law;
  - the union bound `P(some head) ≤ 3/10`;
  - independence `P(all heads) = 10⁻³`;
  - an existence statement from the union bound.
- Markov (a) on a coin.
- Conditioning a fair coin on heads gives `dirac true`.
- The uniform distribution on `Fin 6`.
- A 3-colouring: the `1/k` marginal and the weights.
- The weight formula of a (1/3)-random subset: `{0} ⊆ {0,1}` has weight 2/9, and `{2}` has 0.
- `P(1 ∈ T) = 1/3` and `E|T| = 1` for S = {0,1,2}.
- A colour class of a 2-colouring is a (1/2)-random subset.

## Open questions / notes for the integrator
- `EG.lean` and `EGTest.lean` need the imports `EG.Defs.Prob.FinDist`, `EG.Lib.Prob.Basic`,
  `EG.Lib.Prob.Named` and `EGTest.Prob`. I did not edit the roots.
- Plan §3 names the layer `Found.Prob` (`FinDist`, `Basic`, `Chernoff`, `Bernstein`,
  `RandomSets`). As the task asked, these files live at `EG/Defs/Prob/` and `EG/Lib/Prob/`. The
  plan's `RandomSets` (thinning, unions of independent random sets, uniform permutations and
  k-subsets) is not written yet. The basic random-set facts it needs are in `Named.lean`, so a
  later `RandomSets.lean` can import `Named`.
- Chernoff is not written (separate task). The hooks it needs are `expect_pi_prod(_finset)`
  (mgf factorisation), `expect_indepSubset` / `prob_indepSubset` (random sets as Bernoulli
  products), `prob_le_expect_div` (Markov applied to `exp(tX)`) and
  `map_colourClass_randColouring`.
- Possible later addition: a "sum of independent random sets" lemma (s3:lemL17s: "V₁ ∪ … ∪ V_ℓ
  is a ρ-random subset"), which is a statement about `pi` of `rsubset`s.
- Name-collision risk is low: everything is in `EG.FinDist`. `FinDist.nonempty` is `protected`.

## Fix round 1 (review: `work/p1b/findist.review1.md`)

I checked every issue myself. All four files named above plus the new
`EG/Lib/Prob/Indep.lean` compile with 0 errors, 0 warnings and 0 `sorry`
(`scripts/check.sh`). `python3 scripts/lint.py` reports 0 findings. The axiom scan of
`EG.Lib.Prob.Indep` (prefix EG, covering all EG Prob modules) inspected 387 constants: 0 use
sorryAx and 0 violations.

No existing statement changed. A script compared every `theorem`/`def` signature against HEAD:
all 24 + 141 + 38 old declarations are textually identical. Only two things changed besides
additions. `FinDist.cond` and `FinDist.map_map` are now `protected`, which is an attribute change,
and the pointwise Markov lemmas are now proved as corollaries of their new `_ae` variants.

| # | Issue | Verdict | What was done |
|---|---|---|---|
| 1 | coordinatewise map of a product | **fixed** | `map_pi` (`(pi μ).map (fun ω i => f i (ω i)) = pi fun i => (μ i).map (f i)`) and `map_prod_map` (`(μ.prod ν).map (Prod.map f g) = (μ.map f).prod (ν.map g)`) in Basic. Also: `map_congr_ae` (Basic); `map_selectSet_pi` / `map_selectSet_pi_rsubset` (Named). The last two say that a set selected element by element from independent labels, `a` chosen iff `f a (ω a)`, is `indepSubset S p` / `rsubset S ρ` as soon as each `(μ a).map (f a)` is Bernoulli. This is the s5 l. 67 zone argument, and it is quoted in the docstring. |
| 2 | mutual independence of many blocks | **fixed** | Basic has three forms for functions/events of pairwise disjoint blocks `B u` of coordinates of `pi μ`: `prob_pi_forall_of_dependsOn` (events: `P(⋂_{u∈s} A u) = ∏ P(A u)`), `expect_pi_prod_of_dependsOn` (`E ∏ X u = ∏ E X u`) and `map_pi_of_dependsOn` (law level, exactly the suggested `(pi μ).map (fun f u => g u f) = pi fun u => (pi μ).map (g u)`). All are proved by induction via `prob_pi_inter_of_dependsOn` / `expect_pi_mul_of_dependsOn`. The finset forms only need disjointness inside `s`. Indep has `iIndepFun_pi_of_dependsOn`, which is the same fact as an `iIndepFun` statement. The s4 (G4) sentence is quoted. |
| 3 | colour class in the ambient type | **fixed** | `map_selectSet_randColouring (E : Finset α) j : (randColouring E k).map (fun c => selectSet E fun e => decide (c e = j)) = rsubset E (1/k) _ _` (Named). It comes from `map_decide_eq_uniform` (`(uniform (Fin k)).map (· = j) = bernoulli (1/k)`), the general `map_eq_bernoulli` (an indicator with `P(true) = p` has law `bernoulli p`) and `map_selectSet_pi_rsubset`. |
| 4 | shared vocabulary for "ρ-random" and "independent" | **fixed** | See the details after this table. |
| 5 | `map_map` / `cond` name clashes | **fixed** | `FinDist.map_map` is now `protected`. I reproduced the "Ambiguous term map_map" error with `open EG EG.FinDist Finset`; with `protected` the short name no longer resolves, and the new internal uses write `FinDist.map_map`. `FinDist.cond` is now `protected` too (only dot notation `μ.cond A hA` is used anywhere), so it no longer shadows `Bool.cond`. A probe with `open EG EG.FinDist Finset Set Function` and `#check` of every public name, old and new, gives no ambiguity, and `cond true 1 2` elaborates. The Basic header has a "Names to qualify" note. |
| 6 | test docstring "Fubini in both orders" | **fixed** | The docstring was reworded to one order. A second test computes an asymmetric function with `expect_prod_swap`. |
| 7 | Markov only with pointwise `X ≥ 0` | **fixed** | Each Markov lemma now has an `_ae` variant with hypothesis `∀ ω, 0 < μ.w ω → 0 ≤ X ω`: `mul_prob_le_expect_ae`, `prob_le_expect_div_ae`, `prob_gt_mul_expect_le_ae`, `one_sub_inv_le_prob_le_mul_expect_ae`, `two_thirds_le_prob_le_three_mul_expect_ae`, `one_sub_inv_sub_inv_le_prob_and_ae`, `half_le_prob_le_four_mul_expect_and_ae` and `exists_mem_le_mul_expect_ae`. The helpers are `expect_nonneg_ae` and `expect_eq_zero_iff_ae`. The conditional forms (c) got `two_thirds_mul_prob_le_prob_inter_cond_ae` and `half_mul_prob_le_prob_inter_cond_ae`, which assume `X ≥ 0` only on the outcomes of `A` of positive weight (`nonneg_ae_cond`). The pointwise lemmas keep their exact statements and are one-line corollaries. |
| 8 | no `[Fintype Ω]` in `FinDist` (deviation from PLAN §3) | **not an issue for the code** | The reviewer endorses the design. The deviation and its reason are documented in design decision 1 above and in the `FinDist.lean` docstrings. The integrator records it in STATE.md / PLAN §3; I did not edit those files (outside my scope). |

### Issue 4 in detail

**Definitions.** I added three definitions to `EG/Defs/Prob/FinDist.lean`, in a new section
"Shared vocabulary". Spec statements import only `Defs`, and statements such as Chernoff
("independent indicators"), T16* ("ρ-random subset") and COL(c) ("independently of the
colouring") need these predicates. Each docstring quotes the manuscript.

- `IndepFun μ X Y`, defined as `∀ A B, P(X⁻¹A ∩ Y⁻¹B) = P(X⁻¹A)·P(Y⁻¹B)`.
  - This is the textbook event definition, with no instances.
  - Docstring: s3:defCOL "the labels are independent of the colours", s1:citMarkov (c), s5 l. 134.
- `iIndepFun μ X`, defined as `∀ (s : Finset U) (A : ∀ u, Set (β u)), P(∀ u ∈ s, X u ∈ A u) = ∏_{u∈s} P(X u ∈ A u)`.
  - The value types are dependent, and the condition is on finite subfamilies, so `U` needs no `Fintype`.
  - Docstring: s1:citChernoffGen "a sum of independent indicator variables", and s3:defCOL "colours of distinct edges are independent".
- `IsRSubset μ V S ρ`, defined as `∃ (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1), μ.map V = rsubset S ρ h0 h1`.
  - This is the reviewer's law-level idiom, with ρ ∈ [0,1] as part of the meaning ("For ρ∈[0,1], …", quoted).

**Faithfulness theorems (`EG/Lib/Prob/Indep.lean`).**
- `isRSubset_iff` gives the elementwise reading of the s3 convention. It is an iff with: ρ ∈ [0,1], a.s. `V ⊆ S`, the membership indicators `a ∈ V` (a ∈ S) are `iIndepFun`, and each has probability ρ.
- `indepFun_iff_map_eq_prod` and `iIndepFun_iff_map_eq_pi` (Fintype index) give the law-level forms that the reviewer proposed.

**Rest of the API (`Indep.lean`).**
- `IndepFun`:
  - `symm`, `comp`, `expect_mul`;
  - `IndepFun.map_cond`: conditioning on `X = x` leaves the law of `Y` unchanged. This is the general form of [s1:citMarkov](c), second clause.
  - `indepFun_map_iff` (transport along `map`), `indepFun_fst_snd`.
- `iIndepFun`:
  - `comp`, `indepFun` (pairwise), `map_eq_pi_subtype` (law of a finite subfamily), `expect_prod`;
  - `iIndepFun_map_iff`, `iIndepFun_eval_pi`, `iIndepFun_pi_of_dependsOn`.
- `IsRSubset`:
  - `map_eq`, `nonneg`, `le_one`, `prob_preimage`, `expect_comp`, `subset_ae`;
  - `prob_mem`, `prob_superset`, `prob_disjoint`, `expect_card`, `expect_card_inter`, `iIndepFun_mem`;
  - `isRSubset_selectSet`: a set selected by `iIndepFun` Bernoulli(ρ) indicators is ρ-random;
  - `isRSubset_map_iff`, `isRSubset_rsubset`.

**Documentation.** The idiom is documented in the Basic header ("Conventions for downstream
files"), in the Defs section docstring and in the Indep header.

### New tests (`EGTest/Prob.lean`)
- `map_prod_map` on negated coins.
- `map_pi`: the "colour = 0" indicators of a 3-colouring are independent Bernoulli(1/3) coins.
- `prob_pi_forall_of_dependsOn` with two disjoint blocks of four coins, giving 1/4.
- The ambient colour class `map_selectSet_randColouring`.
- `isRSubset_selectSet` from `iIndepFun_eval_pi`.
- `IsRSubset.expect_card` and `isRSubset_iff` marginals.
- `IndepFun.map_cond` on two coins.
- `iIndepFun.indepFun`.
- An `_ae` Markov application where `X < 0` on an outcome of weight 0. The pointwise lemma does not apply there.

### For the integrator
- New module: `EG.Lib.Prob.Indep`, to add to `EG.lean`. `EGTest.Prob` now imports it. The full
  module list is `EG.Defs.Prob.FinDist`, `EG.Lib.Prob.Basic`, `EG.Lib.Prob.Named`,
  `EG.Lib.Prob.Indep` and `EGTest.Prob`.
- `EG/Defs/Prob/FinDist.lean` gained three definitions (`IndepFun`, `iIndepFun`, `IsRSubset`),
  and `cond` became `protected`. These Defs changes should be in the next review and approval
  of the file.
- Line counts: FinDist 309, Basic 1229, Named 456, Indep 329, EGTest/Prob 285 (all < 1500).

## Fix round 2 (review: `work/p1b/findist.review2.md`, verdict APPROVE)

I checked each issue myself against the files and the manuscript (v5).

| # | Issue | Verdict | What was done |
|---|---|---|---|
| 1 | (cosmetic) docstrings cite manuscript line numbers | **fixed** | Every line-number citation in the Prob files is now a label plus a locator inside the labelled environment. I dropped the line numbers rather than keeping them next to the labels, because they would go stale when v6 lands. The quotes are unchanged. I checked each locator in the v5 source: the (G2)/(G4) items lie in the proof of s4:lemTPV (proof at s4.tex 140–317), and the other passages are where listed below. The changes: `indepSubset`: `[s1:citThm16] (statement)`, `[s4:lemTPV] proof, item (G2)`. `IndepFun`: `[s3:defCOL] (the list after "Consequently:")`, `[s5:lemE1] proof of (c)`. `iIndepFun`: `[s3:defCOL] (the list after "Consequently:")`. `map_pi`, `isRSubset_selectSet`, `map_selectSet_pi`: `[s5:lemZones] proof of (ii)`. `prob_pi_forall_of_dependsOn`, `iIndepFun_pi_of_dependsOn`: `[s4:lemTPV] proof, item (G4)`. One correction to the review: s5.tex l. 134 ("independently of the colouring of Y") is in the proof of **s5:lemE1**(c), not of s5:lemZones, so it is cited as `[s5:lemE1]`. `grep -E "l\. ?[0-9]+\|\.tex"` over `EG/Defs/Prob/FinDist.lean`, `EG/Lib/Prob/*.lean` and `EGTest/Prob.lean` now finds nothing. I also updated the one line citation in design note 7 above. The fix-round-1 table is a historical record and was left as it was. |
| 2 | (minor, optional) no named lemma for "ρ-random subset independent of the colouring" | **fixed** | Two lemmas were added to `EG/Lib/Prob/Indep.lean`, in a new subsection "A ρ-random subset independent of another random variable", and listed in the file header. `IsRSubset.cond_of_indepFun (hV : μ.IsRSubset V S ρ) (hi : μ.IndepFun c V) (x) (hx : 0 < μ.prob (c ⁻¹' {x})) : (μ.cond (c ⁻¹' {x}) hx).IsRSubset V S ρ` has a docstring quoting [s5:lemE1] proof of (c) and [s3:lemCOL](c). `IsRSubset.map_pair_eq_prod (hV) (hi) : μ.map (fun ω => (c ω, V ω)) = (μ.map c).prod (rsubset S ρ hV.nonneg hV.le_one)`. Both are the reviewer's one-liners. New tests in `EGTest/Prob.lean` use `colSet`, a uniform 2-colouring × an independent (1/3)-random subset of {0,1,2}. They check that after fixing the colouring, `P(2 ∈ V) = 1/3`, and they check the joint law. |
| 3 | (integrator) the "no `[Fintype Ω]`" deviation is not in STATE.md | **not an issue for the code: integrator action, outside this task's scope** | The deviation and its reason are already in design decision 1 above and in the `FinDist.lean` docstrings. `STATE.md` (repository root) and `PLAN_FORMALIZATION.md` are integrator-owned, so I did not edit them. I confirmed that `STATE.md` does not mention it yet. Suggested STATE.md entry: *"FinDist deviation (P1b findist, endorsed by both clean-room reviews): `EG.FinDist Ω` is a finitely supported weight function with no `[Fintype Ω]` parameter; `prob`/`expect` sum over the canonical support. Reason: an instance-indexed structure makes `@FinDist (S → Bool) inst₁ ≠ @FinDist (S → Bool) inst₂` when `Fintype`/`DecidableEq` instances are not defeq (classical vs. concrete), a type error in every downstream file. On a Fintype the usual formulas hold (`sum_w`, `prob_eq_sum`, `expect_eq_sum`)."* |
| 4 | (integrator) approval record for the Defs predicates | **not an issue for the code: integrator action, outside this task's scope** | `APPROVALS/**` and `LOCK.json` are integrator-owned. As the author I cannot supply an independent review either. Facts for the record: `LOCK.json` currently locks only `EG.Defs.Objects` and `EG.Spec.Main`, and no `EG.FinDist.*` constant is locked yet. The approval record therefore has to cover the whole of `EG/Defs/Prob/FinDist.lean`, not only the three new predicates. Round 2 changed no definition in that file, only docstring text (the four citations of issue 1), so the round-1 and round-2 back-translations still apply verbatim. Existing reviews: `findist.review1.md` (all round-1 definitions) and `findist.review2.md` §1 (all definitions, including `IndepFun`, `iIndepFun` and `IsRSubset`). The README requires one more independent clean-room review of those three predicates. After that, run `scripts/lock.py update --approval <record>`. |

### Checks after fix round 2
- No statement or definition body changed. I diffed each file against its pre-round copy.
  `FinDist.lean`, `Basic.lean` and `Named.lean` differ only in docstring lines.
  `Indep.lean` differs in docstrings plus the two new theorems. `EGTest/Prob.lean` has only
  additions: `colSet`, `colSet_isRSubset` and two examples.
- `lake build EG.Lib.Prob.Indep` succeeds. `scripts/check.sh` with `LEAN_NUM_THREADS=2` gives rc=0,
  0 errors and 0 sorry warnings on `EG/Defs/Prob/FinDist.lean`, `EG/Lib/Prob/Basic.lean`,
  `EG/Lib/Prob/Named.lean`, `EG/Lib/Prob/Indep.lean` and `EGTest/Prob.lean`.
- `python3 scripts/lint.py`: 0 findings. The axiom scan of `EG.Lib.Prob.Indep` (prefix EG)
  inspected 389 constants: 0 use sorryAx, 0 violations.
- Line counts: FinDist 310, Basic 1230, Named 456, Indep 353, EGTest/Prob 304 (all < 1500).
- Modules are unchanged from fix round 1: `EG.Defs.Prob.FinDist`, `EG.Lib.Prob.Basic`,
  `EG.Lib.Prob.Named` and `EG.Lib.Prob.Indep` (for `EG.lean`), and `EGTest.Prob` (for
  `EGTest.lean`).
