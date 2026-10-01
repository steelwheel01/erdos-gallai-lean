# Clean-room review, round 1: task [findist] (FinDist: finite probability spaces with real weights)

Reviewer: clean-room agent. I edited no Lean file. Files reviewed: `EG/Defs/Prob/FinDist.lean`,
`EG/Lib/Prob/Basic.lean`, `EG/Lib/Prob/Named.lean`, `EGTest/Prob.lean`, and the design note
`work/p1b/findist.md`. Manuscript passages: s1:citMarkov (s1.tex l. 819–842, statement and
derivation), the ρ-random subset convention (s3.tex l. 29–31), s3:lemL15p (s3.tex l. 100–110),
s1:citThm16 (s1.tex l. 617), the s4:lemTPV thinning (s4.tex l. 170–200) and s5.tex l. 67 / l. 134
(zones as ρ-random subsets "independently of the colouring"). PLAN_FORMALIZATION.md §3 decision 3.

**Verdict: approve.** Every definition is a faithful model of the finite probability the
manuscript uses. Every stated manuscript result (Markov with (a), (b), (c); the ρ-random subset
convention; the uniform k-colouring of L15⁺) is proved in exactly the manuscript's form or in a
stronger one. Nothing is weakened. Lint, the axiom scan and compilation are clean, and the
non-vacuity probes pass. The issues below are usability additions, all of them easy and none
blocking. The most useful one is a lemma saying that a coordinatewise map of a product is the
product of the maps (issue 1). I proved it in 6 lines in a scratch file.

## 1. Fidelity (back-translation)

### Definitions (EG/Defs/Prob/FinDist.lean)
| Lean | Plain mathematics | Source | Match |
|---|---|---|---|
| `structure FinDist Ω` (`w`, `w_nonneg`, `exists_finset`) | A function w : Ω → ℝ with w ≥ 0, vanishing outside some finite set s, and ∑_{ω∈s} w(ω) = 1. So it is a finitely supported probability mass function. | PLAN §3 d.3 ("FinDist Ω for [Fintype Ω]") | Yes, and more general. On a Fintype it is exactly "w ≥ 0, ∑ w = 1" (`ofFintype`, `sum_w`). See the deviation note below. |
| `supp μ` | {ω : w(ω) ≠ 0}, a finite set (= {w > 0} by `mem_supp_iff_pos`) | infrastructure | yes |
| `prob μ A` | ∑_{ω ∈ supp} 1_A(ω) w(ω) = P(A) | "Prob" | Yes. Equals ∑_{ω∈A} w(ω) over any finite superset of the support (`prob_eq_sum_of_supp_subset`, `prob_eq_sum_filter`). |
| `expect μ X` | ∑_{ω ∈ supp} w(ω) X(ω) = E X | "Ex" | yes (`expect_eq_sum`) |
| `ofFinset`, `ofFintype` | constructors from explicit weights | — | yes |
| `dirac a` | point mass at a | task | yes |
| `compProd μ K` | Law of (a, b), where a ~ μ and then b ~ K(a). The weight is μ(a)·K(a)(b). | "conditioning = fixing a prefix" | yes |
| `prod μ ν` | independent product, weight μ(a)ν(b) | task | yes |
| `pi μ` ([Fintype ι]) | Independent product over a finite index set, weight ∏_i μ_i(f(i)). Dependent coordinate types are allowed. | task | Yes. For ι = ∅ it is the point mass at the unique function, as it should be. |
| `map f μ` | law of f(ω): weight of b = μ(f⁻¹{b}) | task | yes |
| `bind μ K` | mixture ∑_a μ(a) K(a) | — | yes (`bind_w`) |
| `uniform Ω` ([Finite] [Nonempty]) | weight 1/\|Ω\| | task | yes |
| `bernoulli p h0 h1` | P(true) = p, P(false) = 1 − p, for 0 ≤ p ≤ 1 | task | yes |
| `cond μ A hA` | P(· \| A): weight 1_A(ω) w(ω) / P(A), for P(A) > 0 | citMarkov (c) | yes |
| `selectSet S f` | {a ∈ S : f(a) = true} | — | yes |
| `indepSubset S p` | The random T ⊆ S that contains each a ∈ S independently with probability p(a). It is the pushforward of ∏_{a∈S} Bernoulli(p(a)). | s1:citThm16 l. 617 ("contain each vertex independently with probability 1/3"), s4 l. 176 (thinning) | Yes. The joint law is proved: `prob_indepSubset_superset_disjoint`, `indepSubset_w` = ∏_T p · ∏_{S∖T}(1−p) on T ⊆ S and 0 otherwise. |
| `rsubset S ρ` | the ρ-random subset of S | s3 l. 29–31: "For ρ∈[0,1], a ρ-random subset of a finite set S is a random subset of S that contains each element of S independently with probability ρ." (quoted in the docstring) | Yes. `rsubset_w`: w(T) = ρ^{\|T\|}(1−ρ)^{\|S∖T\|} for T ⊆ S and 0 otherwise. The proof arguments are irrelevant: `rsubset S ρ a c = rsubset S ρ b d` holds by `rfl` (checked). |
| `randColouring ι k` ([NeZero k]) | uniform independent colouring ι → Fin k | s3:lemL15p: "Give every edge of X a colour from [k], independently and uniformly at random." (quoted) | Yes. Fin k stands for [k], and `NeZero k` for k ≥ 1. `randColouring_eq_uniform`, `prob_randColouring_apply` (= 1/k) and `prob_randColouring_forall_mem` (independence) are proved. |

**Deviation from the plan: no `[Fintype Ω]` in the type.** The type is more general than the
plan, not weaker. The author's reason (a `Fintype`-indexed structure would make
`@FinDist (S → Bool) inst₁` and `@FinDist (S → Bool) inst₂` different types when the instances
are not defeq) is correct and important for dozens of downstream files. On a Fintype all the
expected sum formulas are available (`sum_w`, `prob_eq_sum`, `prob_eq_sum_filter`,
`expect_eq_sum`). I endorse this. The integrator should record it in STATE.md, and optionally in
PLAN §3, since the plan text still says "for [Fintype Ω]".

### Statements (EG/Lib/Prob/Basic.lean, Named.lean)
- **[s1:citMarkov]** "If X≥0 and a>0 then P(X≥a)≤EX/a": `prob_le_expect_div (hX : ∀ ω, 0 ≤ X ω)
  (ha : 0 < a) : P{a ≤ X} ≤ E X / a`. Identical, including the non-strict `≥ a`.
  `mul_prob_le_expect` is the multiplied-out form and needs no condition on a.
- **(a)** "for X≥0, P(X≤3EX)≥2/3": `two_thirds_le_prob_le_three_mul_expect`: `2/3 ≤ P{X ≤ 3·E X}`.
  Identical, with ≤ in both places. The case E X = 0, which the manuscript derivation treats
  separately, is covered through `prob_gt_mul_expect_le`. The general form is
  `one_sub_inv_le_prob_le_mul_expect` (c > 0).
- **(b)** "for X₁,X₂≥0, P(X₁≤4EX₁ and X₂≤4EX₂)≥1/2": `half_le_prob_le_four_mul_expect_and`.
  Identical. The general form is `one_sub_inv_sub_inv_le_prob_and`.
- **(c)**, first clause, "given any event of positive probability": (a) and (b) apply directly to
  `μ.cond A hA`, since they are stated for an arbitrary FinDist. The two unfolded forms
  `two_thirds_mul_prob_le_prob_inter_cond` (`2/3·P(A) ≤ P(A ∩ {X ≤ 3E[X|A]})`) and
  `half_mul_prob_le_prob_inter_cond` are equivalent to "P(· | A) ≥ 2/3 (resp. 1/2)" because
  P(A) > 0. `expect_cond` / `prob_cond` identify E[X|A] = E[X·1_A]/P(A) and
  P(B|A) = P(B∩A)/P(A).
- **(c)**, second clause, "given any fixed outcome of variables that are independent of the
  variables being drawn … the conditional law of the latter is their unconditional law":
  `cond_prod_fst` (conditioning μ⊗ν on the first coordinate a gives dirac a ⊗ ν) and
  `map_snd_cond_prod_fst` (the second coordinate then has law ν). For finite products,
  `prob_pi_split` / `pi_eq_map_prod` fix any set of coordinates. For the two-stage (dependent)
  case, `prob_compProd`, `exists_le_prob_section`, `prob_compProd_le_of_forall` and
  `le_prob_compProd_of_forall` give Fubini and "fix a good prefix".
- **Task items**:
  - union bound: `prob_union_le`, `prob_biUnion_le`, `prob_iUnion_le`,
    `exists_forall_notMem_of_sum_lt_one`;
  - complement: `prob_compl` (P(Aᶜ) = 1 − P(A));
  - monotonicity: `prob_mono`, `prob_mono_ae`, `expect_mono(_ae)`;
  - existence: `exists_of_prob_pos` (P(A) > 0 → ∃ ω ∈ A with w ω > 0) and `exists_le_expect`
    (∃ ω with w ω > 0 and X ω ≤ E X), both exactly as asked;
  - linearity: `expect_add`, `expect_const_mul`, `expect_sum`, …;
  - product event: `prob_prod_set_prod`;
  - function of one coordinate: `expect_prod_fst/snd`, `expect_pi_eval`, `prob_pi_eval`;
  - Fubini: `expect_prod`, `expect_prod_swap`, `expect_compProd`;
  - independence: `expect_prod_mul`, `expect_pi_prod(_finset)`, `prob_pi_forall_mem`,
    `expect_pi_mul_of_dependsOn`, `prob_pi_inter_of_dependsOn`;
  - prefix conditioning: `prob_prod_eq_sum : P(A) = ∑_a w(a)·P_ν(A_a)`, exactly the task
    formula. `[Fintype α]` is needed only to write ∑_a. The Fintype-free form is `prob_prod`.

  All of these are present with no extra hypotheses.
- **Random-subset characterisations**:
  - `prob_mem_rsubset` (P(a ∈ T) = ρ);
  - `prob_superset_rsubset` (ρ^{\|A\|});
  - `prob_disjoint_rsubset` ((1−ρ)^{\|B\|});
  - `expect_card_rsubset` (E\|T\| = ρ\|S\|);
  - `map_colourClass_randColouring`: a colour class is a (1/k)-random subset, which is the
    "X_i" of L15⁺.

  All are correct. The side conditions (A, B ⊆ S, A ∩ B = ∅) are the natural ones.

**Bridge**: not applicable. This task touches neither `EGCheck/Bridge.lean` nor
`EG.Spec.MainInternal`.

## 2. Vacuity / triviality

The probes are in a scratch file outside the repository
(`/tmp/claude-0/.../scratchpad/Vac.lean`), which imports `EG.Lib.Prob.Named`. They compile with
0 errors:
1. `dirac true ≠ dirac false`, so `FinDist Bool` is not a subsingleton.
2. `(bernoulli (1/3)).prob {true} ≠ (bernoulli (2/3)).prob {true}`, so `prob` is not degenerate.
3. Markov is tight for an indicator: P(X ≥ 1) = E X / 1.
4. For S = {0,1} and ρ = 1/3: `(rsubset S ρ).w S = 1/9` and `.w ∅ = 4/9`. With `2/9` for {0}
   (the author's test), the total is 1/9 + 2·2/9 + 4/9 = 1, the genuine product law.
5. `rsubset S ρ a c = rsubset S ρ b d` by `rfl` (no dependence on the proofs).
6. `FinDist Empty → False`. A distribution forces a nonempty sample space
   (`FinDist.nonempty`), so no statement "∀ μ : FinDist Ω, …" can be vacuous on an empty Ω by
   accident, and none is trivially satisfied either.
7. The conclusion of Markov (a) is not trivially 1. With X = 4·1_{true} under Bernoulli(1/5),
   P(X ≤ 3EX) = 4/5 exactly.
8. `indepSubset` with element-dependent p (1/2 and 1/3): P({0,1} ⊆ T) = 1/6.
9. Usability probes (issues 1 and 3) also go through: `map_pi_coord` and the colour class as a
   subset of E.

I could not derive `False` or any unexpected equality. The structure invariants (w ≥ 0, a finite
support set, sum = 1) are consistent, since `dirac`, `bernoulli` and `uniform` inhabit them, and
they are not contradictory.

## 3. Soundness hygiene
- `python3 scripts/lint.py`: `lint (development): 0 findings`.
- `lake env lean --run scripts/Axioms.lean --prefix EG EG.Lib.Prob.Named`: `inspected 302
  constants under [EG]; 0 use sorryAx; 0 violations`. This covers FinDist, Basic and Named.
- `scripts/check.sh EG/Lib/Prob/Named.lean` and `scripts/check.sh EGTest/Prob.lean`: rc=0,
  0 errors, 0 sorry warnings. The oleans of FinDist and Basic were newer than their sources.
- Module headers follow AGENTS.md: `@[expose] public section` in the Defs file and
  `public section` in both Lib files. The Lib files contain no defs, so nothing needs `@[expose]`.
  EGTest/Prob.lean is a plain file. The Defs file carries the PROTECTED FILE banner like
  Objects.lean. There is no `sorry`, `native_decide` or other forbidden token. `decide` is used
  only on tiny `Finset ℕ` / `Fin 6` facts in the tests.
- The files are 259, 1030, 371 and 173 lines, all below 1500.

## 4. Usability (downstream: Chernoff, s3–s7)
The API is clean and general. Events are `Set Ω`, and there are no `DecidablePred` arguments
except where a `filter` is formed. Almost-sure hypotheses are uniformly written `0 < μ.w ω → …`.
Existence principles return outcomes of positive weight. The `pi`/`prod`/`compProd`/`map`
layer is enough to express "fix a prefix" in both the independent and the dependent form. The
issues below are additions I recommend before the probability-heavy files (s3 L15⁺/T16*, s4
TPV, s5 zones) start. None changes existing statements.

Issues are listed in the structured verdict:
1. **(minor) Coordinatewise map of a product.** Add `map_pi`:
   `(pi μ).map (fun ω i => f i (ω i)) = pi fun i => (μ i).map (f i)`, and `map_prod_map`:
   `(μ.prod ν).map (Prod.map f g) = (μ.map f).prod (ν.map g)`. Together with `map_map` these are
   the standard way to show that "a set defined vertex-by-vertex from independent labels is a
   ρ-random subset". Uses: s5.tex l. 67 ("The event {v∈Zone} is a function of the pair
   (choice(v), sublabel of v), and these pairs are independent over v. So Zone contains each
   vertex of Y independently with probability exactly ρ_Y"), the s4 l. 176 thinning, and
   L15⁺'s colour classes. I proved `map_pi` in 6 lines in scratch:
   ```lean
   ext g; rw [map_w, pi_w]; simp only [map_w]
   have : (fun ω i => f i (ω i)) ⁻¹' {g} = {ω | ∀ i ∈ univ, ω i ∈ f i ⁻¹' {g i}} := by
     ext ω; simp [funext_iff]
   rw [this, prob_pi_forall_mem]
   ```
2. **(minor) Mutual independence of many blocks.** `prob_pi_inter_of_dependsOn` and
   `expect_pi_mul_of_dependsOn` handle two complementary blocks of coordinates. Chernoff
   applications need a finite family. Example: s4 (G4), "the variables I_u (u∈A_w(w)) depend
   on pairwise distinct edges wu and distinct vertices u, so they are independent", after which
   Chernoff (B) is applied. Suggest a law-level lemma: if `g u` depends only on the coordinates
   in `B u` and the `B u` are pairwise disjoint, then
   `(pi μ).map (fun ω u => g u ω) = pi fun u => (pi μ).map (g u)`. It can be proved by
   induction from `pi_eq_map_prod` / `expect_pi_prod`. The Chernoff task can then assume
   `pi` of Bernoullis without further transport.
3. **(minor) Colour class as a subset of the ambient type.** `map_colourClass_randColouring`
   produces a random `Finset ι`, that is `Finset ↥E` for edges. The graph X_i of L15⁺ has edge
   set a `Finset (Sym2 V)` ⊆ E. Suggest adding the ambient form
   `(randColouring ↥E k).map (fun c => selectSet E fun e => decide (c e = j)) = rsubset E (1/k) _ _`.
   Using issue 1 and the one-coordinate lemma `(uniform (Fin k)).map (· = j) = bernoulli (1/k)`,
   it took about 20 lines in scratch.
4. **(minor) A shared vocabulary for "V is a ρ-random subset" and "independent of".** Downstream
   statements (T16*, COL(c), s5 zones) say "let V be a ρ-random subset … independent of the
   colouring". Suggest documenting one idiom in Basic.lean's header, and optionally adding
   abbrevs in `EG/Lib/Prob` so that all files state these the same way. The idiom:
   "`V : Ω → Finset α` is ρ-random" is `μ.map V = rsubset S ρ _ _`, and "X, Y independent" is
   `μ.map (fun ω => (X ω, Y ω)) = (μ.map X).prod (μ.map Y)`. Otherwise every file invents its
   own formulation, and the transport lemmas multiply.
5. **(cosmetic) Name clashes.** `EG.FinDist.map_map` clashes with `Finset.map_map` when both
   `EG.FinDist` and `Finset` are open, which is what EGTest/Prob.lean opens. I hit this in
   scratch: "Ambiguous term map_map". Similarly, `EG.FinDist.cond` shadows `_root_.cond` inside
   the namespace. It is harmless, since users can qualify. It could be mentioned in the header.
6. **(cosmetic) Test docstring.** In EGTest/Prob.lean, "Fubini in both orders agree on an
   explicit function" is proved with `expect_prod` only (one order). Either add the
   `expect_prod_swap` computation or reword the docstring.
7. **(cosmetic) Markov hypotheses are pointwise.** `hX : ∀ ω, 0 ≤ X ω` matches the manuscript's
   "X ≥ 0". An `_ae` variant (`∀ ω, 0 < μ.w ω → 0 ≤ X ω`) would help when X is only known to be
   nonnegative on the support, for example after conditioning. It is low priority, because
   `expect_congr` / `prob_congr` let the user replace X by `max X 0`.

Integrator notes: the modules to add to the roots are `EG.Defs.Prob.FinDist`, `EG.Lib.Prob.Basic`,
`EG.Lib.Prob.Named` (EG.lean) and `EGTest.Prob` (EGTest.lean). Record the "no Fintype in the
type" deviation in STATE.md.
