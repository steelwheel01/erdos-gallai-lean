# Clean-room review, round 2: task [findist] (FinDist: finite probability spaces with real weights)

Reviewer: clean-room agent (round 2). I edited no Lean file. Scratch checks were done outside the
repository, in the session scratchpad (`Vac2.lean`, `Print2.lean`, `Use2.lean`), each importing
`EG.Lib.Prob.Indep`.

**Verdict: APPROVE.** I found no defects in fidelity, vacuity or soundness.
- Every round-1 item was handled correctly, and the fix round changed no existing statement. I
  checked the Defs diff myself with a read-only `git diff`.
- The three new Defs predicates (`IndepFun`, `iIndepFun`, `IsRSubset`) are the textbook
  definitions. They are faithful to the manuscript and not vacuous.
- The remaining items are cosmetic or optional, plus two notes for the integrator.

Files reviewed (current working tree, after fix round 1):
- `EG/Defs/Prob/FinDist.lean` (309 lines)
- `EG/Lib/Prob/Basic.lean` (1229)
- `EG/Lib/Prob/Named.lean` (456)
- `EG/Lib/Prob/Indep.lean` (329, new)
- `EGTest/Prob.lean` (285)
- `work/p1b/findist.md` and `work/p1b/findist.review1.md`

Manuscript passages compared:
- s1.tex 819–842: s1:citMarkov, statement and derivation
- s1.tex 784–797: s1:citChernoffGen, "sum of independent indicator variables"
- s1.tex 617: s1:citThm16
- s3.tex 27–31: the ρ-random subset convention
- s3.tex 100–110: s3:lemL15p
- s3.tex 966–1024: s3:defCOL, "colours of distinct edges are independent … the labels are
  independent of the colours … T_j(Y,l) is a ρ_l-random subset …, independent of the colouring"
- s4.tex 170–190: thinning, and (G4) "the variables I_u … depend on pairwise distinct edges wu and
  distinct vertices u, so they are independent"
- s5.tex 63–68 and 134: zones, "these pairs are independent over v. So Zone contains each vertex
  of Y independently with probability exactly ρ_Y", and "independently of the colouring of Y"

## 1. Fidelity: back-translation

### Definitions that are unchanged since round 1
I re-read `FinDist`, `supp`, `prob`, `expect`, `ofFinset`, `ofFintype`, `dirac`, `compProd`,
`prod`, `pi`, `map`, `bind`, `uniform`, `bernoulli`, `cond`, `selectSet`, `indepSubset`, `rsubset`
and `randColouring`. The round-1 back-translation table is still accurate. The one change is that
`cond` is now `protected`. That is an attribute change: the body and signature are identical.

In plain mathematics, `FinDist Ω` is a finitely supported probability mass function w ≥ 0 with
Σ w = 1. Then:
- `prob A` = Σ_{ω∈A} w(ω) and `expect X` = Σ w(ω) X(ω);
- `pi` is the independent product ∏_i μ_i(f i), and `map` is the law of f;
- `uniform` has weight 1/|Ω|, `bernoulli p` puts p on true and 1−p on false, and `cond A` is
  1_A w / P(A);
- `rsubset S ρ` is "a random subset of S that contains each element of S independently with
  probability ρ" (s3.tex l. 29–31, quoted in the docstring);
- `randColouring ι k` is "Give every edge of X a colour from [k], independently and uniformly at
  random" (s3:lemL15p, quoted), with Fin k in place of [k] and k ≥ 1 given by `NeZero`.

### New definitions (fix round 1, `EG/Defs/Prob/FinDist.lean`)
I read them with `#print` as well as in the source.

| Lean | Plain mathematics | Manuscript | Match |
|---|---|---|---|
| `IndepFun μ X Y` | For all A ⊆ γ and B ⊆ δ, P(X∈A ∧ Y∈B) = P(X∈A)·P(Y∈B). | s3:defCOL "the labels are independent of the colours"; s1:citMarkov(c) "variables that are independent of the variables being drawn"; s5 l. 134 "independently of the colouring of Y" | Yes. This is the textbook definition of independence of two random variables. On a finitely supported space every set is an event, so there is no measurability gap. |
| `iIndepFun μ X` (dependent value types `β u`) | For every finite set s of indices and all events A_u, P(∀u∈s, X_u∈A_u) = ∏_{u∈s} P(X_u∈A_u). | s1:citChernoffGen "a sum of independent indicator variables"; s3:defCOL "colours of distinct edges are independent" | Yes. This is the textbook mutual independence, stated on finite subfamilies. Probe C shows that it is strictly stronger than pairwise independence. |
| `IsRSubset μ V S ρ` | ρ∈[0,1], and the law of V is the ρ-random subset of S. | s3 "For ρ∈[0,1], a ρ-random subset of a finite set S is a random subset of S that contains each element of S independently with probability ρ." (quoted) | Yes. `isRSubset_iff` proves the literal elementwise reading as an iff: ρ∈[0,1], V ⊆ S a.s., the indicators 1[a∈V] (a∈S) are `iIndepFun`, and P(a∈V) = ρ. The condition ρ∈[0,1] belongs to the manuscript's own definition ("For ρ∈[0,1]"), so it is not an extra hypothesis. |

Edge cases:
- S = ∅: V = ∅ almost surely, for every ρ∈[0,1] (probe E).
- ρ = 1: V ⊇ S almost surely (probe F).
- ρ ∉ [0,1]: `IsRSubset` is false (probe D').
- Empty index set in `iIndepFun`: the condition reads P(Ω) = 1 = empty product, which is correct.

### New and changed statements (Basic / Named / Indep)
- **Markov, `_ae` variants.** Each variant replaces "X ≥ 0" by "X ≥ 0 on outcomes of positive
  weight". That hypothesis is weaker, so each variant is stronger than the manuscript statement.
  The pointwise lemmas keep their exact round-1 statements and are one-line corollaries.
  - `prob_le_expect_div`: "If X≥0 and a>0 then P(X≥a)≤EX/a", with non-strict ≥ a. Identical.
  - (a) `two_thirds_le_prob_le_three_mul_expect`: 2/3 ≤ P(X ≤ 3EX). Identical.
  - (b) `half_le_prob_le_four_mul_expect_and`: 1/2 ≤ P(X₁ ≤ 4EX₁ ∧ X₂ ≤ 4EX₂). Identical.
  - (c) The conditional `_ae` forms assume X ≥ 0 only on the positive-weight outcomes of A. That
    is exactly "X ≥ 0 in the conditional space".
- **Markov (c), second clause: `IndepFun.map_cond`.** If X ⫫ Y, then conditioned on X = x
  (P > 0) the law of Y is its unconditional law. This is the general form of "if the
  conditioning fixes variables independent of those being drawn, the conditional law of the
  latter is their unconditional law" (s1.tex l. 839–841).
- **Law forms.**
  - `indepFun_iff_map_eq_prod`: X ⫫ Y ⇔ law(X,Y) = law X ⊗ law Y.
  - `iIndepFun_iff_map_eq_pi` (Fintype index): law((X_u)_u) = ⊗_u law X_u.
  - `iIndepFun.map_eq_pi_subtype`: the same for any finite subfamily.

  All three are correct equivalences with no extra hypotheses.
- **Mutual independence of blocks.**
  - `prob_pi_forall_of_dependsOn`, `expect_pi_prod_of_dependsOn`, `map_pi_of_dependsOn` and
    `iIndepFun_pi_of_dependsOn` all say: if g_u depends only on the coordinates in B_u, and the
    B_u are pairwise disjoint, then the g_u are mutually independent.
  - This matches s4 (G4) "depend on pairwise distinct edges wu and distinct vertices u, so they
    are independent".
  - The Finset forms need disjointness only inside s, which is more general.
- **Coordinatewise maps.** `map_pi` gives (⊗μ_i)∘(f_i)⁻¹ = ⊗(μ_i∘f_i⁻¹), and `map_prod_map` is
  the two-factor version. Both are correct.
- **Sets selected from independent labels.**
  - `map_selectSet_pi` / `map_selectSet_pi_rsubset`: select a iff f_a(ω_a) holds, where each
    f_a(ω_a) is Bernoulli(p_a). The selected set is then `indepSubset S p` (resp. `rsubset`).
    This is exactly the s5 l. 67 argument (quoted in the docstring).
  - `isRSubset_selectSet` is the same fact for `iIndepFun` indicators on an arbitrary space.
- **Colour class in the ambient type.** `map_selectSet_randColouring`: for a uniform
  k-colouring of E, {e∈E : c e = j} is a (1/k)-random subset of E. This is "X_i" of L15⁺.
- **Transport lemmas.** `indepFun_map_iff`, `iIndepFun_map_iff` and `isRSubset_map_iff` all hold
  by `rfl` after `prob_map` / `map_map`, and they are correct.

The docstring quotes match the manuscript text, which I checked at each cited line. Line numbers
drift by at most one line: s4 (G4) is at l. 188–189, while the docstrings cite l. 189 and l. 190.

**Bridge:** not applicable. This task touches neither `EGCheck/Bridge.lean` nor
`EG.Proof.mainInternal`.

## 2. Vacuity / triviality

I made new probes for the new predicates in `Vac2.lean` (scratchpad). The file compiles with rc=0,
0 errors and 0 warnings.

| Probe | What it shows |
|---|---|
| A. `¬ (uniform Bool).IndepFun id id` | `IndepFun` is not trivially true: a fair coin is not independent of itself (1/2 ≠ 1/4). |
| B. `(uniform Bool).IndepFun (fun _ => ()) id` | `IndepFun` is satisfiable: constants are independent. |
| C. With two fair coins x, y and X = (x, y, x xor y): `¬ μ2.iIndepFun X`, but `μ2.IndepFun (X 0) (X 2)` | `iIndepFun` is genuinely mutual, not pairwise (P(all true) = 0 ≠ 1/8). |
| D. `¬ (dirac {0}).IsRSubset id {0,1} (1/2)`; D'. `¬ μ.IsRSubset V S 2` | `IsRSubset` is not trivially satisfiable. |
| E. `(dirac ∅).IsRSubset id ∅ ρ` for all ρ∈[0,1] | the degenerate S = ∅ case is correct |
| F. `IsRSubset V S 1` ⇒ P(S ⊆ V) = 1 | the ρ = 1 edge case is correct |
| G. `bernoulli (1/3) ≠ bernoulli (2/3)` | the structure is not degenerate |
| H. `@pi ι i1 κ μ = @pi ι i2 κ μ` for any two `Fintype` instances | Instance dependence of `pi` is harmless: `congr` plus `Subsingleton.elim` closes it. |

I found no way to derive `False`. The round-1 probes (`FinDist Empty → False`, Markov tight on an
indicator, the rsubset weights summing to 1, element-dependent `indepSubset`) still apply because
those definitions are unchanged.

## 3. Soundness hygiene
- `python3 scripts/lint.py`: `lint (development): 0 findings`.
- `lake env lean --run scripts/Axioms.lean --prefix EG EG.Lib.Prob.Indep`: `inspected 387 constants
  under [EG]; 0 use sorryAx; 0 violations`. This covers FinDist, Basic, Named and Indep.
  `#print axioms` for `isRSubset_iff` and `map_pi_of_dependsOn` gives `[propext, Classical.choice,
  Quot.sound]`.
- `scripts/check.sh` with `LEAN_NUM_THREADS=2` on each of `EG/Defs/Prob/FinDist.lean`,
  `EG/Lib/Prob/Basic.lean`, `EG/Lib/Prob/Named.lean`, `EG/Lib/Prob/Indep.lean` and
  `EGTest/Prob.lean` gives rc=0, 0 errors and 0 sorry warnings. The oleans were newer than their
  sources.
- Headers:
  - The Defs file is `@[expose] public section` and keeps the PROTECTED FILE banner.
  - The Lib files are `public section`. They contain no new defs, so no `@[expose]` is needed.
  - `EGTest/Prob.lean` is a plain file.
- There is no `sorry` or forbidden token. All files are under 1500 lines.
- Name hygiene: with `open EG EG.FinDist Finset Set Function`, `map_map` resolves to
  `Finset.map_map` and `cond true 1 2` resolves to `Bool.cond`. So the `protected` fix works.
- `git diff` (read-only) of `EG/Defs/Prob/FinDist.lean` against HEAD shows only three things:
  the three new predicates, `protected` on `cond`, and docstring text. This agrees with the
  author's note.

## 4. Usability

The vocabulary layer is what the probabilistic files (s3 COL / L15⁺ / T16*, s4 TPV, s5 zones,
Chernoff) need. Downstream statements can now say "V is a ρ-random subset of S, independent of the
colouring c" as `μ.IsRSubset V S ρ ∧ μ.IndepFun c V`. I checked in `Use2.lean` that the two
consequences the manuscript uses are one-liners:
- conditioning on a value of the colouring keeps V ρ-random:
  `⟨hV.nonneg, hV.le_one, (hi.map_cond x hx).trans hV.map_eq⟩`;
- the joint law is law(c, V) = law(c) ⊗ rsubset S ρ, by
  `rw [(indepFun_iff_map_eq_prod μ).1 hi, hV.map_eq]`.

There is no transport pain, and the `_ae` Markov variants remove the `max X 0` workaround.

Minor items (optional, non-blocking), also in the structured verdict:
1. **(cosmetic) Line-number citations.** Some docstrings cite manuscript line numbers: s4.tex
   l. 189 / l. 190, s5.tex l. 67 / l. 134 and s3.tex l. 1015 / l. 1017. These will drift under v6.
   Where a label exists, cite it as well, e.g. "[s4:lemTPV] proof, (G4)", "[s5:lemZones] proof"
   or "[s3:defCOL]".
2. **(optional) Two convenience lemmas in `Indep.lean`**, since they are the pattern s5 (c) and
   s3:lemCOL(c) use:
   - `IsRSubset.cond_of_indepFun`: conditioning on `c = x` preserves `IsRSubset V S ρ` when
     `IndepFun c V`;
   - `IsRSubset.map_pair_eq_prod`: the joint law of (c, V).

   Each is a one-liner (see above), so this is only for discoverability.
3. **(integrator) Record the deviation.** The deviation "`FinDist Ω` carries no `[Fintype Ω]`"
   (task text: "FinDist Ω for [Fintype Ω]") is still not recorded in STATE.md. Round 1 endorsed
   it, and I endorse it again: the type is more general and has no instance diamonds.
4. **(integrator) Approval record.** `EG/Defs/Prob/FinDist.lean` gained three Defs predicates in
   fix round 1. Per `APPROVALS/README.md`, they need an approval record with two independent
   clean-room reviews and the back-translation. This review is one of them: the table in §1 gives
   the back-translation of `IndepFun`, `iIndepFun` and `IsRSubset`.
5. **(later task, not a defect) Unions of independent random subsets.** s3.tex l. 245–253: "If
   V_1,…,V_ℓ are independent random subsets … V_1∪…∪V_ℓ is a ρ-random subset". This belongs in
   the planned `RandomSets` file. The ingredients (`iIndepFun`, `isRSubset_selectSet`,
   `map_pi_of_dependsOn`) are all present.

Modules to add to the roots (integrator): `EG.Defs.Prob.FinDist`, `EG.Lib.Prob.Basic`,
`EG.Lib.Prob.Named` and `EG.Lib.Prob.Indep` in `EG.lean`, and `EGTest.Prob` in `EGTest.lean`.
