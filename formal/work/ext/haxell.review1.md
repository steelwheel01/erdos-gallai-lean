# [haxell] clean-room review, round 1

Reviewed: `EG/Spec/Ext/Haxell.lean` (83 lines), `EG/Proof/Ext/Haxell.lean` (664 lines), author notes
`work/ext/haxell.md`, against s1.tex l.1301-1470 (s1:citHaxell, its derivation, "Proof of the stated form") and
s3.tex l.708-800 (s3:lemL9rho, claim and application).

**Verdict: APPROVE.** No major or minor defect found. Two cosmetic suggestions at the end.

## 1. Hygiene (re-run by the reviewer)
- `lake build EG.Proof.Ext.Haxell`: success (965 jobs), no errors.
- `python3 scripts/lint.py`: 0 findings.
- `lake env lean --run scripts/Axioms.lean --prefix EG EG.Proof.Ext.Haxell`: 114 constants, 0 `sorryAx`, 0 meta-scan hits,
  0 violations. `#print axioms EG.haxell` / `EG.haxell_stated`: `[propext, Classical.choice, Quot.sound]` only.
- No `sorry`, no `set_option`. Module headers follow AGENTS.md (`@[expose] public section` in Spec, `public section` in
  Proof). The Spec imports only Mathlib. Root files not edited.

## 2. Fidelity of the Spec
Manuscript s1:citHaxell: "Let q≥1 be an integer, and let 𝓗 be a hypergraph (a set of subsets, called edges, of a finite
vertex set) whose vertex set is the disjoint union of two sets 𝓧 and 𝓨, such that every edge e satisfies |e∩𝓧|=1 and
|e∩𝓨|≤q. Suppose that for every 𝓧'⊆𝓧 and every Z⊆𝓨 with |Z|≤(2q−1)(|𝓧'|−1) there is an edge e of 𝓗 with e∩𝓧⊆𝓧' and
e∩Z=∅. Then 𝓗 has an 𝓧-saturating matching, i.e. a set of pairwise disjoint edges such that every vertex of 𝓧 lies in one
of them."

| Manuscript | `HaxellStatedForm` | check |
|---|---|---|
| q ≥ 1 integer | `q : ℕ`, `1 ≤ q` | ok |
| vertex set = 𝓧 ⊔ 𝓨, finite | `X Y : Finset α`, `Disjoint X Y`, `∀ e ∈ H, e ⊆ X ∪ Y` | ok (the last one is needed: otherwise edges could meet outside X∪Y) |
| hypergraph = set of subsets | `H : Finset (Finset α)` | ok |
| \|e∩𝓧\| = 1, \|e∩𝓨\| ≤ q | `(e ∩ X).card = 1`, `(e ∩ Y).card ≤ q` | ok |
| ∀𝓧'⊆𝓧, ∀Z⊆𝓨, \|Z\| ≤ (2q−1)(\|𝓧'\|−1) | same, compared in ℤ | ok; ℤ avoids HAX-NATSUB, matching the manuscript remark "For 𝓧'=∅ there is no such Z" |
| e∩𝓧⊆𝓧', e∩Z=∅ | `e ∩ X ⊆ X'`, `Disjoint e Z` | ok |
| set of pairwise disjoint edges covering 𝓧 | `M ⊆ H`, `(M : Set _).PairwiseDisjoint id`, `∀ a ∈ X, ∃ e ∈ M, a ∈ e` | ok |

`HaxellStatement` (the form to lock, TRIAGE "q²-form (nonempty X', |Z| < q²|X'|)"): identical data and conclusion, hypothesis
`∀ X' ⊆ X, X'.Nonempty → ∀ Z ⊆ Y, Z.card < q ^ 2 * X'.card → ∃ e ∈ H, e ∩ X ⊆ X' ∧ Disjoint e Z` (all in ℕ, no
subtraction). This is exactly the claim of s3:lemL9rho: "for every nonempty I⊆[r] and every F⊆E(G) with |F|<h²|I|, there
are j∈I and P∈𝓨_j with E(P)∩F=∅", with q = h, 𝓧 = [r], 𝓨 = E(G); and the manuscript's own remark "The claim covers every Z
with |Z|<h²|I|". Relation (checked by hand and in Lean, `EG.haxellStatement_of_statedForm`): for nonempty 𝓧',
q²|𝓧'| − (2q−1)(|𝓧'|−1) = (q−1)²|𝓧'| + 2q − 1 > 0, and for 𝓧' = ∅ the stated hypothesis is vacuous in ℤ; so the q²-form
is a consequence of the stated form, and its hypothesis is (strictly) stronger. Not a weakening of what L9ρ needs: the
conclusion is the same and the hypothesis is the one L9ρ verifies.

Edge cases: `X = ∅` (conclusion trivially true with `M = ∅`), `Y = ∅`, `q = 1` (Hall), arbitrary `DecidableEq` instance,
universe-polymorphic `α : Type u` (the proof is `HaxellStatement.{u}` for every `u`; checked `.{0}` and `.{3}`).

## 3. Non-vacuity (scratch file `$SCRATCH/HaxTest.lean`, compiled with `lake env lean`, all pass)
1. `EG.haxell` applied to a concrete instance (q = 1, X = {0,1}, Y = {10,11,12}, H = {{0,10},{0,11},{1,10}}) whose
   q²-hypothesis is proved by `decide` over powersets: yields a matching.
2. `EG.haxell_stated` applied to a q = 2 instance (14 three-element edges, hypothesis `|Z| ≤ 3(|X'|−1)` in ℤ proved by
   `decide`): yields a matching.
3. The hypothesis is not trivially satisfiable: for H = ∅, X = {0} it fails (X' = X, Z = ∅).
4. HAX-NATSUB: for every q ≥ 1 no Z satisfies the ℤ bound at X' = ∅.
5. Content check: H = {{0,10},{1,10}}, X = {0,1} has no X-saturating matching, and the q²-hypothesis fails there
   (X' = {0,1}, Z = {10}, 1 < 2), consistent with the theorem.
6. Application shape of s3:lemL9rho: `EG.haxell` instantiated on `ι ⊕ E` with X = `I.image Sum.inl`,
   Y = `EG'.image Sum.inr` and the claim as hypothesis type-checks (disjointness discharged directly).

## 4. The proof proves exactly the Spec
`theorem haxell : EG.Spec.HaxellStatement.{u}` and `theorem haxell_stated : EG.Spec.HaxellStatedForm.{u}`, with the
Spec definitions imported unchanged (no local restatement). `haxell_nat` (internal ℕ form, nonempty X', bound
`(2q−1)(|X'|−1)` in ℕ) is used only for nonempty X', where the ℕ and ℤ bounds agree (`omega` casts), so no ℕ-subtraction
trap enters.

## 5. Manuscript proof ("Proof of the stated form") — checked, no gap
- Induction on |𝓧| with the restriction to edges avoiding a₀: correct (hypothesis inherited since e∩𝓧⊆𝓧'∌a₀).
- Disjointness of the 𝓢_i and |𝓧^{(k)}|−1 = Σ|𝓢_i| ≤ |𝓧|−1: correct (the Lean `inv_J` invariant formalizes
  "m∈𝓢_j ⇒ m∩𝓨⊆Z^{(i−1)}").
- Counting |Z^{(k)}| ≤ Σ(q + (q−1)|𝓢_i|) ≤ (2q−1)Σ|𝓢_i|: correct, uses |𝓢_i| ≥ 1 and that each m∈𝓢_i meets x_i in 𝓨.
- Swap step: M' good (incl. the degenerate y = m case, which is impossible since m∩x_i∩𝓨 ≠ ∅ = y∩x_i∩𝓨); the 𝓢_{i'}
  for i' < i unchanged and 𝓢_i ↦ 𝓢_i∖{m}; recursion with j := i−1, y := x_i: correct.
- Termination via σ∞ lex order: correct; the Lean proof replaces iteration by choosing a configuration of maximal
  key (key entries |H| − s in `Fin (|H|+1)`, lengths ≤ |𝓧|), which is the same order reversed. Formally verified.

## 6. Suggestions (cosmetic, non-blocking)
- C1: Add a committed non-vacuity test in `EGTest/` (e.g. tests 1 and 6 above), as the blueprint (EUL-EMPTY note)
  recommends for every stage-α Prop; integrator-owned.
- C2: The docstring of `HaxellStatement` paraphrases rather than quotes; consider quoting the L9ρ claim sentence
  ("for every nonempty I⊆[r] and every F⊆E(G) with |F|<h²|I| ...") there as well as in the module docstring.

TRIAGE HAX-TRUTH can be closed as the author says: `HaxellStatement` is now a theorem (`EG.haxell`), not a trusted
hypothesis. The manuscript's remaining caveat (factor 2q−1 unchecked against [Hax95]) no longer matters for this
project, since the stated form is itself proved.
