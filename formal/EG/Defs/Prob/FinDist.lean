module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.BigOperators.Group.Finset.Indicator
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Group.Indicator
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Finite probability distributions with real weights (`EG.FinDist`)

PROTECTED FILE (`EG/Defs/**`): changes need the approval procedure in `APPROVALS/README.md`.

PLAN_FORMALIZATION.md §3, design decision 3: randomness is a custom finite layer, not Mathlib
measure theory. Every random object of the manuscript is a finite family of independent labels
with real parameters; every conclusion drawn from randomness is a deterministic existence
statement (from a positive probability, or from Markov's inequality); "conditioning" is fixing a
prefix of the coordinates, i.e. Fubini over finite sums.

## Contents

* `FinDist Ω`: a probability distribution on `Ω` given by real weights `w : Ω → ℝ` that are
  nonnegative, vanish outside a finite set and sum to `1`. The type does not depend on any
  `Fintype`/`DecidableEq` instance (so no instance diamonds can make two `FinDist Ω` types differ);
  on a `Fintype Ω` the condition is just `∑ ω, w ω = 1` (`FinDist.ofFintype`, `FinDist.sum_w`).
* `μ.supp`: the (finite) set of outcomes of nonzero weight.
* `μ.prob A`: probability of an event `A : Set Ω`; `μ.expect X`: expectation of `X : Ω → ℝ`.
  Both are finite sums over `μ.supp` and need no instances.
* constructions: point mass `dirac`, the two-step product `compProd` (first coordinate from `μ`,
  second from a kernel `K a` depending on the first: this is the "fix a prefix" structure),
  independent product `prod`, finite product `pi` over a `Fintype` index, pushforward `map`,
  `bind`, uniform distribution `uniform`, `bernoulli p` on `Bool`, conditioning `cond` on an event
  of positive probability, independent random subsets `indepSubset` / `rsubset` (the ρ-random
  subsets of s3) and uniform random colourings `randColouring` (s3:lemL15p).
* shared vocabulary for random variables `X : Ω → γ`: independence `IndepFun`, mutual
  independence `iIndepFun`, and "`V` is a ρ-random subset of `S`" `IsRSubset`.

The API (union bound, Markov [s1:citMarkov], existence principles, Fubini, independence) is in
`EG/Lib/Prob/Basic.lean`; the named distributions are treated in `EG/Lib/Prob/Named.lean`, and
the vocabulary predicates in `EG/Lib/Prob/Indep.lean`.
-/

@[expose] public section


namespace EG

open Finset

/-- A finitely supported probability distribution on `Ω` with real weights: the weight `w ω` is
the probability of the outcome `ω`. The weights are nonnegative, vanish outside some finite set
`s`, and sum to `1` over `s`.

This is the sample-space layer of PLAN §3, decision 3 (finite families of independent labels with
real parameters). No `Fintype Ω` instance is part of the type; on a `Fintype` the last condition
is equivalent to `∑ ω, w ω = 1` (`FinDist.ofFintype`, `FinDist.sum_w`). -/
@[ext]
structure FinDist (Ω : Type*) where
  /-- The weight (probability) of each outcome. -/
  w : Ω → ℝ
  /-- Weights are nonnegative. -/
  w_nonneg : ∀ ω, 0 ≤ w ω
  /-- The weights vanish outside a finite set and sum to `1` over it. -/
  exists_finset : ∃ s : Finset Ω, (∀ ω ∉ s, w ω = 0) ∧ ∑ ω ∈ s, w ω = 1

namespace FinDist

variable {Ω α β : Type*}

/-- The set of outcomes of nonzero weight is finite. -/
theorem finite_support (μ : FinDist Ω) : (Function.support μ.w).Finite := by
  obtain ⟨s, hs, -⟩ := μ.exists_finset
  refine s.finite_toSet.subset fun ω hω => ?_
  by_contra h
  exact hω (hs ω h)

/-- The support of `μ`: the finite set of outcomes of nonzero (equivalently, positive) weight. -/
noncomputable def supp (μ : FinDist Ω) : Finset Ω :=
  μ.finite_support.toFinset

theorem mem_supp {μ : FinDist Ω} {ω : Ω} : ω ∈ μ.supp ↔ μ.w ω ≠ 0 := by
  simp [supp]

/-- The support is contained in every finite set outside of which the weights vanish. -/
theorem supp_subset {μ : FinDist Ω} {s : Finset Ω} (hs : ∀ ω ∉ s, μ.w ω = 0) : μ.supp ⊆ s :=
  fun ω h => by_contra fun h' => mem_supp.1 h (hs ω h')

/-- A sum over the support can be taken over any larger finite set, provided the summand
vanishes where the weight does. -/
theorem sum_supp_eq_of_subset (μ : FinDist Ω) {s : Finset Ω} (hs : μ.supp ⊆ s) {f : Ω → ℝ}
    (hf : ∀ ω, μ.w ω = 0 → f ω = 0) : ∑ ω ∈ s, f ω = ∑ ω ∈ μ.supp, f ω :=
  (Finset.sum_subset hs fun ω _ h => hf ω (by simpa [mem_supp] using h)).symm

/-- The weights sum to `1` over the support. -/
theorem sum_w_supp (μ : FinDist Ω) : ∑ ω ∈ μ.supp, μ.w ω = 1 := by
  obtain ⟨s, hs, h1⟩ := μ.exists_finset
  rw [← h1, sum_supp_eq_of_subset μ (supp_subset hs) fun _ h => h]

/-- The probability of an event `A`: the total weight of the outcomes in `A`. -/
noncomputable def prob (μ : FinDist Ω) (A : Set Ω) : ℝ :=
  ∑ ω ∈ μ.supp, A.indicator μ.w ω

/-- The expectation of a real random variable `X`: `∑ ω, w ω * X ω`. -/
noncomputable def expect (μ : FinDist Ω) (X : Ω → ℝ) : ℝ :=
  ∑ ω ∈ μ.supp, μ.w ω * X ω

/-! ### Constructors -/

/-- A distribution from weights supported on a finite set `s` and summing to `1` over `s`. -/
def ofFinset (s : Finset Ω) (w : Ω → ℝ) (h0 : ∀ ω, 0 ≤ w ω) (hs : ∀ ω ∉ s, w ω = 0)
    (h1 : ∑ ω ∈ s, w ω = 1) : FinDist Ω :=
  ⟨w, h0, s, hs, h1⟩

/-- A distribution on a `Fintype` from nonnegative weights summing to `1`. -/
def ofFintype [Fintype Ω] (w : Ω → ℝ) (h0 : ∀ ω, 0 ≤ w ω) (h1 : ∑ ω, w ω = 1) : FinDist Ω :=
  ⟨w, h0, Finset.univ, fun ω h => absurd (Finset.mem_univ ω) h, h1⟩

/-- The point mass (Dirac distribution) at `a`. -/
noncomputable def dirac (a : Ω) : FinDist Ω where
  w := ({a} : Set Ω).indicator 1
  w_nonneg := Set.indicator_nonneg fun _ _ => zero_le_one
  exists_finset := ⟨{a}, fun ω hω => Set.indicator_of_notMem (by simpa using hω) _, by simp⟩

/-- Two-step experiment ("fixing a prefix"): draw `a` from `μ`, then `b` from `K a`. The outcome
`(a, b)` has weight `μ.w a * (K a).w b`. -/
noncomputable def compProd (μ : FinDist α) (K : α → FinDist β) : FinDist (α × β) where
  w p := μ.w p.1 * (K p.1).w p.2
  w_nonneg p := mul_nonneg (μ.w_nonneg _) ((K _).w_nonneg _)
  exists_finset := by
    classical
    refine ⟨μ.supp ×ˢ μ.supp.biUnion fun a => (K a).supp, ?_, ?_⟩
    · rintro ⟨a, b⟩ h
      by_cases ha : μ.w a = 0
      · simp [ha]
      have ha' : a ∈ μ.supp := mem_supp.2 ha
      have hb : b ∉ (K a).supp := fun hb =>
        h (Finset.mem_product.2 ⟨ha', Finset.mem_biUnion.2 ⟨a, ha', hb⟩⟩)
      simp only [mem_supp, not_not] at hb
      simp [hb]
    · rw [Finset.sum_product]
      calc ∑ a ∈ μ.supp, ∑ b ∈ μ.supp.biUnion (fun a => (K a).supp), μ.w a * (K a).w b
          = ∑ a ∈ μ.supp, μ.w a := by
            refine Finset.sum_congr rfl fun a ha => ?_
            rw [← Finset.mul_sum, sum_supp_eq_of_subset (K a)
              (Finset.subset_biUnion_of_mem (fun a => (K a).supp) ha) fun _ h => h,
              sum_w_supp, mul_one]
        _ = 1 := μ.sum_w_supp

/-- The product of two independent distributions: `(a, b)` has weight `μ.w a * ν.w b`. -/
noncomputable def prod (μ : FinDist α) (ν : FinDist β) : FinDist (α × β) :=
  μ.compProd fun _ => ν

/-- The product of a finite family of independent distributions indexed by a `Fintype`:
`f : ∀ i, κ i` has weight `∏ i, (μ i).w (f i)`. -/
noncomputable def pi {ι : Type*} [Fintype ι] {κ : ι → Type*} (μ : ∀ i, FinDist (κ i)) :
    FinDist (∀ i, κ i) where
  w f := ∏ i, (μ i).w (f i)
  w_nonneg f := Finset.prod_nonneg fun i _ => (μ i).w_nonneg (f i)
  exists_finset := by
    classical
    refine ⟨Fintype.piFinset fun i => (μ i).supp, fun f hf => ?_, ?_⟩
    · simp only [Fintype.mem_piFinset, not_forall] at hf
      obtain ⟨i, hi⟩ := hf
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simpa [mem_supp] using hi)
    · rw [← Finset.prod_univ_sum]
      simp [sum_w_supp]

/-- The pushforward (law) of `μ` along `f`: `b` has weight `μ.prob (f ⁻¹' {b})`. -/
noncomputable def map (f : α → β) (μ : FinDist α) : FinDist β where
  w b := μ.prob (f ⁻¹' {b})
  w_nonneg b := Finset.sum_nonneg fun a _ => Set.indicator_nonneg (fun a _ => μ.w_nonneg a) a
  exists_finset := by
    classical
    refine ⟨μ.supp.image f, fun b hb => Finset.sum_eq_zero fun a ha =>
      Set.indicator_of_notMem (show a ∉ f ⁻¹' {b} from fun h =>
        hb (Finset.mem_image.2 ⟨a, ha, Set.mem_singleton_iff.1 (Set.mem_preimage.1 h)⟩)) _, ?_⟩
    simp only [prob]
    rw [Finset.sum_comm, ← μ.sum_w_supp]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [Finset.sum_eq_single_of_mem (f a) (Finset.mem_image_of_mem f ha)]
    · exact Set.indicator_of_mem (show a ∈ f ⁻¹' {f a} from rfl) _
    · intro b _ hb
      exact Set.indicator_of_notMem (show a ∉ f ⁻¹' {b} from fun h =>
        hb (Set.mem_singleton_iff.1 (Set.mem_preimage.1 h)).symm) _

/-- Composition of a distribution with a kernel: draw `a` from `μ`, then output a sample of
`K a`. -/
noncomputable def bind (μ : FinDist α) (K : α → FinDist β) : FinDist β :=
  (μ.compProd K).map Prod.snd

/-- The uniform distribution on a finite nonempty type. -/
noncomputable def uniform (Ω : Type*) [Finite Ω] [Nonempty Ω] : FinDist Ω where
  w _ := (Nat.card Ω : ℝ)⁻¹
  w_nonneg _ := by positivity
  exists_finset := by
    have := Fintype.ofFinite Ω
    refine ⟨Finset.univ, fun ω h => absurd (Finset.mem_univ ω) h, ?_⟩
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]
    have : (Fintype.card Ω : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    exact mul_inv_cancel₀ this

/-- The Bernoulli distribution with parameter `p ∈ [0, 1]` on `Bool`: `true` has probability `p`
and `false` has probability `1 - p`. -/
def bernoulli (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) : FinDist Bool where
  w b := cond b p (1 - p)
  w_nonneg b := by cases b <;> simp [h0, h1]
  exists_finset := ⟨Finset.univ, fun b h => absurd (Finset.mem_univ b) h, by simp⟩

/-- Conditioning on an event `A` of positive probability: `ω` has weight
`μ.w ω / μ.prob A` if `ω ∈ A`, and `0` otherwise.

`protected`, so that it does not shadow `_root_.cond` (`Bool.cond`) inside the namespace or when
`EG.FinDist` is opened; write `μ.cond A hA` or `FinDist.cond μ A hA`. -/
protected noncomputable def cond (μ : FinDist Ω) (A : Set Ω) (hA : 0 < μ.prob A) : FinDist Ω where
  w ω := A.indicator μ.w ω / μ.prob A
  w_nonneg ω := div_nonneg (Set.indicator_nonneg (fun ω _ => μ.w_nonneg ω) ω) hA.le
  exists_finset := by
    refine ⟨μ.supp, fun ω hω => ?_, ?_⟩
    · have : μ.w ω = 0 := by simpa [mem_supp] using hω
      simp [this]
    · rw [← Finset.sum_div]
      exact div_self hA.ne'

/-! ### Random subsets and random colourings -/

/-- The subset of `S` selected by the indicator `f : S → Bool`: the elements `a ∈ S` with
`f a = true`. -/
def selectSet (S : Finset α) (f : S → Bool) : Finset α :=
  (S.attach.filter fun x => f x = true).map (Function.Embedding.subtype _)

/-- Independent random subset of a finite set `S` with element probabilities `p`: every `a ∈ S`
is included independently with probability `p a` (a product of Bernoulli(`p a`) coins over `S`,
pushed forward to `Finset α`).

Manuscript uses: [s1:citThm16] (statement) "contain each vertex independently with
probability 1/3"; [s4:lemTPV] proof, item (G2): "keep each v ∈ V_{j,c} independently with
probability (1/L)/P(v ∈ V_{j,c})". -/
noncomputable def indepSubset (S : Finset α) (p : α → ℝ) (h0 : ∀ a ∈ S, 0 ≤ p a)
    (h1 : ∀ a ∈ S, p a ≤ 1) : FinDist (Finset α) :=
  (pi fun a : S => bernoulli (p a) (h0 a a.2) (h1 a a.2)).map (selectSet S)

/-- [s3, "Conventions for this section"] "For ρ ∈ [0,1], a ρ-random subset of a finite set S is a
random subset of S that contains each element of S independently with probability ρ."

The ρ-random subset of `S`: `indepSubset` with all element probabilities equal to `ρ`. -/
noncomputable def rsubset (S : Finset α) (ρ : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) :
    FinDist (Finset α) :=
  indepSubset S (fun _ => ρ) (fun _ _ => h0) (fun _ _ => h1)

/-- [s3:lemL15p] "Give every edge of X a colour from [k], independently and uniformly at random."

The uniformly random `k`-colouring of a finite type `ι` (for edges: `ι = ↥E` for an edge set
`E : Finset (Sym2 V)`): the product over `ι` of uniform distributions on `Fin k`. Colours are
`Fin k = {0, …, k-1}` in place of the manuscript's `[k] = {1, …, k}`. -/
noncomputable def randColouring (ι : Type*) [Fintype ι] (k : ℕ) [NeZero k] :
    FinDist (ι → Fin k) :=
  pi fun _ : ι => uniform (Fin k)

/-! ### Shared vocabulary: independence and ρ-random subsets

A random variable is a function `X : Ω → γ` on the sample space of a distribution `μ`. The three
predicates below are the fixed idioms for the manuscript's "independent" and "ρ-random subset";
downstream statements use them rather than ad hoc formulations. Their API (equivalent forms as
equalities of laws, transport along `map`, expectations of products, the elementwise reading of
`IsRSubset`) is in `EG/Lib/Prob/Indep.lean`. -/

/-- Independence of two random variables `X` and `Y` under `μ`: for all events `A` and `B`,
`P(X ∈ A and Y ∈ B) = P(X ∈ A) · P(Y ∈ B)`.

Manuscript uses: [s3:defCOL] (the list after "Consequently:") "the labels are independent of
the colours"; [s1:citMarkov](c) "any fixed outcome of variables that are independent of the
variables being drawn"; [s5:lemE1] proof of (c): "independently of the colouring of Y".

Equivalent to `μ.map (fun ω => (X ω, Y ω)) = (μ.map X).prod (μ.map Y)`
(`FinDist.indepFun_iff_map_eq_prod`). -/
def IndepFun {γ δ : Type*} (μ : FinDist Ω) (X : Ω → γ) (Y : Ω → δ) : Prop :=
  ∀ (A : Set γ) (B : Set δ), μ.prob (X ⁻¹' A ∩ Y ⁻¹' B) = μ.prob (X ⁻¹' A) * μ.prob (Y ⁻¹' B)

/-- Mutual independence of a family of random variables `(X u)_{u ∈ U}` under `μ`: for every
finite set `s` of indices and all events `A u`,
`P(X u ∈ A u for all u ∈ s) = ∏_{u ∈ s} P(X u ∈ A u)`. The value types `β u` may depend on `u`,
and `U` need not be finite (the condition is on finite subfamilies).

Manuscript uses: [s1:citChernoffGen] "Let X = ∑_{i=1}^m I_i be a sum of independent indicator
variables"; [s3:defCOL] (the list after "Consequently:") "colours of distinct edges are
independent".

For a `Fintype U` it is equivalent to `μ.map (fun ω u => X u ω) = pi fun u => μ.map (X u)`
(`FinDist.iIndepFun_iff_map_eq_pi`). -/
def iIndepFun {U : Type*} {β : U → Type*} (μ : FinDist Ω) (X : ∀ u, Ω → β u) : Prop :=
  ∀ (s : Finset U) (A : ∀ u, Set (β u)),
    μ.prob {ω | ∀ u ∈ s, X u ω ∈ A u} = ∏ u ∈ s, μ.prob (X u ⁻¹' A u)

/-- [s3, "Conventions for this section"] "For ρ ∈ [0,1], a ρ-random subset of a finite set S is a
random subset of S that contains each element of S independently with probability ρ."

The random set `V : Ω → Finset α` is a ρ-random subset of `S` under `μ`: `ρ ∈ [0, 1]` and the law
of `V` is `rsubset S ρ`. The elementwise reading (almost surely `V ⊆ S`, the indicators of
`a ∈ V` for `a ∈ S` are mutually independent, and each has probability `ρ`) is the theorem
`FinDist.isRSubset_iff`. -/
def IsRSubset (μ : FinDist Ω) (V : Ω → Finset α) (S : Finset α) (ρ : ℝ) : Prop :=
  ∃ (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1), μ.map V = rsubset S ρ h0 h1

end FinDist

end EG
