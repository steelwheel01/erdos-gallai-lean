module

public import EG.Defs.Graph
public import EG.Defs.Prob.FinDist

/-!
# The round randomness `ξ_l` and its law (manuscript s7:defSchedule, "Rounds")

PROTECTED FILE (`EG/Defs/**`): changes need the approval procedure in `APPROVALS/README.md`.

Manuscript v6.1, `s7.tex`, Definition [s7:defSchedule]:
"*Rounds* `l = R, R-1, …, 3`. The round randomness `ξ_l` consists of the following mutually
independent variables: a uniformly random bijection `η_h : [4M_l] → [4M_l]` for every vertex `h`;
a uniformly random `3`-subset `ζ_{h,u} ⊆ [4M_l]` for every ordered pair `(h,u)` of distinct
vertices; and a uniformly random linear order `≺_u` of `V(G)` for every vertex `u`. … The draw
`ξ_l` is fresh: it is independent of stage 1, of stage 3 and of all `ξ_{l'}` with `l' > l`."
"The *past* `Past_l` … is a fixed outcome, not a random σ-algebra. We write `E[·|Past_l]` and
`P(·|Past_l)` for expectation and probability over `ξ_l` with `Past_l` fixed."

Design note: `formal/work/p2d/quot.md`. Namespace `EG.Quot`; TRIAGE §2.10, §3 item 30. Stage 1
(its record and law) is `EG.Stage1.Outcome` / `EG.Stage1.law` (`EG.Defs.Stage1.Law`); it is not
redefined here.

Encoding (TRIAGE §2.10; blueprint s7a SCHED-*):
* the past is a **parameter** (the abstract round input of `EG.Defs.Quot.Round`), so
  `E[·|Past_l]` is the expectation under `roundLaw` with the past fixed, and freshness is
  definitional;
* `[4M_l]` is `Fin (4 * M)` (0-based; `M = M_l ∈ ℕ`, v6.1 (R2)); `η_h : Equiv.Perm (Fin (4M))`;
* `ζ_{h,u}` is a value in `Finset (Fin (4M))` whose law `subset3Law` is uniform on the
  `3`-subsets (so the type `Lists` is inhabited for every `M`; for `4M < 3`, which never happens
  since `M_l ≥ 2^40`, the junk law is `dirac ∅`);
* `ζ` is drawn for **every** ordered pair of vertices of `G`, including `h = u` (extra independent
  coordinates that are never read; they do not change the joint law of the variables the round
  step reads, blueprint SCHED-XI-TYPES);
* `≺_u` is a *rank* `↥G.verts ≃ Fin n` (`n = |V(G)|`): `v ≺_u v'` iff `rank v < rank v'`; the uniform
  law on ranks is the uniform law on linear orders;
* families "for every vertex" are indexed by `↥G.verts` (TRIAGE §2.5);
* the *lists* are the variables `η_h`, `ζ_{h,u}` (s7:consRound (e2), "the lists are fixed"):
  `Lists G M`; the *orders* are `Orders G`; `Xi G M := Lists G M × Orders G`; `roundLaw` is the
  product law of the three families.
* **the second argument is `M = M_l`, not `4M_l`** (the factor `4` is inside `Lists`): write
  `roundLaw I.G I.M`, `Lists I.G I.M`, `Xi I.G I.M` (the blueprint lean_shapes' `roundLaw I.G (4 * I.M)`
  and `κ : Fin (4 * I.M)` are not the Lean shapes); the colours of the round step are natural
  numbers `κ < 3M` (PAR) and `κ < 4M` (HUB).
-/

@[expose] public section

namespace EG.Quot

variable {V : Type*} [DecidableEq V]

/-- The *lists* of the round randomness: the bijections `η_h : [4M] → [4M]` (`h ∈ V(G)`) and the
`3`-subsets `ζ_{h,u} ⊆ [4M]` (`(h,u) ∈ V(G)²`; see the module docstring for `h = u`). -/
abbrev Lists (G : FGraph V) (M : ℕ) : Type _ :=
  (↥G.verts → Equiv.Perm (Fin (4 * M))) × (↥G.verts × ↥G.verts → Finset (Fin (4 * M)))

/-- The *orders* of the round randomness: for every `u ∈ V(G)`, the linear order `≺_u` of `V(G)`,
given by its rank function `↥G.verts ≃ Fin |V(G)|`. -/
abbrev Orders (G : FGraph V) : Type _ := ↥G.verts → (↥G.verts ≃ Fin G.card)

/-- [s7:defSchedule] the round randomness `ξ_l = (η_h, ζ_{h,u}, ≺_u)`: the lists and the orders. -/
abbrev Xi (G : FGraph V) (M : ℕ) : Type _ := Lists G M × Orders G

omit [DecidableEq V] in
theorem card_verts_eq (G : FGraph V) : Fintype.card ↥G.verts = G.card := by
  simp [FGraph.card]

instance (G : FGraph V) : Nonempty (↥G.verts ≃ Fin G.card) :=
  ⟨Fintype.equivFinOfCardEq (card_verts_eq G)⟩

theorem nonempty_subset3 {K : ℕ} (h : 3 ≤ K) : Nonempty {s : Finset (Fin K) // s.card = 3} := by
  obtain ⟨t, -, ht⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin K)))
    (n := 3) (by simpa using h)
  exact ⟨⟨t, ht⟩⟩

/-- [s7:defSchedule] "a uniformly random `3`-subset `ζ ⊆ [K]`": the uniform law on the `3`-subsets
of `Fin K`, as a law on `Finset (Fin K)` (junk `dirac ∅` if `K < 3`). -/
noncomputable def subset3Law (K : ℕ) : FinDist (Finset (Fin K)) :=
  if h : 3 ≤ K then
    haveI := nonempty_subset3 h
    (FinDist.uniform {s : Finset (Fin K) // s.card = 3}).map Subtype.val
  else FinDist.dirac ∅

/-- [s7:defSchedule] the law of the lists: independently for every vertex `h` a uniformly random
bijection `η_h` of `[4M]`, and independently for every ordered pair `(h,u)` a uniformly random
`3`-subset `ζ_{h,u}` of `[4M]`. -/
noncomputable def listsLaw (G : FGraph V) (M : ℕ) : FinDist (Lists G M) :=
  (FinDist.pi fun _ : ↥G.verts => FinDist.uniform (Equiv.Perm (Fin (4 * M)))).prod
    (FinDist.pi fun _ : ↥G.verts × ↥G.verts => subset3Law (4 * M))

/-- [s7:defSchedule] the law of the orders: independently for every vertex `u` a uniformly random
linear order `≺_u` of `V(G)` (a uniformly random rank function). -/
noncomputable def ordersLaw (G : FGraph V) : FinDist (Orders G) :=
  FinDist.pi fun _ : ↥G.verts => FinDist.uniform (↥G.verts ≃ Fin G.card)

/-- [s7:defSchedule] the law of the round randomness `ξ_l` ("mutually independent variables"):
the product of the law of the lists and the law of the orders. `E[X | Past_l]` is
`(roundLaw G M).expect X` with the past (a parameter of `X`) fixed. -/
noncomputable def roundLaw (G : FGraph V) (M : ℕ) : FinDist (Xi G M) :=
  (listsLaw G M).prod (ordersLaw G)

/-! ### Reading the round randomness at vertices of `V` -/

/-- `η_h` for `h : V` (the identity if `h ∉ V(G)`, never read there). -/
def etaAt {G : FGraph V} {M : ℕ} (L : Lists G M) (h : V) : Equiv.Perm (Fin (4 * M)) :=
  if hh : h ∈ G.verts then L.1 ⟨h, hh⟩ else 1

/-- `ζ_{h,u}` for `h u : V` (`∅` if `h ∉ V(G)` or `u ∉ V(G)`, never read there). -/
def zetaAt {G : FGraph V} {M : ℕ} (L : Lists G M) (h u : V) : Finset (Fin (4 * M)) :=
  if hh : h ∈ G.verts then (if hu : u ∈ G.verts then L.2 (⟨h, hh⟩, ⟨u, hu⟩) else ∅) else ∅

/-- The elements of `C` that lie in `V(G)`, listed in increasing order of the rank `o` (i.e. in the
order `≺` given by `o`). -/
def sortByRank {G : FGraph V} (o : ↥G.verts ≃ Fin G.card) (C : Finset V) : List V :=
  (List.finRange G.card).filterMap (fun i => if ((o.symm i : ↥G.verts) : V) ∈ C then
    some ((o.symm i : ↥G.verts) : V) else none)

/-- [s7:consRound] (e2) "`w_1 ≺_u w_2 ≺_u ⋯` the elements of `C` in the order `≺_u`" (the
empty list if `u ∉ V(G)`). -/
def inOrder {G : FGraph V} (O : Orders G) (u : V) (C : Finset V) : List V :=
  if hu : u ∈ G.verts then sortByRank (O ⟨u, hu⟩) C else []

end EG.Quot
