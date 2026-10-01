module

public import EG.Lib.Vortex.TPVStepMain

/-!
# One step of the VX⁺ run (manuscript s4:thmVXp, proof, "Step `j`" (a)–(f), "Cost")

Unit P3-s4. The run of Theorem VX⁺ is the run of Lemma TPV with `P = Z` (no `Q`), with two
changes in a step: the *parity* edges and the *flexible* edges.

"(a) *Parity.* For every `w ∈ W_j` with `deg_{F_j}(w)` odd, output one edge of `C^j_w` as a single
edge (the *parity edge* of `w`). … (b) … choose eight further distinct edges of `C^j_w` …:
*reserved* edges `e^{c,1}_w, e^{c,2}_w` (`c ∈ [3]`) and *flexible* edges `f_w, f'_w`. (c) *Classes.*
Every edge of `F'_j` that is not chosen receives … a class … Then `d_1(w)+d_2(w)+d_3(w) =
deg_{F'_j}(w) − 8` is even, so the number of odd `d_c(w)` is `0` or `2`. If `d_c(w)` and `d_{c'}(w)`
are odd (`c ≠ c'`), give `f_w` class `c` and `f'_w` class `c'`; otherwise give both class `1`. …
Then for all `w ∈ W_j` and `c ∈ [3]`, `deg_{F_{j,c}}(w)` is even … (d) … every `w ∈ W_j` is an end
of an even number, hence of `0` or `2`, paths of `Paths_{j,c}`."

The nine edges of `C^j_w` are indexed by `Fin 9`: `0, …, 5` reserved (`(c, i) ↦ 2c + i`), `6, 7`
flexible, `8` the parity edge (chosen only if `deg_{F_j}(w)` is odd).

Main result: `EG.VXRun.step` (the edges used, at most `13|U_j|` objects of which at most `|W_j|`
are single edges, and the invariants for `j + 1`).
-/

public section

namespace EG

namespace VXRun

open TPVRun

variable {V : Type*} [DecidableEq V]

/-! ### The flexible classes -/

/-- The class of `f_w` given the class degrees `d` at `w`. -/
@[expose] def flA (d : Fin 3 → ℕ) : Fin 3 :=
  if d 0 % 2 = 1 ∧ d 1 % 2 = 1 then 0 else if d 0 % 2 = 1 ∧ d 2 % 2 = 1 then 0
  else if d 1 % 2 = 1 ∧ d 2 % 2 = 1 then 1 else 0

/-- The class of `f'_w` given the class degrees `d` at `w`. -/
@[expose] def flB (d : Fin 3 → ℕ) : Fin 3 :=
  if d 0 % 2 = 1 ∧ d 1 % 2 = 1 then 1 else if d 0 % 2 = 1 ∧ d 2 % 2 = 1 then 2
  else if d 1 % 2 = 1 ∧ d 2 % 2 = 1 then 2 else 0

/-- "the number of odd `d_c(w)` is `0` or `2`. If `d_c(w)` and `d_{c'}(w)` are odd, give `f_w`
class `c` and `f'_w` class `c'`; otherwise give both class `1`": afterwards every class degree is
even. -/
theorem flex_parity (d : Fin 3 → ℕ) (h : (d 0 + d 1 + d 2) % 2 = 0) (x : Fin 3) :
    (d x + (if flA d = x then 1 else 0) + (if flB d = x then 1 else 0)) % 2 = 0 := by
  rcases Nat.mod_two_eq_zero_or_one (d 0) with h0 | h0 <;>
  rcases Nat.mod_two_eq_zero_or_one (d 1) with h1 | h1 <;>
  rcases Nat.mod_two_eq_zero_or_one (d 2) with h2 | h2 <;>
  fin_cases x <;> simp [flA, flB, h0, h1, h2] <;> omega

omit [DecidableEq V] in
/-- Nine distinct elements of a set with at least nine elements. -/
theorem exists_nine {s : Finset V} (h : 9 ≤ s.card) :
    ∃ f : Fin 9 → V, (∀ k, f k ∈ s) ∧ Function.Injective f := by
  obtain ⟨t, hts, htc⟩ := Finset.exists_subset_card_eq h
  refine ⟨fun k => (t.equivFin.symm (Fin.cast htc.symm k)).1, fun k => hts (t.equivFin.symm _).2,
    ?_⟩
  intro a b hab
  have := Subtype.ext hab
  have := t.equivFin.symm.injective this
  exact Fin.cast_injective _ this

/-- The reserved index of `(c, i)`: `2c + i`. -/
@[expose] def idx (c : Fin 3) (i : Fin 2) : Fin 9 := ⟨2 * c + i, by omega⟩

theorem idx_lt (c : Fin 3) (i : Fin 2) : (idx c i : ℕ) < 6 := by
  simp only [idx]; omega

theorem idx_div (c : Fin 3) (i : Fin 2) : (idx c i : ℕ) / 2 = c := by
  simp only [idx]; omega

theorem idx_ne (c : Fin 3) : idx c 0 ≠ idx c 1 := by
  simp [idx, Fin.ext_iff]

/-- The class of the chosen edge with index `k` at `w` (reserved: `k / 2`; flexible: `a`, `b`). -/
@[expose] def chc (a b : Fin 3) (k : Fin 9) : Fin 3 :=
  if h : (k : ℕ) < 6 then ⟨k / 2, by omega⟩ else if (k : ℕ) = 6 then a else b

theorem chc_idx (a b : Fin 3) (c : Fin 3) (i : Fin 2) : chc a b (idx c i) = c := by
  simp only [chc, dif_pos (idx_lt c i)]
  exact Fin.ext (idx_div c i)

/-- The number of flexible indices of class `x`. -/
theorem card_flex (a b x : Fin 3) :
    (Finset.univ.filter fun k : Fin 9 => ((k : ℕ) = 6 ∨ (k : ℕ) = 7) ∧ chc a b k = x).card =
      (if a = x then 1 else 0) + (if b = x then 1 else 0) := by
  have e : (Finset.univ.filter fun k : Fin 9 => ((k : ℕ) = 6 ∨ (k : ℕ) = 7) ∧ chc a b k = x) =
      (if a = x then {(6 : Fin 9)} else ∅) ∪ (if b = x then {(7 : Fin 9)} else ∅) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    constructor
    · rintro ⟨hk | hk, hc⟩
      · have hk' : k = 6 := Fin.ext hk
        subst hk'
        left
        have : chc a b 6 = a := by simp [chc]
        rw [this] at hc
        simp [hc]
      · have hk' : k = 7 := Fin.ext hk
        subst hk'
        right
        have : chc a b 7 = b := by simp [chc]
        rw [this] at hc
        simp [hc]
    · rintro (hk | hk)
      · split_ifs at hk with ha
        · rw [Finset.mem_singleton] at hk
          subst hk
          exact ⟨Or.inl rfl, by simp [chc, ha]⟩
        · simp at hk
      · split_ifs at hk with hb
        · rw [Finset.mem_singleton] at hk
          subst hk
          exact ⟨Or.inr rfl, by simp [chc, hb]⟩
        · simp at hk
  rw [e]
  split_ifs <;> simp

/-- The number of chosen indices: `8`, or `9` with the parity edge. -/
theorem card_chosen (o : Prop) [Decidable o] :
    (Finset.univ.filter fun k : Fin 9 => (k : ℕ) < 8 ∨ o).card = if o then 9 else 8 := by
  split_ifs with h
  · simp [h]
  · simp only [h, or_false]
    decide

end VXRun

end EG
