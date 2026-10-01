# Blocker ROUND-RULE-DEPENDENCE — resolution memo

Source hazard: `formal/work/p2/blueprint_s7a.md` (ROUND-RULE-DEPENDENCE on `s7:consRound`, SCHED-RULE-DEPENDENCE on `s7:defSchedule`, WD-SDR-INDEP-SIMPLE, CC-CONDITIONING; `blueprint_s7b.md` PAY-C-CONDITIONING).
Manuscript: `proofs/manuscript/s7.tex` v6 (line numbers below refer to it). Reviewer: Fable 5.1, 2026-09-26.

**Verdict in one paragraph.** The round step uses nine "fixed rules / fixed orders" whose admissible inputs the text never states. Every probabilistic consumer needs a specific restriction (table in §2), and every restriction it needs is one the manuscript *asserts in a proof* but never *imposes in the construction*. No use anywhere in s6/s7 (including s6:defJconsumer, s6:consOrder(4), s7:thmJVps, s7:lemOneOutcome, the Markov choice (f), the rank split (g) and Dec_l (h)) needs a rule to read the orders ≺_u, and none needs the grouping to read η. The proposed restriction is therefore consistent with every use, and the intended construction satisfies it. The blueprint's claim that Lemma CC, the ultra-hub lemma, Pay(c) and Cuckoo SDR are *false* for rules that read ≺ (resp. η) is confirmed with explicit adversarial rules (§3). Classification: **T1** (statements true for the intended construction; the construction text under-specifies the rules and the proofs of WellDef(iii), CC(i), Ultra(i), Pay(c) and the (e2) claim rely on the unstated restriction). Not T0: a manuscript sentence is required, not only a Lean convention. Not T2: no statement is false for the construction the text describes once "fixed rule" is read as the text's own proofs read it, and no constant changes. Exact replacement text in §4; Lean encoding in §5.

---

## 1. Inventory: the nine fixed choices, where they are made, what they may see

Notation: **P** = Past_l (stage 1, stage 2 statuses, stage 3, ξ_{l'} for l' > l and everything they determine, in particular J_l, the pool, Cand_l(·), JV-bad statuses, D_l, F_Z, Q*_Z, the classes Y(u)). **L** = the lists component of ξ_l, i.e. (η_h)_h and (ζ_{h,u})_{h,u}. **O** = the orders component (≺_u)_u. ξ_l = (L, O).

| # | step | rule (s7.tex) | what it chooses | data it must be able to read | data it must NOT read | why (consumer) |
|---|---|---|---|---|---|---|
| R1 | (b) l.257 | "paired, by a fixed rule, into cherries" | a pairing of the live Jfr items at each fresh centre x | P (live items are determined in (a) from J_l, Pool_l, JV-bad) | O; (L harmless, see §2.7) | CC, Pay(c): "the κ-object at x" and S_w must be functions of (P, L) |
| R2 | (b) l.261 | "one of them, chosen by a fixed rule, is paid" | the unpaired fresh leg when the count is odd | P | O | same; Pay(b) counts it deterministically |
| R3 | (b) l.262 | "coloured greedily, in a fixed order" | order of the PAR objects for the greedy colouring, hence the colouring | P | O | CC: colour classes fixed given (P, L) |
| R4 | (c) l.273–274 | "split, by a fixed rule, into k_h groups" | partition of the live items of a non-ultra hub h into k_h groups of ≤ ⌈Hcd_l/8⌉ | P | **η_h** (and all of L), O | WellDef(iii): the list of (h_i,u) must be the image of a *fixed* 3-set under η_{h_i} (uniform 3-subset); WellDef(iv) needs only group sizes |
| R5 | (d) l.288–289 | "chooses, by a fixed rule, pairwise distinct colours … (a system of distinct representatives)" | one SDR among those that exist | P, L (colours come from the lists) | O | (e2) claim l.309–312 and §"lists fixed" l.700–704: (a)–(d),(e1) determined by (P, L); CC(i), Ultra(i), Pay(c) |
| R6 | (e1) l.299–300 | "processed in a fixed order" | processing order of the coloured non-ultra items | P, L (the set of coloured items depends on L) | O | same as R5 (Used(u) must be a function of (P, L)) |
| R7 | (e1) l.301 | "the first vertex w, in a fixed order of V(G)" | the order of V(G) used to pick the (e1) junction | P (L harmless) | O | same; §3.3 shows a ≺_u-reading order biases w_1 by a factor up to M_l−1 |
| R8 | (e2) l.305–306 | "listed in a fixed order e_1,…,e_q" | the order of E'(u) | P, L (E'(u) contains the coloured ultra items, which depend on L) | O (neither ≺_u nor any ≺_x) | CC(i) l.759–766, Ultra(i) l.831–837, Pay(c) l.962–967: "the junction of the κ-end at x is a function of ≺_x alone" and "uniform on C(x)" |
| R9 | (g) l.345–347 | "listed in a fixed order" (rank split) | order of the parallel edges of a layer | anything (P, L, O) | — | copies_l, MULT, CC(iii), UHsplit(ii) are invariant under the rank order (a vertex is non-isolated in exactly max m sub-layers whichever order is used, s7.tex l.546–550) |
| R10 | (h) l.356–358 | "chosen by a fixed deterministic rule" (Dec_l) | a decomposition of E(Q_l) into f(Q_l) objects | anything: it is a function of Q_l, which depends on all of ξ_l | — | Lift(ii) holds for *every* Dec (l.585); the only requirement is determinism so that Past_{l−1} is well defined (remNonCirc(3)) |

(The blueprint counts nine; R2 is listed separately here, so ten rows. R9/R10 are the blueprint's "(g),(h) arbitrary".)

Rules outside the round step that were checked and are unaffected: the designation δ (s6:defDesign / s7:thmMainProof l.1485, fixed before stage 1); the choices inside JS-LC Step 2 (s6:lemJplus: "every choice of which edges are deleted"), made at s6:consOrder step (3), i.e. *before* ξ_l is drawn, hence functions of P; the (1e) and stage-3 selections and the choice of ξ_l in the event of (f) (s7:lemOneOutcome), which select outcomes and are not rules of the round step.

### Where the manuscript already asserts the restriction (as a proof step, not as part of the construction)

- (e2), l.308–312: "With Past_l and the lists fixed, the map e_i ↦ w_i is a uniformly random injection …, and these injections are independent over ports: Used(u) is determined by Past_l and the lists, and the orders ≺_u are independent of both." — asserts R5, R6, R7 ∈ (P, L) and R8 independent of O.
- §"Quotient size and payments", l.700–704: "We say that the lists are fixed when … η_h and ζ_{h,u} … are fixed. Then steps (a)–(d) and (e1) … are determined, and only the orders ≺_u are random." — asserts R1–R7 ∈ (P, L).
- WellDef(iii) proof, l.437–440: "With Past_l fixed, it is determined which hubs are ultra, how the items are grouped, and which group each item belongs to. The list of (h_i,u) is a function of η_{h_i} …" — asserts R4 ∈ P.
- CC(i) proof, l.759–761: "With the past and the lists fixed, the junction of the κ-end at a port x is a function of ≺_x alone" — asserts R8 ∈ (P, L).
- Ultra(i) proof, l.831–836; Pay(c) proof, l.962–967 — same as CC(i).
- Blueprint s7b PAY-C-CONDITIONING already notes that PAR objects "are determined by (ω, J) … not by ξ_l".

None of these sentences is a consequence of the construction as written: "fixed rule" is undefined, and since ξ_l is drawn at the start of the round (defSchedule l.181–189), a "deterministic rule chosen in advance" can be a function of all of ξ_l. The proofs therefore use a property of the construction that the construction does not state. That is the gap.

---

## 2. What each consumer needs (derivation from the TeX)

2.1 **s7:lemWellDef(iii) (Cuckoo SDR).** Failure at u is a Hall violation among the m lists of the live hub items (h_i,u). The proof needs: (α) the set of live items, ultra status of each h_i, and the group index g_i of (h_i,u) are functions of P; then the list is η_{h_i}({3g_i−2, 3g_i−1, 3g_i}) for non-ultra h_i (a uniform 3-subset, as the image of a fixed set under a uniform permutation) or ζ_{h_i,u} for ultra h_i; (β) distinct hubs ⇒ distinct coordinates ⇒ independent lists. Needs R4 ∈ P (and ultra/live in P, which they are). Does not depend on R5 (existence, not the choice) nor on anything in O. **Necessity of R4 ∈ P: §3.1.**

2.2 **s7:lemWellDef(i),(ii),(iv),(v); s7:lemMULT; s7:lemSimple; s7:lemLift.** Deterministic for every past and every ξ_l; they hold for arbitrary rules of any argument type (Lift(ii) explicitly for every Dec). No restriction needed.

2.3 **The (e2) claim (l.308–312), s7:lemCC(i), s7:lemUltra(i), s7:lemPay(c) loops.** Need, with (P, L) fixed: C(u) := Cand_l(u)∖Used(u) is fixed (R5, R6, R7 ∈ (P, L)); E'(u) and its order are fixed (R1–R3, R5, R8 ∈ (P, L)); then e_i ↦ w_i is the restriction of the uniform order ≺_u to the fixed set C(u), so the junction of e_i is uniform on C(u) and is a function of ≺_u alone; independence over ports is independence of the coordinates ≺_u. Every rule R1–R8 must therefore be independent of O. **Necessity: §3.2, §3.3.**

2.4 **s7:lemCC(ii),(iii).** (ii) conditions the product law on the atom (I_x)_x; each I_x is a function of ≺_x alone by 2.3; S_w and the partner ports are functions of the indicators. (iii) averages over the atoms and uses Σ|S_w| ≤ 2·#PAR objects (deterministic). Needs exactly 2.3. Also needs the colour classes (R3) fixed given (P, L) so that "the κ-object at x" is well defined before ≺ is drawn.

2.5 **s7:lemUltra(ii)–(iv), s7:lemUHsplit(ii).** Ultra(ii)–(iv) need only Ultra(i) plus deterministic counts. UHsplit(ii): PAR copies via CC(iii); non-ultra hub copies are deterministic given (P, L) by WellDef(iv) + MULT (needs (e1) to be a function of (P, L), i.e. R5–R7 ∈ (P, L)); junction copies via MULT (deterministic); ultra copies via Ultra(iv). Then "averaging over the lists" (Fubini over the product law L × O). Nothing further.

2.6 **s7:lemPay(c) SDR part, (d), s7:consRound(f), s7:lemOneOutcome, s7:thmJVps, s7:remNonCirc(3), s6:defJconsumer, s6:consOrder(4).** (f) is Markov for the non-negative functions copies_l, pay_l of ξ_l with P fixed: valid for rules of any argument type; the bound ≥ 1/2 needs only the expectations of UHsplit(ii)/Pay(c), which hold under 2.1–2.5. lemOneOutcome(iii) picks ξ_l in the event and then applies the *deterministic* construction to it: R9/R10 may read all of ξ_l, and the chosen ξ_l (including its orders) becomes part of Past_{l−1}, which the rules of round l−1 may read in full (the orders are re-drawn per round, l.187). s6:defJconsumer explicitly allows "possibly fresh randomness"; s6:consOrder(4) applies the consumer after J_l is fixed at step (3). No use needs a round-l rule to read the round-l orders. **No conflict.**

2.7 **Could any rule be *relaxed* relative to the blueprint's proposal?** R1–R3 (step (b)) could be allowed to read L without breaking any proof (all proofs of 2.3–2.5 fix L first), and R7 could be restricted to P. Neither relaxation is used anywhere. Recommendation: keep the blueprint's assignment (R1–R4: P; R5–R8: P, L), because (i) it matches the step order of the text (lists first appear in (c)), (ii) ROUND-PAY-DEF and s7:lemPay(b)/propCost treat the unpaired fresh legs as deterministic in the past, and (iii) Cuckoo (2.1) forces R4 ∈ P anyway, so "step (b),(c): past" is the uniform statement.

2.8 **Could the restriction "none depends on the orders" be applied to R9, R10 as the blueprint's sentence literally says?** No: Q_l depends on O, so Dec_l (a function of Q_l) depends on O, and the parallel classes ordered in (g) depend on O. The sentence must exempt (g),(h) (or phrase (g) as a P-order on the index set of items/PAR objects, restricted to each parallel class). The wording in §4 does this.

---

## 3. Confirmation that the restriction is necessary (adversarial rules)

All rules below are deterministic and "fixed in advance"; they merely read more of ξ_l than the proofs allow. The round lemmas are stated "for every past", so any past satisfying the J⁺ interface (RoundInput.Valid) is in scope.

3.1 **Grouping reading η_h ⇒ WellDef(iii) false.** Let u be a port with m = M_l − 1 live hub items (h_i,u) (allowed by J2) at non-ultra hubs h_i with k_{h_i} =: k ≥ 2 groups (i.e. c_{h_i} > ⌈Hcd_l/8⌉; the manuscript's ultra mechanism exists precisely because c_h up to and beyond thult_l = ⌊M_l Hcd_l/7⌋ is contemplated, and J1/J2 do not cap c_h below that). Rule: group the items of h_i so that (h_i,u) lands in a group whose η_{h_i}-image lies inside T := [m−1] ⊂ [K], K = 4M_l, when such a group exists. The k images are disjoint uniform 3-subsets; P(a given one ⊆ T) = C(m−1,3)/C(K,3) ≈ 4^{−3}, so P(no group of h_i has image ⊆ T) ≤ (1 − c)^k for an absolute c > 0 (negative association of the disjoint blocks); for k close to 8M_l/7 this is e^{−Ω(M_l)}. Then, with probability ≥ 1 − m·e^{−Ω(M_l)}, all m lists at u lie in the (m−1)-set T, Hall fails, and P(SDR failure at u | Past_l) ≈ 1 ≫ (4M_l)^{−4}. For small k ≥ 2 the failure probability is still ≥ k^{s}-times the manuscript's term T_s for every s, and the union bound of l.452–481 is invalid. With k = 1 there is no freedom, so the statement survives only for pasts in which every hub at u has c_h ≤ ⌈Hcd_l/8⌉.

3.2 **(e2) order reading ≺_x ⇒ CC(i), Ultra(i) false outright; Pay(c) false for suitable pasts.** Rule at port x: put the κ-end at the index i such that w_i = the first element of C(x) in a fixed (past-only) order of V(G). Its junction is then min C(x), a constant: "uniform on C(v_o)∖{w}" (l.727) fails for every past with a PAR object (|C(x)| ≥ Hcd_l/2 ≥ 2). Same rule for ultra ends kills Ultra(i) ("each is uniform on a set of size ≥ Hcd_l/2"). For loops: let each port x with a κ-object o = {x, x'} put its κ-end at the ≺_x-index of w*(o) := min(C(x) ∩ C(x')) whenever the intersection is non-empty (a function of (P, L), computable at both ports); then o loops with probability 1, and E[loop-paid | Past_l] ≥ #{o : C(p_o) ∩ C(q_o) ≠ ∅}, which for pasts with many such objects (overlapping ancestors, mult_r(w) ≥ 2) exceeds 5.5 nM_l/Hcd_l. Each rule reads only its own ≺_x, so the "independent over ports" clause alone would not detect it; the uniformity clause does. A rule reading a *different* port's order (≺_{x'}) breaks independence across ports directly.

3.3 **(e1) order of V(G) reading ≺_u ⇒ uniformity of w_1 fails.** Fix a target w* ∈ Cand_l(u). Rule for each of the j ≤ M_l − 2 (e1) items at u: if w* is the ≺_u-minimum of the current Cand_l(u)∖Used(u)∖Used_κ(h), take the second element, else take the minimum. After (e1), w* is the ≺_u-minimum of C(u) whenever it was among the first j+1 elements of Cand_l(u) in ≺_u: P(w_1 = w*) = (j+1)/|Cand_l(u)|, up to (M_l − 1)/Hcd_l instead of 1/|C(u)| ≤ 2/Hcd_l. The "at most 3/Hcd_l" of CC(i) and the "2/Hcd_l" of Pay(c) fail.

3.4 **SDR reading ≺_u.** If an SDR exists, all live hub items at u are coloured, so the *membership* of E'(u) is P-determined; only the colours vary. A rule reading ≺_u can still correlate the colour of an ultra item (h,u) with its junction (known from ≺_u and R8), so that "the junctions of the items of colour κ at h are independent and uniform" (Ultra(i)) is no longer a statement about a fixed set of items; the proof of Ultra(i) breaks (the quantitative failure is milder, a factor ≤ 3 in collision rates). R5 must therefore also be independent of O, as the text's l.700–704 already asserts.

3.5 **Rules reading L where only P is allowed (R1–R3).** No proof breaks (§2.7); this part of the blueprint's restriction is a convention, not a necessity. R4 reading L is fatal (3.1).

Conclusion of §3: the blueprint's "FALSE" claims are correct (with the k_h ≥ 2 proviso for 3.1), and the necessity is exactly: R4 ∈ P; R1–R8 independent of O. Everything else is convention.

---

## 4. Classification and exact replacement text

**Class: T1** (PLAN §7). Statement true for the construction as intended and as the manuscript's own proofs read it; the construction text has a definitional gap that the proofs of s7:lemWellDef(iii), the (e2) claim of s7:consRound, s7:lemCC(i), s7:lemUltra(i) and s7:lemPay(c) silently fill. No statement is weakened, no constant changes, no consumer outside s7 is affected (s6:defJconsumer already admits "possibly fresh randomness"). The Lean side of the same decision is a T0 encoding (the argument types of `Rules`), recorded in §5.

**Patch 1 — s7:consRound, insert after the first paragraph (after "…(i)–(v) of Lemma~\ref{s6:lemJplus}.", l.234):**

```latex
\emph{Fixed rules.} The steps below use several ``fixed rules'' and ``fixed
orders''. Each is a deterministic rule, chosen once and for all before any
randomness is drawn, and each may read only the data named here. The rules of
steps (b) and (c) (the pairing of the live $\Jfr$ items at a fresh centre and the
choice of its unpaired leg, the order in which the PAR objects are coloured, and
the splitting of the live items of a non-ultra hub into groups) are functions of
$\Past_l$ alone; in particular they do not read $\xi_l$. The rules of steps (d),
(e1) and (e2) (the choice of the system of distinct representatives, the
processing order of the coloured hub items, the order of $V(G)$ used in (e1), and
the order $e_1,\dots,e_q$ of $E'(u)$) are functions of $\Past_l$ and of the
\emph{lists}, that is, of the variables $\eta_h$ and $\zeta_{h,u}$ of $\xi_l$;
none of them reads any of the orders $\prec_u$. The orders $\prec_u$ enter the
construction only through the assignment $e_i\mapsto w_i$ of step (e2). The rank
orders of step (g) and the rule choosing $\Dec_l$ in step (h) are deterministic
functions of $\Past_l$ and $\xi_l$ (they may read $Q_l$) and are otherwise
arbitrary. Every statement of this section about the round step holds for every
choice of the fixed rules that obeys these restrictions; the restrictions are
used in Lemma~\ref{s7:lemWellDef}(iii) (the grouping does not read $\eta_h$) and
in the claims of step (e2), Lemma~\ref{s7:lemCC}(i), Lemma~\ref{s7:lemUltra}(i)
and Lemma~\ref{s7:lemPay}(c) (nothing before the assignment $e_i\mapsto w_i$
reads the orders $\prec_u$).
```

**Patch 2 — s7:consRound (e2), l.311–312, replace** "$\Used(u)$ is determined by $\Past_l$ and the lists, and the orders $\prec_u$ are independent of both." **by**

```latex
by the restrictions on the fixed rules, $\Used(u)$, $E'(u)$ and the order
$e_1,\dots,e_q$ are determined by $\Past_l$ and the lists, and the orders
$\prec_u$ are independent of both.
```

**Patch 3 — s7:lemWellDef proof (iii), l.437–439, replace** "With $\Past_l$ fixed, it is determined which hubs are ultra, how the items are grouped, and which group each item belongs to." **by**

```latex
With $\Past_l$ fixed, it is determined which hubs are ultra, how the items are
grouped, and which group each item belongs to: the grouping rule of step (c)
reads $\Past_l$ only (the restrictions on the fixed rules in
Construction~\ref{s7:consRound}).
```

**Patch 4 — §"Quotient size and payments", l.702–704, replace** "Then steps (a)--(d) and (e1) of Construction~\ref{s7:consRound} are determined, and only the orders $\prec_u$ are random." **by**

```latex
Then steps (a)--(d) and (e1) of Construction~\ref{s7:consRound}, the sets
$E'(u)$ and their orders $e_1,\dots,e_q$ are determined (by the restrictions on
the fixed rules), and only the orders $\prec_u$ are random.
```

**Patch 5 — s7:lemCC proof (i), l.759–761, replace** "With the past and the lists fixed, the junction of the $\kappa$-end at a port $x$ is a function of $\prec_x$ alone, and the orders of distinct ports are independent." **by**

```latex
With the past and the lists fixed, $C(x)$, $E'(x)$ and its order are fixed for
every port $x$ (restrictions on the fixed rules), so the junction of the
$\kappa$-end at $x$ is a function of $\prec_x$ alone, and the orders of distinct
ports are independent.
```

**Patch 6 (optional, defSchedule l.196–197)** after "…probability over $\xi_l$ with $\Past_l$ fixed." add: "The fixed rules of Construction~\ref{s7:consRound} read $\xi_l$ only as stated there."

No change to any statement; the added clause "for every choice of the fixed rules that obeys these restrictions" strengthens the lemmas' scope (they were implicitly about one construction). Ledger entry: T1, labels s7:consRound (definition text), s7:lemWellDef, s7:lemCC, s7:lemPay (proof sentences), cross-references only in s7:defSchedule and the §"Quotient size and payments" preamble.

---

## 5. Lean encoding (the T0 half of the decision)

Confirms PLAN decision 7 and the blueprint's `Rules I` with these argument types (the types *are* the restriction; `R.Valid` carries only the specifications, never argument restrictions):

```lean
structure Rules (I : RoundInput V) where
  freshPairing : V → List (Sym2 V × Sym2 V)              -- R1 (b): past only
  unpairedLeg  : V → Option (Sym2 V)                     -- R2 (b): past only
  parColour    : ParObj V → Fin (3 * I.M)                -- R3 (b): past only (any proper colouring; greedy existence is WellDef(i))
  hubGroup     : V → Sym2 V → ℕ                          -- R4 (c): past only — MUST NOT take Lists
  sdr          : Lists I.G (4 * I.M) → V → Sym2 V → Option (Fin (4 * I.M))   -- R5 (d)
  e1Order      : Lists I.G (4 * I.M) → List (Sym2 V)     -- R6 (e1)
  vertOrder    : Lists I.G (4 * I.M) → List V            -- R7 (e1)  (past-only also acceptable)
  e2Order      : Lists I.G (4 * I.M) → V → List (End V)  -- R8 (e2)
  rank         : Xi I.G (4 * I.M) → LayerEdge V → ℕ      -- R9 (g): anything
  dec          : FGraph (QVert V) → List (Obj (QVert V)) -- R10 (h): function of Q_l; Classical.choose default
```

Every round Spec is `∀ I, I.Valid → ∀ R : Rules I, R.Valid → …`. With these types, the (e2) junction is definitionally a function of `(I, R, L, ≺_u)`, so independence across ports is `iIndepFun` of coordinate projections of `ordersLaw`, and the uniform-3-subset step of Cuckoo is `perm_image_uniform` applied to the P-determined set `{3g, 3g+1, 3g+2}` (SCHED-UNIFORM-LEMMAS (2)). Nothing in `Rules` may take `Orders` except `rank`.

Record in the conventions file: "s7 fixed rules: argument types as above (manuscript v6 patch ROUND-RULE-DEPENDENCE, T1)."

---

## 6. Checklist of consumers examined

s7:consRound (a)–(h) incl. the Markov choice (f); s7:defSchedule; s7:lemWellDef (i)–(v); s7:lemMULT; s7:lemSimple; s7:lemLift (i)–(iv); s7:lemCC (i)–(iii); s7:lemUltra (i)–(iv); s7:lemVstar; s7:lemPay (a1)–(e); s7:defXprime; s7:lemEXprime; s7:lemUHsplit (i)–(iv); s7:lemOneOutcome; s7:propCost; s7:thmJVps; s7:thmHI; s7:thmMainProof; s7:remNonCirc; s6:lemJplus; s6:defJconsumer; s6:consOrder; s6:thmMIXC(a). Result: no consumer needs a forbidden dependence; four proofs (WellDef(iii), CC(i), Ultra(i), Pay(c)) plus the (e2) claim need the restriction and currently assert it without a definitional basis.
