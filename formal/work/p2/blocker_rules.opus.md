# Blocker ROUND-RULE-DEPENDENCE — resolution (s7:consRound and consumers)

Source read: `proofs/manuscript/s7.tex` in full, `s6.tex` (defDesign, lemJplus, defJconsumer, consOrder, lemLent),
the `fixed rule` conventions in s4/s5, `formal/work/p2/blueprint_s7a.md` (hazards ROUND-RULE-DEPENDENCE,
SCHED-RULE-DEPENDENCE, CC-CONDITIONING, WD-SDR-INDEP-SIMPLE) and `blueprint_s7b.md` (PAY-C-CONDITIONING).

**Verdict: T0 (wording/encoding). There is no T2 or T3 conflict.** The intended construction satisfies the
restriction, and no use needs a round-l rule in (b)–(e2) to read the round-l orders ≺_u, or needs the grouping to
read η. The manuscript already asserts the needed determinacy where it is used, except for one item that is only
implicit: the order e_1..e_q of E'(u) in (e2).

**The blueprint's proposed sentence is itself wrong as written, and must not be adopted verbatim.** "Every fixed rule
and fixed order below is a function of Past_l and, from step (d) on, of the lists; none depends on the orders ≺_u"
conflicts with the manuscript twice:
1. **(g)/(h) conflict.** The rank order of (g) is a "fixed order", Dec_l in (h) is chosen "by a fixed deterministic
   rule", and both come after step (d). Both must depend on the round-l orders, because their domains (the edges of
   the layers, E(Q_l)) are built from the junctions chosen by ≺_u in (e2). The sentence forbids exactly this.
2. **Earlier-round orders.** Past_l contains ξ_{l'} (l'>l), including the orders ≺_u of those earlier rounds. J_l
   depends on them: J_l comes from JS-LC on EQ(Z) ⊆ Erem(Z) = E_l(Z)\Lent(Z), and Lent(Z) ⊇ LentJV(Z) is made of
   junction edges on lifted cycles of rounds l' ≥ l+2 (s6:consOrder, s6:lemLent). So every round-l rule depends on
   earlier orders through its input (the live items, c_h^live, ultra status, …). A bare "none depends on the orders
   ≺_u" read over all rounds contradicts "is a function of Past_l". The restriction must say "the orders of ξ_l".

The corrected text is in §4. The Lean argument types are in §5.

---

## 1. The fixed rules: what they are, where they are chosen, what their domain depends on

Round l, with Past_l fixed. ξ_l = (Lists, Orders), where Lists = (η_h)_h, (ζ_{h,u})_{h,u} and Orders = (≺_u)_u.

| # | Rule (s7:consRound) | Domain it acts on | Domain depends on | Needs to read | Must NOT read |
|---|---|---|---|---|---|
| R1 | (b) pairing of live J^fr items at fresh centre x into cherries | live J^fr items at x | past (J_l, Pool_l, JV-bad) | past | ξ_l (lists harmless, orders not) |
| R2 | (b) choice of unpaired fresh leg | same | past | past | ξ_l |
| R3 | (b) order of the greedy PAR colouring (so the colouring) | PAR objects | past | past | orders of ξ_l (lists harmless) |
| R4 | (c) grouping of the live items of a non-ultra h into k_h groups + numbering of the groups (group i gets η_h(3i−2..3i)) | live items of h; ultra status from c_h^live | past | past | **η** (and ξ_l generally) |
| R5 | (d) SDR choice at u (when an SDR exists) | live hub items at u + their lists | past + lists | lists (unavoidable) | orders of ξ_l |
| R6 | (e1) processing order of coloured non-ultra hub items | coloured items | past + lists (via SDR) | lists (domain) | orders of ξ_l |
| R7 | (e1) "fixed order of V(G)" | V(G) | – | nothing | orders of ξ_l |
| R8 | (e2) order e_1..e_q of E'(u) | PAR ends at u + coloured ultra-hub items at u | past + lists (SDR decides which ultra items are coloured) | lists (domain) | orders of ξ_l (not even ≺_u) |
| R9 | (g) rank order of parallel edges in a layer | edges of the layers | past + lists + **orders** (junctions) | orders (domain) | nothing |
| R10 | (h) Dec_l, a decomposition of E(Q_l) of size f(Q_l) | E(Q_l) | past + all of ξ_l | orders (domain) | nothing |
| (R0) | designation δ, JS-LC choices, Dec_{l'} (l'>l) | – | fixed before stage 1 (δ: "any deterministic function of the run", s6:defDesign) / in the past | – | – |

(e3), (f) and the ultra/non-ultra test (c_h^live > thult_l) involve no free choice. The ultra test is a function of the
past, because liveness comes from (a) only.

## 2. What each consumer needs

In each case the "Needs" column is what the proof text itself asserts or uses.

* **s7:lemWellDef(iii) (Cuckoo SDR), and so s7:lemPay(c) first bound.** The proof says: "With Past_l fixed, it is
  determined which hubs are ultra, how the items are grouped, and which group each item belongs to." It then uses
  that the list of (h_i,u) is the image of a fixed 3-set under η_{h_i}, so the lists are independent uniform 3-sets.
  *Needs:* R4 is a function of the past only. Ultra status is a function of the past, which is automatic. R5 is
  irrelevant here, because the failure event does not depend on which SDR is chosen.
* **(c)'s own claim** "they form a uniformly random sequence of k_h pairwise disjoint 3-subsets". *Needs:* R4 does
  not read η_h.
* **(e2)'s own claim** "With Past_l and the lists fixed, e_i ↦ w_i is a uniformly random injection …, independent
  over ports: Used(u) is determined by Past_l and the lists, and ≺_u are independent of both." *Needs:* Used(u)
  (R3, R5, R6, R7), the set E'(u) (R1–R3, R5) and **its order e_1..e_q (R8)** are all functions of past + lists.
  The text justifies only Used(u). The order is the implicit item.
* **Subsection preamble** ("Then steps (a)–(d) and (e1) … are determined, and only the orders ≺_u are random")
  asserts that R1–R7 are functions of past + lists.
* **s7:lemCC.** (i) "with the past and the lists fixed, the junction of the κ-end at x is a function of ≺_x alone".
  *Needs:* which end at x is the κ-end (R1, R3), C(x) (R5–R7) and the position of that end in E'(x) (R8) are
  functions of past + lists. The closing sentence "for every outcome of the lists, the SDR and the greedy step (e1):
  only the orders ≺_u are random" states exactly this.
* **s7:lemUltra (i)–(iv).** *Needs:* the set of coloured items of h of colour κ (R5) and their positions in E'(u_i)
  (R8) are functions of past + lists.
* **s7:lemPay(c) loop bound** ("Fix the lists … junctions independent, the one at q uniform"). *Needs:* R8 at p and
  at q are functions of past + lists.
* **s7:lemUHsplit(ii).** Non-ultra copies and junction copies are bounded deterministically for every outcome, and
  the rest is CC(iii) and Ultra(iv). Then "averaging over the lists". *Needs:* only what CC and Ultra need.
  |V(Q_l)| does not depend on R9 (by the second statement of s7:lemMULT, the copy count is max-multiplicity),
  so R9 is unrestricted.
* **(f) Markov choice / s7:lemOneOutcome (iii) / s7:thmJVps / s7:remNonCirc(3).** These need only that
  copies_l and pay_l are functions of (Past_l, ξ_l) once the rules are fixed, and that the rules are fixed *before*
  ξ_l is chosen in the event (rule first, then outcome). They impose no restriction on the argument types. R9 and
  R10 may read all of ξ_l, and R10 must. The chosen ξ_l then enters Past_{l−1}.
* **s6 consumers (s6:defJconsumer, s6:consOrder, s6:thmMIXC, s6:lemLent).** The J-consumer is "a rule … given
  everything constructed at rounds >l, the stage-1 outcome and J_l (and possibly fresh randomness)". This is fully
  compatible. JC1–JC3 and the Lent bookkeeping are deterministic, per-outcome properties (s7:lemLift holds "for any
  past, any ξ_l"). δ is fixed as a function of the run (s6:defDesign), which Ex|Cand_l(u)| and E X′ need. That is
  already explicit.
* **Existence (inhabitedness).** s7:lemOneOutcome and s7:thmJVps need *some* admissible rule family. Lex-first
  choices with the restricted arguments exist: a pairing always exists; the greedy colouring succeeds by WellDef(i);
  a grouping exists because k_h⌈Hcd/8⌉ ≥ c_h; the SDR choice is "some SDR if one exists"; orders are arbitrary.
  **No use needs anything outside the restricted class.**

## 3. The restriction is load-bearing (so this is a real gap, not pedantry)

Under the permissive reading ("fixed rule" = any deterministic function of everything, including ξ_l), the
following claims are false for some admissible past. So the Lean `Rules` argument types must encode the
restriction.

**(A) Grouping reads η ⇒ WellDef(iii) and Pay(c) (first bound) fail, with failure probability → 1.** Let K = 4M.
Take a past with a port u carrying m = M−1 live items at distinct non-ultra hubs h_1..h_m, each with
c_{h_i}^live ∈ ((M−1)Hcd/8, M·Hcd/7]. Then k_{h_i} ≥ M and h_i is non-ultra.
* Rule: let S = [m−1] (|S| = M−2). If some group triple T_j of η_{h_i} satisfies T_j ⊆ S, put (h_i,u) into the
  first such group. To keep sizes ≤ ⌈Hcd/8⌉, swap it with an item of that group.
* Probability: for j ≤ M/8, given T_1..T_{j−1}, P(T_j ⊆ S) ≥ ((5M/8 − 5)/(4M))^3 ≥ 1/343. So
  P(no T_j ⊆ S) ≤ exp(−M/2744).
* Result: with probability ≥ 1 − M·exp(−M/2744) (≈ 1, since M ≥ 2^40), all m lists lie in S. By Hall, SDR
  failure is certain, far above (4M)^{−4}. Each such port pays M−1 items, so the payment can be Θ(n·M_l) per round
  instead of O(n/M_l^3).

**(B) (e2) order at u reads ≺_u ⇒ CC(i) and Ultra(i) fail.** At a port v with q ≥ 2 ends in E'(v), one of which
is a given end e:
* Rule: put e at position i if the i-th ≺_v-element of C(v) is a target w' and i ≤ q.
* Result: P(e → w') ≥ q/|C(v)| ≈ 2q/Hcd. For q ≥ 2 this exceeds CC(i)'s "at most 3/Hcd". The same rule makes
  the junction of an ultra item non-uniform, against Ultra(i).
* If the order at q also reads ≺_p, the loop probability of a PAR object p–q becomes ≈ q/|C(p)| (align q's end
  with p's junction when it is among q's first q candidates), against Pay(c)'s 2/Hcd.
* Note: with only per-port self-reading, the loop bound alone survives (Σ_w P(p→w)P(q→w) ≤ max_w P(p→w)). The
  cross-port read is what breaks it.

**(C) (b) colouring reads ξ_l ⇒ CC(i)'s structural claim fails.** "The κ-end at x is a function of ≺_x alone"
fails, because which object at x has colour κ then depends on other ports' orders.

The numerical endpoints (Pay(d), UHsplit(iv)) have large slack in cases (B) and (C). Case (A) breaks them outright.
In every case the lemma statements, read with the intended restriction, are true (verified: every proof step in §2
goes through). This is why the class is T0 and not T2: the prover fixes the rules, restricted rules exist (§2),
and every lemma is proved for them.

## 4. Replacement text (manuscript, T0 clarification)

**4a. Insert in s7:consRound**, as a new paragraph right after "with the properties \Jp{1}--\Jp{3} and (i)--(v) of
Lemma~\ref{s6:lemJplus}." (before *Items.*):

```tex
\emph{Fixed rules.} The rules and orders called fixed in steps (b)--(e) below
are deterministic functions, chosen before $\xi_l$ is drawn, with the following
arguments. The pairing of the fresh legs and the choice of the unpaired fresh
leg, the order of the greedy colouring of the PAR objects in (b), and the split
of the live items of a non-ultra hub into groups together with the numbering of
the groups in (c) are functions of $\Past_l$ alone. The choice of the system of
distinct representatives in (d), the processing order and the order of $V(G)$
in (e1), and the order $e_1,\dots,e_q$ of $E'(u)$ in (e2) are functions of
$\Past_l$ and the lists, that is, of the variables $\eta_h$ and $\zeta_{h,u}$ of
$\xi_l$. None of these rules depends on the orders $\prec_u$ of $\xi_l$. Through
$\Past_l$ they may depend on the draws $\xi_{l'}$ of the rounds $l'>l$, and in
general they do, since $J_l$ does. The rank order in (g) and the rule choosing
$\Dec_l$ in (h) are not restricted; they depend on $\xi_l$ through $Q_l$. Rules
with these arguments exist, for instance lexicographically first choices for
fixed orders of the finite sets involved.
```

**4b. In (c)**, replace
"The lists of the groups of $h$ are pairwise disjoint, and they form a uniformly random sequence of"
with
"The lists of the groups of $h$ are pairwise disjoint, and, since the groups and their numbering are functions of
$\Past_l$ while $\eta_h$ is independent of $\Past_l$, they form a uniformly random sequence of"

**4c. In (e2)**, replace
"$\Used(u)$ is determined by $\Past_l$ and the lists, and the orders $\prec_u$ are independent of both."
with
"$\Used(u)$, the set $E'(u)$ and its order $e_1,\dots,e_q$ are determined by $\Past_l$ and the lists (by the
paragraph on fixed rules), and the orders $\prec_u$ are independent of both."

**4d (optional). In the proof of s7:lemWellDef(iii)**, after "and which group each item belongs to", add
"(the grouping is a function of $\Past_l$ alone)".

Nothing else changes. No statement is weakened, and no constant or consumer is affected.

## 5. Lean encoding (replaces the blueprint's Rules row)

`Rules I` (I : RoundInput = Past_l, which contains stage 1, stage 3, and ξ_{l'} for l'>l, but **not** ξ_l):

| field | type (schematic) | Valid |
|---|---|---|
| freshPairing | `Past → (x : FreshCentre) → Pairing (liveFr x)` | perfect on all but ≤1 leg |
| unpairedLeg | folded into freshPairing | – |
| parOrder | `Past → LinearOrder PARObj` (colouring := greedy along it) | – (WellDef(i) proves success) |
| hubGroups | `Past → (h : NonUltra) → Fin k_h ↪ …` (group index of each live item) | k_h groups, sizes ≤ ⌈Hcd/8⌉ |
| sdrChoice | `Past → Lists → (u : Port) → Option SDR` | returns some SDR iff one exists |
| e1Order | `Past → Lists → LinearOrder ColouredNonUltraItem` | – |
| vertOrder | `Past → Lists → LinearOrder V` (or a constant order) | – |
| e2Order | `Past → Lists → (u : Port) → LinearOrder (E' u)` | – |
| rankOrder | `Past → Xi → …` (unrestricted) | – |
| decChoice | `Past → Xi → …` or `(Q : SimpleGraph) → Decomp Q` | size = f(Q) |

* Every Spec is `∀ R : Rules I, R.Valid → …`, as in blueprint decision 7.
* Add `Rules.exists_valid : ∃ R : Rules I, R.Valid` (lex-first; uses WellDef(i),(ii)), which s7:lemOneOutcome
  consumes.
* The blueprint's summary sentence and table (lines 30, 47, 53, 400, 428, 511 of `blueprint_s7a.md`) should cite
  §4a above instead of "none depends on the orders ≺_u", which is inconsistent with (g)/(h) and with Past_l.
* Class: **T0** (record in the conventions file; manuscript clarification §4 optional per PLAN §7). The blocker is
  resolved: the argument types above are the decision.
