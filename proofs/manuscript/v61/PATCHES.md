# Manuscript v6.1: the P2-triage patches

Date: 2026-09-26. Base: manuscript v6, at commit `4fcfe88` (the TeX is unchanged through `a1a08ff`).
Sources: `formal/work/p2/TRIAGE.md` §1a (patch set R included), `formal/work/p2/blocker_mint.md`, `formal/work/p2/blocker_rules.opus.md` §4 and `formal/work/p2/blocker_rules.fable.md` §4.

**Status: CANDIDATE proof, reviewed by AI only.** None of these patches has had any referee, AI or human. Every changed statement is marked "changed in v6.1 (P2 triage): no referee yet" in `s1:tabDAG`. TRIAGE.md §4 still asks for a targeted clean-room re-review of the patched lines (G0 pattern).

Invariants kept:
- No statement used downstream is weakened. (Corrected after the v6.1 referee review, see `FIXES.md`: the new statement of s6:lemJSLC, §4, is implied by but weaker than its v6 form, which named the proof-internal g_{Y,l}; it is the form its only consumer uses, and the sharper v6 bound remains proved in the proof. Also, the v6 meta-remark s3:thmT16s(c), §3, was false as written; it had no consumer and is corrected.)
- No constant changes. This includes the cost line 1085, 1091, 169, 369, 80, as well as 126, 745/739 and 338.
- Line numbers below refer to the v6.1 files.

`patch.diff` holds the full diff. Its base is `a1a08ff`, the last commit whose manuscript TeX is v6. See the note at the end.

---

## 1. M-INTEGER: M_l ∈ ℕ (TRIAGE §1a, blocker_mint.md §2–§4). Class T1

Defect: in v6, (R2) defined M_l as a real number, but M_l is used as a count in several places:
- K^JS_l = M_l² classes, with the label law giving K^JS_l·ρ_l = M_l^-2;
- the palettes [3M_l] and [4M_l];
- the bijections η_h : [4M_l] → [4M_l];
- the binomials binom(K, s−1);
- "M_l − 1 cherry systems" and ncl_l.

| # | File:line | Change | Rationale |
|---|---|---|---|
| 1a | s2.tex:518–527 (s2:defHBtp, (R2)) | `M_l := ⌈max(2^40, 2^16 T log^4 T)⌉ ∈ ℕ`. A new explanatory sentence says the ceiling makes M_l an integer, that Λ_l is the log of this integer, and that only two facts about the ceiling are used: M_l ≥ max(…) and M_l ≤ max(…)+1. | This is the repair of blocker_mint §2. The fallback "ceilings at each use" is rejected, because it would change the JS label law and s6:lemLost(i). |
| 1b | s2.tex:675 (proof of s2:lemCap(ii)) | "M_l = max(…)" becomes "M_l ≥ max(…)". | Wording (blocker_mint §3, s2 table). |
| 1c | s2.tex:952–958 (proof of s2:propDegRec, *Parameters*) | The proof uses x ≥ 21 + 6 log x (was 20), so max(2^40, B) ≤ 2^{20}x^6 2^x ≤ 2^{2x−1}. Then M_l ≤ 2^{2x−1} + 1 ≤ 2^{2x} = d_l². | The ceiling adds up to 1, and d_l² need not be an integer, so this line is genuinely needed. x ≥ 21 + 6 log x follows from x ≥ 2^14·105·log³x, just as the old 20 + 6 log x did. Every later line uses only log M_l ≤ 2x. |
| 1d | s3.tex:1248–1256 (proof of s3:lemCOLJV, standing bound (B6)) | Re-derived for the ceiling. Put B := 2^16 T log^4 T ≥ 2^{16+λ} > 2^161. Then M_r ≤ B+1, so Λ_r ≤ log B + 1/(B ln 2) ≤ log B + 2^-160 (justification corrected after the v6.1 review, `FIXES.md`). Also log B = 16 + λ + 2μ + 4 log(λ+2μ) and 4 log(λ+2μ) ≤ 4μ + 0.01 (because 2μ/λ ≤ 2^-240 for μ ≥ 2^8). So Λ_r ≤ λ + 6μ + 16.01 + 2^-160 ≤ λ + 6μ + 20. | The old proof took the log of the real max, so it had no room for the ceiling. The new chain has slack of about 4. The statement of (B6) and every row of Table s3:tabCOLJV are unchanged. |
| 1e | s1.tex:1861 (symbol table s1:tabSymbols) | The M_l entry now reads "M_l ∈ ℕ (a ceiling, (R2))". | Editorial. |
| 1f | notation.txt:64 | The M_l entry records the ceiling. | Keeps notation.txt in sync with the symbol table. |

Re-checked, no text change (blocker_mint §3):
- s2:propStructure, s2:lemTower, s2:propParentless;
- s1:condG2, s1:condG4;
- s3:defCOL, s3:lemCOL;
- s5:lemParent;
- s6:defDesign, s6:defLending, s6:lemLost, s6:lemJSLC, s6:lemJplus, s6:thmMIXC;
- all s7 uses.

Each of these is one of three kinds:
- a lower bound on M_l, preserved by M_l ≥ max(…);
- a consequence of M_l ≤ d_l² (1c), M_{l−1} ≥ 2M_l, M_l ≤ λ_{l−2}^{1.6}, or M_l ≥ 2^40;
- an integer statement that is now literally true, for example K^JS_l ρ_l = M_l^-2 exactly.

## 2. ROUND-RULES: declared arguments for the fixed rules of s7:consRound (TRIAGE §1a patch set R; opus §4a–4d; fable §4). Class T1

Wording reconciliation:
- The text follows TRIAGE R-1, which is the fable text merged with the opus corrections.
- (g) and (h) are **not** restricted: the rank order and Dec_l may read all of ξ_l, and they must, since Q_l does.
- The prohibition is on "the orders ≺_u **of ξ_l**", because Past_l contains the draws ξ_{l'} of rounds l' > l, orders included, and J_l depends on them.
- The blueprint sentence "none depends on the orders ≺_u" is **not** used.

| # | File:line | Change | Source |
|---|---|---|---|
| 2a | s7.tex:236–266 (s7:consRound, new paragraph *Fixed rules* before *Items*) | The rules and orders called fixed in (b)–(e) are deterministic functions, chosen before any randomness is drawn. **Functions of Past_l alone:** the pairing of the live J^fr items at a fresh centre and the unpaired fresh leg (b); the greedy PAR colouring order (b); the grouping of the live items of a non-ultra hub and the numbering of the groups (c). **Functions of Past_l and the lists (η_h, ζ_{h,u}):** the SDR choice (d); the processing order and the order of V(G) (e1); the order e_1..e_q of E'(u) (e2). None of these reads the orders ≺_u of ξ_l, which enter only through e_i ↦ w_i. Through Past_l the rules may depend on ξ_{l'} (l' > l), orders included. The rank order (g) and Dec_l (h) are unrestricted deterministic functions of Past_l and ξ_l. The paragraph also says that such rules exist (lex-first choices), that every round-step statement holds for every rule choice that obeys the restrictions, and where the restrictions are used. | TRIAGE R-1 = opus 4a = fable Patch 1 |
| 2b | s7.tex:314–316 (step (c)) | "…pairwise disjoint, and, since the groups and their numbering are functions of Past_l while η_h is independent of Past_l, they form a uniformly random sequence of…" | R-2 = opus 4b |
| 2c | s7.tex:345–347 (step (e2)) | "by the restrictions on the fixed rules, Used(u), the set E'(u) and its order e_1,…,e_q are determined by Past_l and the lists, and the orders ≺_u are independent of both." | R-3 = opus 4c = fable Patch 2 |
| 2d | s7.tex:472–476 (proof of s7:lemWellDef(iii)) | Adds "(the grouping rule of step (c) reads Past_l only, by the restrictions on the fixed rules in Construction s7:consRound)". | R-4 = opus 4d = fable Patch 3 |
| 2e | s7.tex:738–742 (preamble of the subsection "Quotient size and payments") | "steps (a)–(d) and (e1) of Construction s7:consRound, the sets E'(u) and their orders e_1,…,e_q are determined (by the restrictions on the fixed rules), and only the orders ≺_u are random." | R-6 = fable Patch 4 |
| 2f | s7.tex:797–801 (proof of s7:lemCC(i)) | "With the past and the lists fixed, Cand_l(x) \ Used(x), E'(x) and its order are fixed for every port x (restrictions on the fixed rules in Construction s7:consRound), so the junction of the κ-end at a port x is a function of ≺_x alone…" | R-5 = fable Patch 5. The text uses Cand_l(x)\Used(x) rather than C(x), because C(·) is defined only later in that proof. |

Not applied: fable Patch 6 (defSchedule cross-reference), which is optional and not in TRIAGE's set R.

Why the restriction is load-bearing: without it, adversarial rules falsify the claims.
- A grouping that reads η_h makes SDR failure almost sure (opus §3(A), fable §3.1).
- An (e2) order that reads ≺_u steers junctions (opus §3(B), fable §3.2–3.4).

With the restriction, every statement is true as stated.

## 3. T16-C-META (TRIAGE §1a). Class T1, wording

| # | File:line | Change | Rationale |
|---|---|---|---|
| 3a | s3.tex:822–824 (s3:thmT16s item (c)) | Now reads: "Apart from Step 0 of the proof below, which uses the full hypothesis on s to obtain N ≥ 2^30, ρN ≥ 84 and e^{−ρN/8} ≤ N^{−3} (through (b)), the proof uses only s ≥ 2K_*(θ_*+1)…". | The old meta-claim "the proof uses only s ≥ 2K_*(θ_*+1)" was false as written: the preliminary step uses s < N together with s ≥ 2^135 tL^28 ρ^-5. No consumer uses (c). |
| 3b | s3.tex:838 (proof) | The preliminary paragraph is now headed "Step 0: N and ρN are large." | The reference in (c) now has a target. |
| 3c | s3.tex:894–897 (proof, paragraph "For (c)") | Adds the same qualification: Step 0's consequences are used in Step 4 (N ≥ 2^30, ρN ≥ 84) and in Step 5 (e^{−ρN/8} ≤ N^{−3}, via (b)). | Consistency. |

## 4. JSLC-G-UNDEFINED (TRIAGE §1a). Class T1, wording

| # | File:line | Change | Rationale |
|---|---|---|---|
| 4a | s6.tex:450–452 (statement of s6:lemJSLC) | The bound is now `126 n/M_l + 1.5 Σ_{(Y,l) giant} m_{Y,l}` cycles. The statement says the sum is over the Y with (Y,l) giant (s6:defDesign) and that m_{Y,l} is the maximal class-Y degree (s6:defDesign). The definition of sc_{Y,l} = (3g_{Y,l} − 6M_l)^+, and the reference to g_{Y,l} ("Step 5 of the proof"), are removed from the statement. | The v6 statement referred to g_{Y,l}, an object that exists only inside the proof. The new bound is implied by the old one, because sc ≤ 1.5 m. It is exactly the form used by the only consumer. It is weaker than the v6 form; the sharper bound 15n/M_l + Σ_giant sc remains proved (paragraph *The sharper bound* at the end of the proof, added after the v6.1 review, `FIXES.md`). |
| 4b | s6.tex:539 (proof, Step 5) | sc_{Y,l} := (3g_{Y,l} − 6M_l)^+ is defined here and marked local to the proof. g = sc = 0 if R_Y has no giant component. | Moves the symbol into the proof. |
| 4c | s6.tex:543 (proof, end of Step 5) | Adds: a giant component of R_Y lies in a giant component of Bead_{Y,l} (Step 3), so sc_{Y,l} = 0 unless (Y,l) is giant. | This justifies summing only over giant pairs. |
| 4d | s6.tex:605 (proof, Step 8) | The final line uses sc ≤ 1.5 m (Step 5) and 15 ≤ 126 to conclude the new form. | This proves the statement as now stated. |
| 4e | s6.tex:860 (proof of s6:thmMIXC(c), the O_S line) | The sum is written with 1.5 Σ_giant m in place of Σ_giant sc. The right-hand side 252n/D_* + 1.5 Σ m is unchanged. | This is the only consumer (checked). The constant 126, and hence 252/D_* in ε_M, are unchanged. |
| 4f | s1.tex:1914; notation.txt:99 | The symbol-table rows for sc_{Y,l}, g_{Y,l}, S_0(Y,l) now say "local to the proof" and "defined in: s6:lemJSLC (proof)". | Sync. |

## 5. Cosmetic T1 items (TRIAGE §1a) and the optional standing assumption

| # | File:line | Change | Rationale |
|---|---|---|---|
| 5a | s1.tex:897–901 (s1:citLem14, sketch of the proof in [BM]) | Adds a justification of (9). For n ≥ 3 it follows from log n_1 < log n − 2/5: 2/(2+log n_1) − 2/(2+log n) > 0.8/(2+log n)² ≥ 1/(10 log² n), because log n ≥ log 3 > 2/(2√2 − 1). For n = 2, (7) gives n_1 = 1 and (9) reads 1 > 2/3 + 1/10. | L14-INEQ9: the quoted chain yields (9) only for log n > 1.09. |
| 5b | s6.tex:229 (proof of s6:lemHCCglob) | The proof now cites "the argument of the proof of Fact s1:factAdd(b) (concatenation of decompositions of disjoint edge sets)". It also notes that the statement of factAdd(b) is the corresponding bound on f. | GLOB-FACTADD-MISCITE: factAdd(b) is a bound on the minimum f. The step used is concatenation. |
| 5c | s2.tex:24–29 (introduction of s2) | New paragraph *Standing assumption*: D_* is the constant of s1:defConstants(iii) and satisfies Γ1–Γ4. The paragraph cites the termination part of s2:propExists (through s2:propDegRec, hence Γ1) as an example. | Optional wording (EX-GAMMA-NEEDED / MAIN-PROPEXISTS-HYPS, T0). s5.tex:9 and s7.tex:10 already have such a sentence. This is not a weakening: D_* is by definition such a constant. |

## 6. Status text, dependency table, outline

| # | File:line | Change |
|---|---|---|
| 6a | s1.tex:44–46, 56–59 (abstract) | "This is version 6.1 …". Adds a sentence: v6.1 applies the repairs of the Lean-formalization triage; no statement used downstream weakened (lemJSLC restated in its consumer's form; wording corrected after the v6.1 review, `FIXES.md`), no constant changed; no referee yet. |
| 6b | s1.tex:345–382 (s1:remStatus(iii)) | New closing paragraph *Version 6.1 (P2 triage)*, listing changes (1)–(5), stating that they have had no referee of any kind, and pointing to this file. |
| 6c | s1.tex:2103–2112 (legend of s1:tabDAG in s1:ssecDAG) | The "no referee yet" sentence now covers the v6.1 changes. Adds the definition of the marker "changed in v6.1 (P2 triage): no referee yet". |
| 6d | s1.tex, s1:tabDAG rows (marker appended to the status cell) | Rows marked: s1:remStatus (2256), s1:citLem14 (2280), s2:defHBtp (2339), s2:lemCap (2352), s2:propDegRec (2357), s2:propExists (2369), s3:thmT16s (2405), s3:lemCOLJV (2408), s6:lemHCCglob (2487), s6:lemJSLC (2504), s6:thmMIXC (2510), s7:consRound (2526), s7:lemWellDef (2527), s7:lemCC (2542). |
| 6e | s1.tex:2280, 2420 | Two tabDAG tabular blocks are split, before the rows s1:citLem14 and s3:lemCOLJVev. The longer status cells had made two blocks overflow the page (overfull \vbox). |
| 6f | s7.tex:1612–1618 (subsection "What is not established") | Adds a sentence on v6.1: its patches, no referee yet, and the marker. |
| 6g | ms.tex:14–17, 251 | Header comment for v6.1; `\date{Version~6.1, 26 September 2026}`. |
| 6h | outline.txt | Kept in sync. Changes: header legend; abstract item (8); s1:remStatus(iii) closing paragraph; s1:citLem14 (9); s1:ssecDAG legend; s2 standing assumption; (R2); s2:lemCap proof; s2:propDegRec proof line; s3:thmT16s(c); s3:lemCOLJV (B6); s6:lemHCCglob; s6:lemJSLC statement; s6:thmMIXC; s7:consRound (*Fixed rules*, (c), (e2)); s7:lemWellDef(iii); s7:lemCC; s7:ssecNotEstablished. The RC tags equal the new tabDAG status cells. |
| 6i | notation.txt:64, 99 | See 1f and 4f. |

Labels whose text changed: s2:defHBtp, s2:lemCap (proof), s2:propDegRec (proof), s3:lemCOLJV (proof), s3:thmT16s, s6:lemJSLC, s6:thmMIXC (proof), s6:lemHCCglob (proof), s7:consRound, s7:lemWellDef (proof), s7:lemCC (proof), s1:citLem14 (sketch), s1:remStatus, and s2:propExists (by the section's standing assumption only). The following unlabelled text also changed: the abstract, s1:ssecSymbols (tabSymbols), s1:ssecDAG (legend), the s2 introduction, the s7 subsection preamble "Quotient size and payments", and s7:ssecNotEstablished.

## 7. Compilation

- pdflatex ×3 in a scratch directory outside the repository.
- 0 errors, 0 LaTeX warnings, 0 undefined references.
- 4 overfull \hbox, the same set as in v6.
- **172 pages** (v6: 169). The growth comes from the *Fixed rules* paragraph, the remStatus/abstract text and the two extra tabDAG blocks.
- The PDF was copied to `proofs/manuscript/EG_candidate_proof_v6.pdf` and `proofs/manuscript/ms.pdf`.

## Note on the diff base

During this work, other sessions made commits on the branch (`18e3800 WIP`, `73224ce WIP: agent outputs`, `fbefc0b …`). They swept the in-progress v6.1 edits of the manuscript files into git. This session ran no git command that modifies the repository. So `git diff HEAD` no longer shows the v6.1 changes.

`patch.diff` is therefore `git diff a1a08ff -- proofs/manuscript/{ms.tex,s1..s7.tex,outline.txt,notation.txt}` against the working tree. `a1a08ff` is the last commit before any v6.1 edit, and its manuscript TeX is identical to v6 (`4fcfe88`).
