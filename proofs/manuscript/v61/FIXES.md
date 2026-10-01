# Manuscript v6.1: fixes after the clean-room referee review

Date: 2026-09-26. Reviews: `review.opus.md` and `review.fable.md`, both by clean-room AI referees. Each non-cosmetic finding below was checked independently before it was fixed.

**Status: CANDIDATE proof, reviewed by AI only.** These fixes have not been re-reviewed.

Invariants:
- No constant changes. This includes the cost line 1085, 1091, 169, 369, 80, as well as 126.
- No mathematical content of any statement is changed. The only change inside a statement is the wording of the meta-remark s3:thmT16s(c) (cosmetic).
- No git command that modifies the repository was run.

## Findings

### F1. (B6) in the proof of s3:lemCOLJV: "B > 2^160, so log(1+1/B) ≤ 2^-160". Minor. **Fixed.**

Check: the finding is valid. log₂(1+1/B) ≤ 1/(B ln 2). So B > 2^160 alone gives only a bound of about 1.443·2^-160.

The conclusion is true. T = λ²2^λ, so log T = λ + 2μ ≥ 1, and B = 2^16 T log⁴T ≥ 2^{16+λ} > 2^161. Hence 1/(B ln 2) < 2^-161/0.69 < 2^-160.

Fix, in s3.tex, (B6):
- The text now states B ≥ 2^16 T ≥ 2^{16+λ} > 2^161 ≥ 2^40.
- The chain now reads log(1+1/B) ≤ 1/(B ln 2) ≤ 2^-160, with the justification 1/(B ln 2) < 2^-161/0.69 < 2^-160.

The statement of (B6), the final bound λ + 6μ + 20 (slack about 4) and Table s3:tabCOLJV are unchanged. outline.txt and PATCHES.md §1d were synced.

### F2. Bookkeeping claims in s1:remStatus(iii), the abstract and PATCHES.md "Invariants kept". Minor. **Fixed.**

Check: both parts are valid.

(1) The v6 conclusion of s6:lemJSLC was 126n/M_l + Σ sc_{Y,l}. Since sc_{Y,l} ≤ (1.5m_{Y,l} − 12)^+ ≤ 1.5m_{Y,l}, the v6.1 conclusion 126n/M_l + 1.5 Σ_giant m_{Y,l} is implied by it but does not imply it. So "no statement is weakened" was literally false. It is mathematically harmless:
- the v6 form named g_{Y,l}, which exists only inside the proof;
- the only consumer, s6:thmMIXC(c), uses the new form;
- the proof still establishes the sharper bound.

(2) "Found no false statement" contradicted PATCHES.md §3a. The v6 meta-remark s3:thmT16s(c) was false as written. It had no consumer.

Fix:
- **Abstract (s1.tex):** now says "no constant changes, no statement used downstream is weakened (Lemma s6:lemJSLC, whose statement named an object internal to its proof, is restated in the form its only consumer uses)".
- **s1:remStatus(iii), opening:** the triage "found no fatal error and no false statement on which the proof relies". The paragraph states that the meta-remark s3:thmT16s(c) was false as written and had no consumer. It states that the only statement whose new form is weaker is s6:lemJSLC, and that the sharper v6 bound remains proved.
- **s1:remStatus(iii), items (3) and (4):** (3) now says the meta-remark is "corrected". (4) says the new form is implied by, but weaker than, the v6 bound, and that the sharper form 15n/M_l + Σ sc_{Y,l} remains proved.
- **s7.tex, s7:ssecNotEstablished:** matching wording.
- **PATCHES.md:** the "Invariants kept" line and rows 4a and 6a are corrected, and each correction points to this file.
- **outline.txt:** the header legend, the abstract item, the remStatus paragraph and the s7:ssecNotEstablished item are synced.

### F3. Paragraph *Fixed rules* of s7:consRound contradicts itself. Minor. **Fixed.**

Check: the finding is valid, as a literal reading.
- Bullet 3 said that the orders ≺_u of ξ_l enter the construction "only through e_i ↦ w_i". Bullet 4 lets (g) and (h) read all of ξ_l.
- The opening sentence limited the paragraph to the rules "called fixed in steps (b)–(e)". But step (g) ("listed in a fixed order") and step (h) ("a fixed deterministic rule") also use fixed rules, and bullet 4 governs them.

Fix, in s7.tex:
- The opening now reads "The rules and orders called fixed in steps (b)–(e), (g) and (h) below…".
- Bullet 3 now reads "None of the rules of steps (b)–(e) reads the orders ≺_u of ξ_l; within steps (a)–(f), the orders ≺_u of ξ_l enter only through the assignment e_i ↦ w_i of (e2) (and through what is computed from it)." The parenthesis covers the loops of (e3) and the quantities of (f), which are computed from the junctions.

The meaning is unchanged, and it agrees with the cited uses: s7:lemCC(i), s7:lemUltra(i) and s7:lemPay(c) all rely on "nothing before the assignment e_i ↦ w_i reads the orders ≺_u". outline.txt was synced.

### F4. The v6.1 conclusion of s6:lemJSLC is weaker than the v6 one. Minor. **Fixed.**

This is the same issue as F2(1), and the finding is valid. On top of the rewording under F2, the proof now records the sharper bound. A new closing paragraph, *The sharper bound*, follows "On the constant" in the proof of s6:lemJSLC. It says:
- Step 8 proves at most 15n/M_l + Σ_giant sc_{Y,l} cycles, where sc_{Y,l} = (3g_{Y,l} − 6M_l)^+ ≤ (1.5m_{Y,l} − 12)^+ (Step 5);
- this was the v6 conclusion, which referred to the proof-internal g_{Y,l};
- the stated bound follows from it and is the form used by the only consumer, s6:thmMIXC(c), and nothing downstream uses the sharper bound.

The statement of the lemma is unchanged. The referee's option to state it with Σ_giant (1.5m − 12)^+ was not taken, because it is still weaker than v6 and no consumer needs it. The constant 126, and hence 252/D_* in ε_M, are unchanged. The existing tabDAG marker of s6:lemJSLC ("changed in v6.1 (P2 triage): no referee yet") already covers the proof. outline.txt (s6:lemJSLC entry) was synced.

## Cosmetic findings

| ID | Location | Status |
|---|---|---|
| opus c1 | s2.tex (R2), the ceiling sentence | **Fixed.** It now reads "Besides integrality, only two facts about the ceiling are used". |
| opus c2 = fable F7 | s3:thmT16s(c) | **Fixed.** It now reads "…to obtain (b), N ≥ 2^30 and ρN ≥ 84 (from (b), Step 5 then draws e^{−ρN/8} ≤ N^{−3})". This matches the proof: Step 0 derives (b), and Step 5 derives the exponential bound from it. The "For (c)" paragraph of the proof was already accurate. outline.txt was synced. |
| opus c3 | s6:lemHCCglob proof, "applied q−1 times" | **Not changed.** The phrase is redundant but correct, and the referee marked it optional. |
| fable F2 | (B6) | Same as F1 above. **Fixed.** |
| fable F3 | *Fixed rules*, bullet 3 | Same as F3 above. **Fixed.** |
| fable F4 | s6.tex, end of Step 5 of the proof of s6:lemJSLC | **Fixed.** Step 3 defines "giant component" only for R_Y, so the text no longer says "then so does Bead_{Y,l}". It now says "the component of Bead_{Y,l} containing it has more than 2γ_l edges (Step 3), so (Y,l) is giant". Step 3 shows that each component of R_Y lies inside a component of Bead_{Y,l} with at least as many edges. |
| fable F5 | *Fixed rules*, the list of uses | **Fixed.** Two uses are added: the opening paragraph of the subsection "Quotient size and payments", and the proof of s7:lemUHsplit(ii), where the copies of non-ultra hubs are deterministic given the lists. Both uses were checked in the text. outline.txt was synced. |
| fable F6 | outline.txt, entry s6:lemJSLC | **Fixed.** The bound is now g_{Y,l} ≤ m_{Y,l}/2 + 2M_l − 4, as in s6.tex. |

## UNRESOLVED

None. No finding is major or fatal. All four are minor: a gap in one justification, where the conclusion is true with slack, and three bookkeeping or wording issues. None needed a change to any statement or constant.

## Compilation

- pdflatex ×3 in a scratch directory outside the repository.
- 0 errors, 0 LaTeX warnings, 0 undefined references.
- 4 overfull \hbox, the same set of paragraphs as in v6.1 (line numbers shift by the added lines); no overfull \vbox.
- **173 pages** (v6.1: 172). The growth comes from the added text: *The sharper bound*, the list of uses in *Fixed rules*, and the remStatus wording.
- The PDF was copied to `proofs/manuscript/ms.pdf` and `proofs/manuscript/EG_candidate_proof_v6.pdf`.

## Files changed

- `s1.tex`: the abstract; s1:remStatus(iii).
- `s2.tex`: the ceiling sentence in (R2) of s2:defHBtp.
- `s3.tex`: (B6) in the proof of s3:lemCOLJV; the wording of s3:thmT16s(c).
- `s6.tex`: the paragraph *The sharper bound* in the proof of s6:lemJSLC; the wording at the end of Step 5.
- `s7.tex`: the paragraph *Fixed rules* of s7:consRound (its scope, bullet 3 and the list of uses); s7:ssecNotEstablished.
- `outline.txt`: synced.
- `v61/PATCHES.md`: the invariant and rows 1d, 4a, 6a.
- This file.
