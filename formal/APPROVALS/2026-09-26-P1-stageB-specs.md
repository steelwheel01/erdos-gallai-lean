# 2026-09-26 — P1 stage-B statements: approval

**Scope:** EG.Spec.Quot.HI (HIHyp, HIStatement = s7:thmHI), EG.Spec.HB.Cap (s2:lemCap (i) and the
graph-level consequence), EG.Spec.Ext.BMLemma25 (s1:citLem25 with T0-cap-1: extra hypothesis
2 ≤ m, necessary — the literal statement is false at m = 1 for large ε, `EG.bmLemma25_literal_false`
— and harmless), EG.Spec.Link.L15 (s3:lemL15p; per-colour bound 1 − 2N⁻⁵ and joint bound
1 − 2kN⁻⁵, as in the manuscript).

**Reviews.** Authoring reviews in P1b stage B (wf_bb8deba0-ade; formal/work/p1b/*.review*.md, all
approve). Final independent approval (wf_48be0a7c-1f0), reviewing from scratch with scratch Lean
tests (formal/APPROVALS/reviews/<group>.<opus|fable>.md):

| Group | Opus | Fable (different model) | Blocking |
|---|---|---|---|
| hi | approve-with-notes | approve | none |
| cap | approve-with-notes | approve | none |
| l15 | approve | approve-with-notes | none |

Notes (non-blocking): HIStatement generalises the constants to arbitrary reals (stronger than the
manuscript; c ≥ 0 proved); at n = 0 Lean's 0/0 = 0 makes a harmless instance satisfiable; the joint
Lemma 15⁺ bound must not be paraphrased as per-colour; colours are Fin k; downstream variable k
needs `NeZero k`; `decide` instance hygiene for colour classes; the later proof of B–M Lemma 25 needs
ε ≤ log²m, left implicit by B–M. Checked by a reviewer: every manuscript use of Lemma 15⁺ uses the
joint bound.

**Decision:** approved; locked together with the stage-A scope
(APPROVALS/2026-09-26-P1-foundations.md) by `scripts/lock.py update` (all modules).
