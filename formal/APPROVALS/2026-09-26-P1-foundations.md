# 2026-09-26 — P1 foundations, GATE statement and bridge: approval

**Scope (to be locked with `scripts/lock.py update --modules …` once stage B is integrated):**
EG.Defs.Objects, EG.Defs.Fnum, EG.Spec.Main, EG.Defs.Graph, EG.Defs.Walk, EG.Defs.Expander,
EG.Defs.Prob.FinDist, EG.Defs.Orient, EG.Spec.Chain.Gate; bridge EGCheck/Bridge*.lean (proof, not
locked; the locked EGCheck/Final.lean re-checks its type syntactically and its axioms).

**Reviews.**
1. Authoring reviews (P1b stage A, wf_6674b9d9-12d): two clean-room review rounds per group, all
   approve (formal/work/p1b/*.review{1,2}.md).
2. Final independent approval (wf_6f4849c0-fbd): per group one reviewer on Opus and one on a
   different model (Fable 5.1), reviewing from scratch with scratch Lean tests
   (formal/APPROVALS/reviews/<group>.<opus|fable>.md):

| Group | Opus | Fable | Blocking issues |
|---|---|---|---|
| objects-main-fnum | approve-with-notes | approve | none |
| graph | approve-with-notes | approve | none |
| findist | approve-with-notes | approve-with-notes | none |
| gate | approve-with-notes | approve | none |
| bridge | approve-with-notes | approve | none |

Notes are non-blocking encoding conventions, collected in formal/CONVENTIONS.md. Independent
checks by the reviewers include: MainInternal ⇔ f(n) = O(n) (scratch proof), K8 is a (5,0)- but
not (6,0)-expander (pins log₂² and the 2n/3 cutoff), K2 pins the log base and the multiset reading
of Def 7, GATE non-vacuity on the cyclic triangle, provenance of the pinned upstream files.

**Manuscript-side findings (T0, forwarded to v6):** the remark after s1:citDef11 needs ε > 0;
v6 Fact EG0(b) needs a loopless edge set.

**Decision:** approved for locking (integrator, 2026-09-26). The user is notified in the status
report (non-blocking per PLAN §9).
