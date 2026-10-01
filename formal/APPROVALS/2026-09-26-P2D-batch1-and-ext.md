# 2026-09-26 — P2-D batch 1 definitions and external-result statements: approval

**Scope.** (a) P2-D batch 1 definitions (wf_2d8e30ba-18f): small foundations (Obj.isEdge, nbrSetDeg,
IsWellExpanding, Log/logStar/tower, Constants, PathDecomp, Components, Gamma/Core), s6 routing-engine data
(Cluster, EqLpt, HCCP), s3/s4 parameters (Link/Star, Vortex, Lend/COLTable), and the s2 hierarchy model
(HB Witness, SplitTree, Round with integer M_l per v6.1, Run). Additions to the locked files
EG/Defs/Graph.lean and EG/Defs/Objects.lean only add constants: no locked constant's closure changed
(checked by comparing lock dumps). (b) Statements of proved external results: EG.Spec.Ext.Haxell
(stated and q²-forms), EG.Spec.Found.EG0, EG.Spec.Found.BBD (wf_b7a0dc25-a0a); the locked
BMLemma25Statement is now proved.

**Reviews.** Every group had an authoring review in round 1 (Opus) and an independent review in round 2
on a different model (Fable), each with a fix round (formal/work/p2d/*.review{1,2}.md,
formal/work/ext/*.review{1,2}.md). All final verdicts: approve; no open minor or major issue; no
manuscript defect found (notes are T0 encodings, recorded in the design notes).

**Build at approval.** lake build EG EGTest EGCheck OK; lint 0 findings; axiom scan 3,312 constants,
0 violations, 0 meta-scan hits; sorry frontier = {EG.Proof.mainInternal} (plus EGCheck.smoke/solution).

**Decision:** approved for locking (integrator, 2026-09-26; user notified in the status report).
