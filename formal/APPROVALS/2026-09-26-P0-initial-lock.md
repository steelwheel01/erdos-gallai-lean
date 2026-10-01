# 2026-09-26 — P0 initial lock

**What:** initial `LOCK.json` for the P0 scaffold: `EG.Obj` (+ constructors), `EG.cycleEdges`,
`EG.Obj.edges`, `EG.Obj.WF`, `EG.IsDecomp` (EG/Defs/Objects.lean) and `EG.Spec.MainInternal`
(EG/Spec/Main.lean), plus the file hashes of the protected files (TRUST.md, lake files,
EGCheck/Final.lean).

**Status:** DRAFT definitions, not yet reviewed. They are re-reviewed in P1 (two independent
agent reviews, PLAN §4/§6 GNG-2) together with the other foundation definitions, and re-locked
under a new approval record. This initial lock exists so that CI's lock check is meaningful
from the first run.

**Who:** orchestrator (integrator), 2026-09-26.
