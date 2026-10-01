module

public import EG.Spec.Stage1.COLa
public import EG.Lib.Stage1.COLa
public import EG.Proof.Link.L15
public import EG.Proof.Todo.StructureExp
public import EG.Proof.Todo.COLJVRow3
public import EG.Proof.Todo.COLJVRow9

/-!
# [s3:lemCOL] (a), failure bound from its proof — Proved in P3.

Formerly a declared input of probe unit P4B (probe P-4, part 2), owned by the s3 Lemma-COL unit;
used by s3:lemCOL (c) (`EG.Spec.COLcStatement`). Proved in P3 (unit s3) by
`EG.COLaProof.colaProb` (`EG/Lib/Stage1/COLa.lean`): three applications of Lemma 15⁺ (`EG.l15p`),
conditioning on the bits, with Proposition s2:propStructure (i) (`EG.Todo.StructureExp`) and rows
3 and 9 of the COL-JV table (`EG.Todo.COLJVRow3`, `EG.Todo.COLJVRow9`). Design note
`formal/work/p2b/P4B.md`.
-/

public section

namespace EG

/-- Proved in P3. [s3:lemCOL] (a), failure bound from its proof "the total failure probability of (a) is at most `2(2+k+k_own)N^{-5} ≤ … ≤ N^{-2}/4`". -/
theorem colaProb : EG.Spec.COLaProbStatement :=
  COLaProof.colaProb EG.l15p EG.Todo.StructureExp EG.Todo.COLJVRow3 EG.Todo.COLJVRow9

end EG
