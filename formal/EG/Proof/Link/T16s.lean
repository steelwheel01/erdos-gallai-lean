module

public import EG.Spec.Link.T16s
public import EG.Lib.Link.T16sProof
public import EG.Proof.Link.L15
public import EG.Proof.Todo.P18s
public import EG.Proof.Todo.L9rho
public import EG.Proof.Todo.T16sForced
public import EG.Proof.Todo.ChernoffGen
public import EG.Proof.Todo.StarS5

/-!
# Theorem 16* [s3:thmT16s] — Proved in P3.

Formerly a declared input of probe unit P4B (probe P-4, part 2), owned by the s3 Theorem-16*
unit; used by s3:lemCOL (c) per U-index (`EG.Spec.COLcIndexStatement`). Proved in P3 (unit s3)
by the assembly `EG.T16sProof.t16s` (`EG/Lib/Link/T16sProof.lean`) from Lemma 15⁺
(`EG.l15p`), Lemma 19* (`EG.Todo.P18s`), Lemma 9_ρ (`EG.Todo.L9rho`), Theorem 16* (b)
(`EG.Todo.T16sForced`), Chernoff (`EG.Todo.ChernoffGen`) and (S5) (`EG.Todo.StarS5`).
Design note `formal/work/p2b/P4B.md`.
-/

public section

namespace EG

/-- Proved in P3. [s3:thmT16s] Theorem 16*: "… Then, with probability at least `1 - 2^{86} t L^{19} ρ^{-3} N^{-3}`, the graph `X` is `(2^{12}L^4, t)`-path connected through `V`." -/
theorem t16s : EG.Spec.T16sStatement :=
  T16sProof.t16s EG.l15p EG.Todo.P18s EG.Todo.L9rho EG.Todo.T16sForced EG.Todo.ChernoffGen
    EG.Todo.StarS5

end EG
