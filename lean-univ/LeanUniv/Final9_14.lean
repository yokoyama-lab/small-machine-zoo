/-
  **URTM(9,14) in the sense of Def. 7.1** (computable encoding and decoding included)

  Morita's URTM(10,8) with the state copy_y_2 merged into case_y_1; the difference between the two
  roles is carried by a tag on the cells (`lean/URTM/CTSH9_14Defs.lean`, `T9`, 63 quintuples). The
  witness is `U9_14.U = numT num9_14 T9` (`U9_14.U_def`). Its CTSH theorem is
  `URTM.CTSH.U9_14.urtm9_14_simulates_ctsh`; the chain tm n → TRM → 2-TS → CTSH is the one of (10,8),
  the encoder is the one of (10,8), and the decoder erases the tags before the decoder of (10,8)
  (`LeanUniv/U9_14.lean`). No hypotheses. Minimality is not claimed.
-/
import LeanUniv.U9_14
import LeanUniv.U9_14b

namespace URTM.Univ.Final9_14
open URTM URTM.Spec

theorem exists_urtm_9_14 :
    ∃ U : List Quint, Deterministic U ∧ Reversible U ∧ NStates U = 9 ∧ NSyms U = 14 ∧
      IsUTMStrict U :=
  U9_14.exists_urtm_9_14

/-- **A second URTM(9,14)** (the table t4b: copy_n_2 merged into case_y_1, 64 quintuples; witness
    `U9_14b.U_def`). The same point (9,14) as `exists_urtm_9_14`, by a different merge. -/
theorem exists_urtm_9_14b :
    ∃ U : List Quint, Deterministic U ∧ Reversible U ∧ NStates U = 9 ∧ NSyms U = 14 ∧
      IsUTMStrict U :=
  U9_14b.exists_urtm_9_14b

end URTM.Univ.Final9_14
