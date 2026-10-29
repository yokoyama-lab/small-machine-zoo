/-
  **URTM(4,88) in the sense of Def. 7.1** (computable encoding and decoding included)

  The 4-state conversion of Theorem A (docs/03 §2, `URTM.KState.conv`) applied to Morita's (10,8)
  gives a deterministic reversible TM with 4 states and 88 symbols that satisfies `IsUTMStrict`
  (`LeanUniv/Strict.lean`, Morita 2017 Def. 7.1; the decoder is right on every code of the halting ID).
  The table is `conv T qs ss` with the states renamed to `Fin 4` (`LeanUniv/U4_88.lean`,
  `URTM.Univ.U4_88.U_is_conv`). The chain tm n → TRM → 2-TS → CTSH is the one of (10,8); the exit
  layer is the machine's CTSH theorem. No hypotheses.

  URTM(4,88) is dominated by URTM(4,48), URTM(4,46) and URTM(4,41). Minimality is not claimed.
-/
import LeanUniv.U4_88

namespace URTM.Univ.Final4_88
open URTM URTM.Spec

theorem exists_urtm_4_88 :
    ∃ U : List Quint, Deterministic U ∧ Reversible U ∧ NStates U = 4 ∧ NSyms U = 88 ∧
      IsUTMStrict U :=
  ⟨U4_88.U, U4_88.U_det, U4_88.U_rev, U4_88.U_counts.1, U4_88.U_counts.2, U4_88.isUTMStrict_U⟩

end URTM.Univ.Final4_88
