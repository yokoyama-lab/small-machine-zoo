/-
  **URTM(4,48) in the sense of Def. 7.1** (computable encoding and decoding included)

  The ε-reversed 4-state conversion of Morita's (10,8) (docs/20 §3, `URTM.CTSH.U4_48`) gives a
  deterministic reversible TM with 4 states and 48 symbols that satisfies `IsUTMStrict`
  (`LeanUniv/Strict.lean`, Morita 2017 Def. 7.1; the decoder is right on every code of the halting ID).
  The machine is the block conversion `KStateBlocks.bconv` with one block in each direction
  (`LeanUniv/U4_48.lean`), which is the table of `URTM.CTSH.U4_48` up to the names of the states
  (`URTM.CTSH.U4_48B.same_as_eps`). The chain tm n → TRM → 2-TS → CTSH is the one of (10,8); the exit
  layer is the machine's CTSH theorem. No hypotheses.

  URTM(4,48) is dominated by URTM(4,46) and URTM(4,41). Minimality is not claimed.
-/
import LeanUniv.U4_48

namespace URTM.Univ.Final4_48
open URTM URTM.Spec

theorem exists_urtm_4_48 :
    ∃ U : List Quint, Deterministic U ∧ Reversible U ∧ NStates U = 4 ∧ NSyms U = 48 ∧
      IsUTMStrict U :=
  ⟨U4_48.U, U4_48.U_det, U4_48.U_rev, U4_48.U_counts.1, U4_48.U_counts.2, U4_48.isUTMStrict_U⟩

end URTM.Univ.Final4_48
