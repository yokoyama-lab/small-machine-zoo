/-
  **2-symbol URTMs from the other five machines of Morita (in the sense of Def. 7.1)**

  The symbol reduction of docs/23 (Morita 2017 Thm 5.4 improved, with the merging of states) that
  gives URTM(85,2) from (13,7) (`Final85_2.lean`), applied to the other five machines of Morita
  whose two-symbol records the search found (docs/32 §3, `results/fewsym/records/*.merge.json`):

  * (10,8) → URTM(92,2), 169 quintuples (`U92_2_10_8`);
  * (24,4) → URTM(92,2), 176 quintuples (`U92_2_24_4`);
  * (15,6) → URTM(108,2), 187 quintuples (`U108_2_15_6`);
  * (17,5) → URTM(115,2), 198 quintuples (`U115_2_17_5`);
  * (32,3) → URTM(115,2), 209 quintuples (`U115_2_32_3`).

  Each is a deterministic and reversible TM with the stated numbers of states and symbols that is a
  UTM in the strict sense of Morita Def. 7.1 (`IsUTMStrict`, with computable encoding and decoding;
  the decoder is right on every code of the halting ID). The common part of the proofs is
  `FewSymGen.isUTMStrict_fewsym`. All five are dominated by URTM(85,2). Minimality is not claimed.
  No hypotheses.

  None of the five tables has a halting quintuple or a pseudo-state (`U_noPseudo`): the machine
  halts where no quintuple applies.
-/
import LeanUniv.U92_2_10_8
import LeanUniv.U92_2_24_4
import LeanUniv.U108_2_15_6
import LeanUniv.U115_2_17_5
import LeanUniv.U115_2_32_3

namespace URTM.Univ.FinalFewSym
open URTM URTM.Spec

/-- **URTM(92,2) from (10,8).** -/
theorem exists_urtm_92_2_of_10_8 :
    ∃ U : List Quint, Deterministic U ∧ Reversible U ∧ NStates U = 92 ∧ NSyms U = 2 ∧
      IsUTMStrict U :=
  ⟨U92_2_10_8.U, U92_2_10_8.U_det, U92_2_10_8.U_rev, U92_2_10_8.U_counts.1,
    U92_2_10_8.U_counts.2, U92_2_10_8.isUTMStrict_U⟩

/-- **URTM(92,2) from (24,4).** -/
theorem exists_urtm_92_2_of_24_4 :
    ∃ U : List Quint, Deterministic U ∧ Reversible U ∧ NStates U = 92 ∧ NSyms U = 2 ∧
      IsUTMStrict U :=
  ⟨U92_2_24_4.U, U92_2_24_4.U_det, U92_2_24_4.U_rev, U92_2_24_4.U_counts.1,
    U92_2_24_4.U_counts.2, U92_2_24_4.isUTMStrict_U⟩

/-- **URTM(108,2) from (15,6).** -/
theorem exists_urtm_108_2_of_15_6 :
    ∃ U : List Quint, Deterministic U ∧ Reversible U ∧ NStates U = 108 ∧ NSyms U = 2 ∧
      IsUTMStrict U :=
  ⟨U108_2_15_6.U, U108_2_15_6.U_det, U108_2_15_6.U_rev, U108_2_15_6.U_counts.1,
    U108_2_15_6.U_counts.2, U108_2_15_6.isUTMStrict_U⟩

/-- **URTM(115,2) from (17,5).** -/
theorem exists_urtm_115_2_of_17_5 :
    ∃ U : List Quint, Deterministic U ∧ Reversible U ∧ NStates U = 115 ∧ NSyms U = 2 ∧
      IsUTMStrict U :=
  ⟨U115_2_17_5.U, U115_2_17_5.U_det, U115_2_17_5.U_rev, U115_2_17_5.U_counts.1,
    U115_2_17_5.U_counts.2, U115_2_17_5.isUTMStrict_U⟩

/-- **URTM(115,2) from (32,3).** -/
theorem exists_urtm_115_2_of_32_3 :
    ∃ U : List Quint, Deterministic U ∧ Reversible U ∧ NStates U = 115 ∧ NSyms U = 2 ∧
      IsUTMStrict U :=
  ⟨U115_2_32_3.U, U115_2_32_3.U_det, U115_2_32_3.U_rev, U115_2_32_3.U_counts.1,
    U115_2_32_3.U_counts.2, U115_2_32_3.isUTMStrict_U⟩

end URTM.Univ.FinalFewSym
