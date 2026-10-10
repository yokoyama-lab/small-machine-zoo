/-
  **Morita の手設計 5 台 URTM(13,7)・(15,6)・(17,5)・(24,4)・(32,3) の存在
  （Morita Def. 7.1 の意味で、計算可能な符号化と復号を含めて）**

  各定理: 状態数 m・記号数 n の決定的かつ可逆な TM で `IsUTMStrict`（`LeanUniv/Strict.lean`。
  Morita 2017 Def. 7.1。復号は停止 ID の**どの**符号に対しても正しいことを要求する）を満たすものが
  存在する。連鎖は (10,8) と共通の tm n → TRM → 2-TS → CTSH（`Chain10_8`・`ChainGen`）に、
  各機械の CTSH 模倣定理（`lean/URTM/CTSH<m>_<n>Main.lean`）を出口層としてつないだもの。仮定は無い。

  証人 U は Morita の記述ファイル（`data/urtm/urtm<m>-<n>.txt`）の表を番号付けしたもの。本文の表
  （Table 7.1 ほか）が `(halt)`・`(null)` と記す 2 つの停止の欄を、記述ファイルは疑似状態への 0 シフトの
  五つ組 2 本で表すので、U は本文の表より五つ組が 2 本多い（`U<m>_<n>.U_halting` がその 2 本を名指しする）。
  疑似状態は出ていく五つ組を持たず、`NStates`（出ていく五つ組を持つ状態の数）には入らない。これは記述ファイル
  自身の約束である（"halting states "halt" and "null" are added to indicate which case occurred, but they
  should not be counted as the number of states"）。(10,8) と同じ約束。したがって定理が述べるのは
  「記述ファイルの機械が万能」であって、「疑似状態を持たない本文の表そのものが万能」ではない。

  **Existence of Morita's five hand-designed URTMs in the exact sense of Def. 7.1**, including
  computable encoding and decoding. The chain tm n → TRM → 2-TS → CTSH is the one of (10,8);
  the exit layer is each machine's CTSH theorem. No hypotheses.
  The witness is the numbered table of Morita's description file: the book's table plus two
  0-shift quintuples into the pseudo-states `halt`/`null` (which have no outgoing quintuple and
  are not counted by `NStates`, as the description file itself prescribes); `U<m>_<n>.U_halting`
  names the two quintuples. Same convention as (10,8). The theorems are about the machines of
  the description files, not about the book's tables without pseudo-states.
-/
import LeanUniv.U13_7
import LeanUniv.U15_6
import LeanUniv.U17_5
import LeanUniv.U24_4
import LeanUniv.U32_3

namespace URTM.Univ.FinalMorita
open URTM URTM.Spec

theorem exists_urtm_13_7 :
    ∃ U : List Quint, Deterministic U ∧ Reversible U ∧ NStates U = 13 ∧ NSyms U = 7 ∧
      IsUTMStrict U :=
  ⟨U13_7.U, U13_7.U_det, U13_7.U_rev, U13_7.U_counts.1, U13_7.U_counts.2, U13_7.isUTMStrict_U⟩

theorem exists_urtm_15_6 :
    ∃ U : List Quint, Deterministic U ∧ Reversible U ∧ NStates U = 15 ∧ NSyms U = 6 ∧
      IsUTMStrict U :=
  ⟨U15_6.U, U15_6.U_det, U15_6.U_rev, U15_6.U_counts.1, U15_6.U_counts.2, U15_6.isUTMStrict_U⟩

theorem exists_urtm_17_5 :
    ∃ U : List Quint, Deterministic U ∧ Reversible U ∧ NStates U = 17 ∧ NSyms U = 5 ∧
      IsUTMStrict U :=
  ⟨U17_5.U, U17_5.U_det, U17_5.U_rev, U17_5.U_counts.1, U17_5.U_counts.2, U17_5.isUTMStrict_U⟩

theorem exists_urtm_24_4 :
    ∃ U : List Quint, Deterministic U ∧ Reversible U ∧ NStates U = 24 ∧ NSyms U = 4 ∧
      IsUTMStrict U :=
  ⟨U24_4.U, U24_4.U_det, U24_4.U_rev, U24_4.U_counts.1, U24_4.U_counts.2, U24_4.isUTMStrict_U⟩

theorem exists_urtm_32_3 :
    ∃ U : List Quint, Deterministic U ∧ Reversible U ∧ NStates U = 32 ∧ NSyms U = 3 ∧
      IsUTMStrict U :=
  ⟨U32_3.U, U32_3.U_det, U32_3.U_rev, U32_3.U_counts.1, U32_3.U_counts.2, U32_3.isUTMStrict_U⟩

end URTM.Univ.FinalMorita
