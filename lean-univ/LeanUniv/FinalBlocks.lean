/-
  **ブロック化の 6 台 URTM(4,46)・(5,45)・(6,37)・(7,32)・(8,28)・(9,27) の存在
  （Morita Def. 7.1 の意味で、計算可能な符号化と復号を含めて）**

  各定理: 状態数 m・記号数 n の決定的かつ可逆な TM で `IsUTMStrict`（`LeanUniv/Strict.lean`。
  Morita 2017 Def. 7.1。復号は停止 ID の**どの**符号に対しても正しいことを要求する）を満たすものが
  存在する。機械は Morita の (10,8)・(15,6)・(17,5) にブロック分け × 役割の併合 × ε の変換
  `KStateBlocks.bconv` を掛けたもの（(4,46)・(6,37) ← (10,8)、(5,45)・(7,32)・(9,27) ← (15,6)、
  (8,28) ← (17,5)）。連鎖は (10,8) と共通の tm n → TRM → 2-TS → CTSH に、各機械の CTSH 模倣定理
  （`lean/URTM/CTSH<m>_<n>Main.lean`）を出口層としてつないだもの。仮定は無い。

  証人 U は生成表 `URTM.Gen.KB<m>_<n>.TpyB`（= `bconv T spB qsB ssB`）を番号付けしたもの。元機械と同じく、
  停止は疑似状態への 0 シフトの五つ組 2 本で表す（`U<m>_<n>.U_halting`）。疑似状態は出ていく五つ組を
  持たず、`NStates` には入らない。最小性は主張しない。

  **Existence of the six block-converted URTMs in the exact sense of Def. 7.1**, including
  computable encoding and decoding. Each machine is `KStateBlocks.bconv` applied to Morita's
  (10,8), (15,6) or (17,5). The chain tm n → TRM → 2-TS → CTSH is the one of (10,8); the exit
  layer is each machine's CTSH theorem. No hypotheses. Minimality is not claimed.
-/
import LeanUniv.U4_46
import LeanUniv.U5_45
import LeanUniv.U6_37
import LeanUniv.U7_32
import LeanUniv.U8_28
import LeanUniv.U9_27

namespace URTM.Univ.FinalBlocks
open URTM URTM.Spec

theorem exists_urtm_4_46 :
    ∃ U : List Quint, Deterministic U ∧ Reversible U ∧ NStates U = 4 ∧ NSyms U = 46 ∧
      IsUTMStrict U :=
  ⟨U4_46.U, U4_46.U_det, U4_46.U_rev, U4_46.U_counts.1, U4_46.U_counts.2, U4_46.isUTMStrict_U⟩

theorem exists_urtm_5_45 :
    ∃ U : List Quint, Deterministic U ∧ Reversible U ∧ NStates U = 5 ∧ NSyms U = 45 ∧
      IsUTMStrict U :=
  ⟨U5_45.U, U5_45.U_det, U5_45.U_rev, U5_45.U_counts.1, U5_45.U_counts.2, U5_45.isUTMStrict_U⟩

theorem exists_urtm_6_37 :
    ∃ U : List Quint, Deterministic U ∧ Reversible U ∧ NStates U = 6 ∧ NSyms U = 37 ∧
      IsUTMStrict U :=
  ⟨U6_37.U, U6_37.U_det, U6_37.U_rev, U6_37.U_counts.1, U6_37.U_counts.2, U6_37.isUTMStrict_U⟩

theorem exists_urtm_7_32 :
    ∃ U : List Quint, Deterministic U ∧ Reversible U ∧ NStates U = 7 ∧ NSyms U = 32 ∧
      IsUTMStrict U :=
  ⟨U7_32.U, U7_32.U_det, U7_32.U_rev, U7_32.U_counts.1, U7_32.U_counts.2, U7_32.isUTMStrict_U⟩

theorem exists_urtm_8_28 :
    ∃ U : List Quint, Deterministic U ∧ Reversible U ∧ NStates U = 8 ∧ NSyms U = 28 ∧
      IsUTMStrict U :=
  ⟨U8_28.U, U8_28.U_det, U8_28.U_rev, U8_28.U_counts.1, U8_28.U_counts.2, U8_28.isUTMStrict_U⟩

theorem exists_urtm_9_27 :
    ∃ U : List Quint, Deterministic U ∧ Reversible U ∧ NStates U = 9 ∧ NSyms U = 27 ∧
      IsUTMStrict U :=
  ⟨U9_27.U, U9_27.U_det, U9_27.U_rev, U9_27.U_counts.1, U9_27.U_counts.2, U9_27.isUTMStrict_U⟩

end URTM.Univ.FinalBlocks
