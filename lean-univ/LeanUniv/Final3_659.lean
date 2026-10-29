/-
  **3 状態の URTM(3,659) の存在（Morita Def. 7.1 の意味で、計算可能な符号化と復号を含めて）**

  `exists_urtm_3_659`: 状態数 3・記号数 659 の決定的かつ可逆な TM で `IsUTMStrict`（`LeanUniv/Strict.lean`。
  Morita 2017 Def. 7.1。復号は停止 ID の**どの**符号に対しても正しいことを要求する）を満たすものが
  存在する。機械は Morita の (32,3)（停止用の五つ組を除いたもの）に改良版の 3 状態化（docs/09）を
  **反転せずに**掛けたもの（`URTM.Gen.T3_659.T3py`、1757 本。証人がこの表であることは `U3_659.U_is_conv`）。
  連鎖は (10,8) と共通の tm n → TRM → 2-TS → CTSH に、`LeanUniv/Sim3_659.lean` の CTSH 模倣定理を
  出口層としてつないだもの。仮定は無い。

  この機械は停止用の五つ組も疑似状態も持たない（`U3_659.U_noPseudo`）。当てられる五つ組が無くなって止まる。
  停止配置は模倣した歩数 N に依る（1 歩ごとに窓が 2 マス伸び、1 マスずれる）が、復号 `U3_659.readU` は
  停止 ID だけを読み、N を受け取らない。最小性は主張しない（反転した (3,600) の方が記号が少ない）。

  **Existence of the 3-state URTM(3,659) in the exact sense of Def. 7.1**, including computable
  encoding and decoding. The machine is the improved 3-state conversion (not mirrored) of Morita's
  (32,3) without its halting quintuples (`U3_659.U_is_conv`). It has no halting quintuple and no
  pseudo-state (`U3_659.U_noPseudo`). The final configuration depends on the number of simulated
  steps; the decoder reads only the halting ID. No hypotheses. Minimality is not claimed.
-/
import LeanUniv.U3_659

namespace URTM.Univ.Final3_659
open URTM URTM.Spec

theorem exists_urtm_3_659 :
    ∃ U : List Quint, Deterministic U ∧ Reversible U ∧ NStates U = 3 ∧ NSyms U = 659 ∧
      IsUTMStrict U :=
  ⟨U3_659.U, U3_659.U_det, U3_659.U_rev, U3_659.U_counts.1, U3_659.U_counts.2,
    U3_659.isUTMStrict_U⟩

end URTM.Univ.Final3_659
