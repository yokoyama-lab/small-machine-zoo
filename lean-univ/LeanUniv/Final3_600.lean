/-
  **3 状態の URTM(3,600) の存在（Morita Def. 7.1 の意味で、計算可能な符号化と復号を含めて）**

  `exists_urtm_3_600`: 状態数 3・記号数 600 の決定的かつ可逆な TM で `IsUTMStrict`（`LeanUniv/Strict.lean`。
  Morita 2017 Def. 7.1。復号は停止 ID の**どの**符号に対しても正しいことを要求する）を満たすものが
  存在する。機械は Morita の (32,3)（停止用の五つ組を除いたもの）に改良版の 3 状態化の反転版（docs/09）を
  掛けたもの（`URTM.Gen.T3_600.T3py`、1572 本）。連鎖は (10,8) と共通の tm n → TRM → 2-TS → CTSH に、
  `lean/URTM/CTSH3_600Main.lean` の CTSH 模倣定理を出口層としてつないだもの。仮定は無い。

  この機械は停止用の五つ組も疑似状態も持たない（`U3_600.U_noPseudo`）。当てられる五つ組が無くなって止まる。
  停止配置は模倣した歩数 N に依る（1 歩ごとに窓が 2 マス伸び、1 マスずれる）が、復号 `U3_600.readU` は
  停止 ID だけを読み、N を受け取らない。最小性は主張しない。

  **Existence of the 3-state URTM(3,600) in the exact sense of Def. 7.1**, including computable
  encoding and decoding. The machine is the improved 3-state conversion (mirrored) of Morita's
  (32,3) without its halting quintuples. It has no halting quintuple and no pseudo-state
  (`U3_600.U_noPseudo`). The final configuration depends on the number of simulated steps; the
  decoder reads only the halting ID. No hypotheses. Minimality is not claimed.
-/
import LeanUniv.U3_600

namespace URTM.Univ.Final3_600
open URTM URTM.Spec

theorem exists_urtm_3_600 :
    ∃ U : List Quint, Deterministic U ∧ Reversible U ∧ NStates U = 3 ∧ NSyms U = 600 ∧
      IsUTMStrict U :=
  ⟨U3_600.U, U3_600.U_det, U3_600.U_rev, U3_600.U_counts.1, U3_600.U_counts.2,
    U3_600.isUTMStrict_U⟩

end URTM.Univ.Final3_600
