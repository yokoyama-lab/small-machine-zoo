/-
  **2 記号の URTM(85,2) の存在（Morita Def. 7.1 の意味で、計算可能な符号化と復号を含めて）**

  `exists_urtm_85_2`: 状態数 85・記号数 2 の決定的かつ可逆な TM で `IsUTMStrict`（`LeanUniv/Strict.lean`。
  Morita 2017 Def. 7.1。復号は停止 ID の**どの**符号に対しても正しいことを要求する）を満たすものが
  存在する。機械は Morita の (13,7) に記号削減（Thm 5.4 の改良と状態の併合、docs/23）を掛けたもの
  （`URTM.Gen.FS85_2.M`、153 本、各記号を 3 ビットに符号化）。連鎖は (10,8) と共通の
  tm n → TRM → 2-TS → CTSH に、`lean/URTM/CTSH85_2Main.lean` の CTSH 模倣定理を出口層としてつないだもの。
  仮定は無い。

  この機械は停止用の五つ組も疑似状態も持たない（`U85_2.U_noPseudo`）。(13,7) が停止の五つ組を当てる
  ところで、当てられる五つ組が無くなって止まる。状態は 85 個ちょうど。最小性は主張しない。

  **Existence of the 2-symbol URTM(85,2) in the exact sense of Def. 7.1**, including computable
  encoding and decoding. The machine is the symbol reduction of Morita's (13,7) (3 bits per
  symbol). It has no halting quintuple and no pseudo-state (`U85_2.U_noPseudo`): it halts where
  no quintuple applies. No hypotheses. Minimality is not claimed.
-/
import LeanUniv.U85_2

namespace URTM.Univ.Final85_2
open URTM URTM.Spec

theorem exists_urtm_85_2 :
    ∃ U : List Quint, Deterministic U ∧ Reversible U ∧ NStates U = 85 ∧ NSyms U = 2 ∧
      IsUTMStrict U :=
  ⟨U85_2.U, U85_2.U_det, U85_2.U_rev, U85_2.U_counts.1, U85_2.U_counts.2, U85_2.isUTMStrict_U⟩

end URTM.Univ.Final85_2
