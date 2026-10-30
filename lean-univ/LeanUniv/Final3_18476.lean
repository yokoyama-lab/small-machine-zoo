/-
  **3 状態 18476 記号の URTM の存在（Morita Def. 7.1 の意味で、計算可能な符号化と復号を含めて）**

  `exists_urtm_3_18476`: 状態数 3・記号数 18476 の決定的かつ可逆な TM で `IsUTMStrict`
  （`LeanUniv/Strict.lean`。Morita 2017 Def. 7.1。復号は停止 ID の**どの**符号に対しても正しいことを要求する）
  を満たすものが存在する。機械は Morita の 3 状態化の中間段: (32,3)（停止用の五つ組を除いたもの）の
  1WU 機械 T̂（Lemma 5.9。1 マスに (32,3) の 2 マスを詰める）に、↑ と ↓ をまとめて計数 1..61 を全部残した
  3 状態化 `Conv3P.conv That .L .bl idx3 (fun _ => 61) allW` を掛けたもの（`lean/URTM/CTSH3_18476Main.lean`。
  証人がその番号付けであることは `U3_18476.U_is_conv`）。表はおよそ 10⁵ 本あるので書き下さず、
  状態数・記号数・決定性・可逆性は単射な番号付けを通して記号の機械から移す（`Num3_18476.lean`）。
  連鎖は (10,8) と共通の tm n → TRM → 2-TS → CTSH に、zoo の CTSH 模倣定理
  `CTSH.U3_18476.urtm3_18476_simulates_ctsh` を出口層としてつないだもの（`U3_18476.lean`）。仮定は無い。

  復号 `U3_18476.readU` は停止 ID だけを読む（模倣した歩数 N を受け取らない）。組を 2 マスにほどき、
  頭のマスの計数が運ぶ 1 マスを補って、(32,3) の復号に渡す。最小性は主張しない
  （(3,600)・(3,659) の方が記号が少ない）。

  **Existence of the 3-state URTM(3,18476) in the exact sense of Def. 7.1**, including computable
  encoding and decoding. The machine is the intermediate machine of Morita's three-state conversion
  of (32,3) without its halting quintuples (`U3_18476.U_is_conv`). No hypotheses. Minimality is not
  claimed.
-/
import LeanUniv.U3_18476

namespace URTM.Univ.Final3_18476
open URTM URTM.Spec

theorem exists_urtm_3_18476 :
    ∃ U : List Quint, Deterministic U ∧ Reversible U ∧ NStates U = 3 ∧ NSyms U = 18476 ∧
      IsUTMStrict U :=
  ⟨U3_18476.U, U3_18476.U_det, U3_18476.U_rev, U3_18476.U_counts.1, U3_18476.U_counts.2,
    U3_18476.isUTMStrict_U⟩

end URTM.Univ.Final3_18476
