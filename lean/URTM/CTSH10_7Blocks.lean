/-
  (10,7) の表 `T10`（`URTM.CTSH.U10_7`、lean/URTM/CTSH10_7.lean）をブロック化の一般定理
  `KStateBlocks.bconv_main` の基底にするための 3 つの事実（CTSH11_7Blocks の (11,7) 用 `hW11`・`finCfg11_pseudo`・
  `nostuck11` の類比。2026-11-04、T25）。記号の併合で URTM(6,29)・(4,38)・(5,36) になるブロック表
  （tools/gen_symmerge_lean.py、`URTM.CTSH.SM6_29` など、生成モジュール `URTM.Gen.KB6_29` など）が使う。

  * `hW10`: 0 シフトの規則は疑似状態へ入る停止規則だけ（`ZeroShiftHalts T10`。`decide`）。
  * `finCfg10_pseudo`: 停止配置 `finCfg10` の状態は疑似状態（null か halt）。
  * `nostuck10`: `encC10 C w` からの実行は疑似状態以外で止まらない（主定理 `urtm10_7_simulates_ctsh` の
    2 番目、停止配置は必ず `finCfg10`、から）。
  未証明の穴・新規公理・native_decide を使わない。
-/
import URTM.CTSH10_7
import URTM.KStateBlocks

namespace URTM.CTSH.U10_7

open URTM URTM.KState URTM.KStateSparse URTM.CTSH

/-- `T10` の 0 シフトの規則は停止規則だけ（ブロック化の一般定理の仮定 `hW`）。 -/
theorem hW10 : ZeroShiftHalts T10 := by decide

/-- (10,7) の停止配置 `finCfg10` の状態は疑似状態（null か halt）。 -/
theorem finCfg10_pseudo (C : CTSH) (vf : List Ch) (mf : Nat) (rm : List Ch) :
    ∃ h, (finCfg10 C vf mf rm).st = .halt h := by
  cases vf with
  | nil => exact ⟨_, rfl⟩
  | cons _ _ => exact ⟨_, rfl⟩

/-- (10,7) を Morita の初期配置から動かすと、疑似状態以外では止まらない
    （規則の無い組 (q, s) に出会わない）。 -/
theorem nostuck10 (C : CTSH) (w : List Ch) : NoStuck T10 (encC10 C w) := by
  intro N e he
  obtain ⟨n, vf, mf, rm, _, rfl⟩ := (urtm10_7_simulates_ctsh C w).2.1 N e he
  exact finCfg10_pseudo C vf mf rm

end URTM.CTSH.U10_7
