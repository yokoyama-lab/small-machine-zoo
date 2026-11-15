/-
  (9,8) の表 `T9`（`URTM.CTSH.U9_8`、lean/URTM/CTSH9_8.lean）をブロック化の一般定理
  `KStateBlocks.bconv_main` の基底にするための 3 つの事実（CTSH10_7Blocks の (10,7) 用 `hW10`・`finCfg10_pseudo`・
  `nostuck10` の類比。2026-11-05、T28）。記号の併合で URTM(7,26)・(6,28) になるブロック表
  （tools/gen_symmerge_lean.py、生成モジュール `URTM.Gen.KB7_26` など）が使う。

  * `hW9`: 0 シフトの規則は疑似状態へ入る停止規則だけ（`ZeroShiftHalts T9`。`decide`）。
  * `finCfg9_pseudo`: 停止配置 `finCfg9` の状態は疑似状態（null か halt）。
  * `nostuck9`: `encC9 C w` からの実行は疑似状態以外で止まらない（主定理 `urtm9_8_simulates_ctsh` の
    2 番目、停止配置は必ず `finCfg9`、から）。
  未証明の穴・新規公理・native_decide を使わない。
-/
import URTM.CTSH9_8
import URTM.KStateBlocks

namespace URTM.CTSH.U9_8

open URTM URTM.KState URTM.KStateSparse URTM.CTSH

/-- `T9` の 0 シフトの規則は停止規則だけ（ブロック化の一般定理の仮定 `hW`）。 -/
theorem hW9 : ZeroShiftHalts T9 := by decide

/-- (9,8) の停止配置 `finCfg9` の状態は疑似状態（null か halt）。 -/
theorem finCfg9_pseudo (C : CTSH) (vf : List Ch) (mf : Nat) (rm : List Ch) :
    ∃ h, (finCfg9 C vf mf rm).st = .halt h := by
  cases vf with
  | nil => exact ⟨_, rfl⟩
  | cons _ _ => exact ⟨_, rfl⟩

/-- (9,8) を Morita の初期配置（8 記号で書いたもの）から動かすと、疑似状態以外では止まらない
    （規則の無い組 (q, s) に出会わない）。 -/
theorem nostuck9 (C : CTSH) (w : List Ch) : NoStuck T9 (encC9 C w) := by
  intro N e he
  obtain ⟨n, vf, mf, rm, _, rfl⟩ := (urtm9_8_simulates_ctsh C w).2.1 N e he
  exact finCfg9_pseudo C vf mf rm

end URTM.CTSH.U9_8
