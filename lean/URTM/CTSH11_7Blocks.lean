/-
  (11,7) の表 `T11`（`URTM.CTSH.U11_7`、lean/URTM/CTSH11_7.lean）をブロック化の一般定理
  `KStateBlocks.bconv_main` の基底にするための 3 つの事実（CTSH4_79Main の (13,7) 用 `finCfg13_pseudo`・
  `nostuck13` の類比）。記号の併合で URTM(4,40) になるブロック表（tools/gen_symmerge_lean.py、
  `URTM.CTSH.SM4_40`、生成モジュール `URTM.Gen.KB4_40`）が使う。

  * `hW11`: 0 シフトの規則は疑似状態へ入る停止規則だけ（`ZeroShiftHalts T11`。`decide`）。
  * `finCfg11_pseudo`: 停止配置 `finCfg11` の状態は疑似状態（null か halt）。
  * `nostuck11`: `encC11 C w` からの実行は疑似状態以外で止まらない（主定理 `urtm11_7_simulates_ctsh` の
    2 番目、停止配置は必ず `finCfg11`、から）。
  未証明の穴・新規公理・native_decide を使わない。
-/
import URTM.CTSH11_7
import URTM.KStateBlocks

namespace URTM.CTSH.U11_7

open URTM URTM.KState URTM.KStateSparse URTM.CTSH

/-- `T11` の 0 シフトの規則は停止規則だけ（ブロック化の一般定理の仮定 `hW`）。 -/
theorem hW11 : ZeroShiftHalts T11 := by decide

/-- (11,7) の停止配置 `finCfg11` の状態は疑似状態（null か halt）。 -/
theorem finCfg11_pseudo (C : CTSH) (vf : List Ch) (mf : Nat) (rm : List Ch) :
    ∃ h, (finCfg11 C vf mf rm).st = .halt h := by
  cases vf with
  | nil => exact ⟨_, rfl⟩
  | cons _ _ => exact ⟨_, rfl⟩

/-- (11,7) を Morita の初期配置から動かすと、疑似状態以外では止まらない
    （規則の無い組 (q, s) に出会わない）。 -/
theorem nostuck11 (C : CTSH) (w : List Ch) : NoStuck T11 (encC11 C w) := by
  intro N e he
  obtain ⟨n, vf, mf, rm, _, rfl⟩ := (urtm11_7_simulates_ctsh C w).2.1 N e he
  exact finCfg11_pseudo C vf mf rm

end URTM.CTSH.U11_7
