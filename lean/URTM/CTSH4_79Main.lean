/-
  URTM(4,79)（定理 A の疎版 ∘ URTM(13,7)、docs/15_sparse_counters_2026-09-27.md）が
  任意の CTSH を模倣すること。

  * 疎版の一般定理 `URTM.KStateSparse.sconv_main`（KStateSparse.lean）は、T の実行が
    疑似状態以外で止まらない（`NoStuck`）ことを仮定に、密な版と同じ模倣を与える。
  * (13,7) の CTSH 模倣の主定理 `urtm13_7_simulates_ctsh`（CTSH13_7Main.lean）の 2 番目
    （停止配置は必ず `finCfg13`）から、`encC13 C w` からの実行は疑似状態 null / halt でしか
    止まらない（`nostuck13`）。
  * 具体の疎版 `sconv T qsS ss` は生成モジュール `URTM.Gen.KS13_7`（tools/gen_kstate_lean.py
    --sparse K13_7）にあり、Python（tools/kstate_sparse_k4.py）の表 `TpyS` と規則の並びまで一致し、
    記号の全体は 79 要素、規則は 203 本（いずれも `decide +kernel`）。

  生成モジュールに依存するので、`tools/gen_all_lean.sh`（CI）が書く `URTM.lean` 経由でビルドされる。
  未証明の穴・新規公理・native_decide を使わない。
-/
import URTM.CTSH13_7Main
import URTM.Gen.KS13_7

namespace URTM.CTSH.U4_79

open URTM URTM.KState URTM.KStateSparse URTM.CTSH URTM.Gen.K13_7
open URTM.Gen.KS13_7 (qsS TpyS hQS sconv_eq_py)
open URTM.CTSH.U13_7 (encC13 finCfg13 urtm13_7_simulates_ctsh)

/-- (13,7) の停止配置 `finCfg13` の状態は疑似状態（null か halt）。 -/
theorem finCfg13_pseudo (C : CTSH) (vf : List Ch) (mf : Nat) (rm : List Ch) :
    ∃ h, (finCfg13 C vf mf rm).st = .halt h := by
  cases vf with
  | nil => exact ⟨_, rfl⟩
  | cons _ _ => exact ⟨_, rfl⟩

/-- (13,7) を Morita の初期配置から動かすと、疑似状態以外では止まらない
    （規則の無い組 (q, s) に出会わない）。 -/
theorem nostuck13 (C : CTSH) (w : List Ch) : NoStuck T (encC13 C w) := by
  intro N e he
  obtain ⟨n, vf, mf, rm, _, rfl⟩ := (urtm13_7_simulates_ctsh C w).2.1 N e he
  exact finCfg13_pseudo C vf mf rm

/-- **主定理（URTM(4,79) は任意の CTSH を模倣する）**。T' = `sconv T qsS ss`
    （定理 A の疎版を (13,7) に適用したもの。4 状態・記号は 79 要素の `sparseUniverse T qsS ss` に入る・
    規則 203 本・決定的可逆、Python の生成表 `TpyS` と一致）を符号化 `E = enc T (canonOff T qsS)` を
    通して見ると、任意の CTSH C と初期語 w について:

    1. C が (w, 0) から n ステップで停止 ID (vf, mf) に達するなら、T' は E (encC13 C w) から
       n ステップ以上で停止し、停止配置は E (finCfg13 C vf mf rm)。
    2. 逆に T' が E (encC13 C w) から停止するなら、C も (w, 0) から停止し、停止配置は 1 の形。
    3. C が停止しない ⇔ T' が停止しない。 -/
theorem urtm4_79_simulates_ctsh (C : CTSH) (w : List Ch) :
    let T' := sconv T qsS ss
    let E := enc T (canonOff T qsS)
    Deterministic T' ∧ Reversible T' ∧
    (∀ x : KSt, x ∈ [KSt.Hp, .Hm, .Ap, .Am]) ∧
    (∀ ρ ∈ T', ρ.s ∈ sparseUniverse T qsS ss ∧ ρ.t ∈ sparseUniverse T qsS ss) ∧
    (sparseUniverse T qsS ss).length = 79 ∧ T'.length = 203 ∧ T' = TpyS ∧
    (∀ n vf mf, CHaltsIn C n (w, 0) (vf, mf) →
      ∃ N rm, n ≤ N ∧ HaltsIn T' N (E (encC13 C w)) (E (finCfg13 C vf mf rm))) ∧
    (∀ N e, HaltsIn T' N (E (encC13 C w)) e →
      ∃ n vf mf rm, CHaltsIn C n (w, 0) (vf, mf) ∧ e = E (finCfg13 C vf mf rm)) ∧
    ((∀ n f, ¬ CHaltsIn C n (w, 0) f) ↔ (∀ N e, ¬ HaltsIn T' N (E (encC13 C w)) e)) := by
  intro T' E
  obtain ⟨hD', hR', -, hF, hB, hN, hsym⟩ := sconv_main (ss := ss) hW hD hR hQS hS
  obtain ⟨-, h79, h203⟩ := URTM.Gen.KS13_7.card
  refine ⟨hD', hR', KSt_all, hsym, h79, ?_, sconv_eq_py,
    compose_ctsh E (finCfg13_pseudo C) (nostuck13 C w) (urtm13_7_simulates_ctsh C w) hF hB hN⟩
  show (sconv T qsS ss).length = 203
  rw [sconv_eq_py]; exact h203

end URTM.CTSH.U4_79
