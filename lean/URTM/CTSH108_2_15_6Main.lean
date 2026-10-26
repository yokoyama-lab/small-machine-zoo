/-
  URTM(108,2)（(15,6) の記号削減: Morita 2017 Thm 5.4 の改良＋状態の併合、docs/23）が任意の CTSH を模倣すること。

  (15,6) から停止規則 2 本を除いた機械に、記号の符号（3 ビット）b 000・y 100・n 101・∗ 110・$ 111・yd 001、
  先書き v と経路の型（規則ごとに 3・5・7 ステップ）を選んだ Thm 5.4 の変換を施し（162 状態）、状態を併合したもの
  （108 状態・187 本、results/fewsym/records/urtm15-6.108.merge.json。2 記号化の LNS、docs/32 §3）。
  表は生成モジュール `URTM.Gen.FS108_2_15_6`（tools/gen_fewsym_lean.py が tools/fewsym_merge.py の表をそのまま写したもの）にある。

  合成するもの:
    1. `U15_6.urtm15_6_simulates_ctsh`
    2. `FewSym.fs_simulates`（停止規則の除去 `drop_simulates` を内部で使う）に、
       規則ごとの有限の検査 `FS108_2_15_6.cert`（カーネルの `decide`）と決定性 `FS108_2_15_6.det` を渡す。

  併合した機械は「T が規則の無い配置で止まる」場合の停止を保存しないが、(15,6) を Morita の初期配置から
  動かすと停止規則の読みでしか止まらない（停止配置はどれも疑似状態、1 の逆向きから）。`fs_simulates` はこれを内部で使う。

  生成モジュールに依存するので、`tools/gen_all_lean.sh`（CI）が書く `URTM.lean` 経由でビルドされる。
  未証明の穴・新規公理・native_decide を使わない。
-/
import URTM.CTSH15_6Main
import URTM.FewSym
import URTM.Gen.FS108_2_15_6

set_option maxRecDepth 100000

namespace URTM.CTSH.U108_2_15_6

open URTM URTM.KState URTM.CTSH URTM.SimLemmas URTM.FewSym URTM.Gen.K15_6
open URTM.Gen.FS108_2_15_6 (M E cost sts hyp det rev card costs)
open URTM.CTSH.U15_6 (encC15 finCfg15 urtm15_6_simulates_ctsh)

/-- 疑似状態へ入る規則の現状態: halt ← case_y_1（q1）が b を読む、null ← case_y_2（q2）が $ を読む。 -/
def f15 : Ps → St
  | .h0 => .q1
  | .h1 => .q2

theorem hH156 : HaltRulesId T f15 := by decide

/-- (15,6) の停止配置 `finCfg15` の状態は疑似状態（null か halt）。 -/
theorem finCfg15_pseudo (C : CTSH) (vf : List Ch) (mf : Nat) (rm : List Ch) :
    ∃ h, (finCfg15 C vf mf rm).st = .halt h := by
  cases vf with
  | nil => exact ⟨_, rfl⟩
  | cons _ _ => exact ⟨_, rfl⟩

/-- (15,6) の配置の符号化（各記号を 3 ビットに、ヘッドを 3 倍の位置＋桁 ce に、状態 q を併合後の [q^r] に）。 -/
def E108 (c : Cfg St Ps Sy) : Cfg Nat Ps Bool := enc E c

/-- 停止配置: (15,6) の停止配置から停止規則を 1 つ戻し、URTM(108,2) がブロックの中で止まるまで進めたもの。 -/
def fin108 (C : CTSH) (vf : List Ch) (mf : Nat) (rm : List Ch) : Cfg Nat Ps Bool :=
  pre M E (unhalt f15 (finCfg15 C vf mf rm))

/-- **主定理（(15,6) から作った URTM(108,2) は任意の CTSH を模倣する）**。`M`（生成された表）は決定的かつ可逆、
    状態は 108 個の `sts` に入り、記号は {0, 1}（`Bool`）、規則は 187 本。(15,6) の停止しない規則の 1 ステップを
    規則ごとに 3・5・7 ステップで模倣する。任意の CTSH C と初期語 w について、Morita の初期配置の符号化
    `E108 (encC15 C w)` から:

    1. C が (w, 0) から n ステップで停止 ID (vf, mf) に達するなら、M は停止し（N + 1 ≥ n）、停止配置は `fin108 C vf mf rm`。
    2. 逆に M が停止するなら C も停止し、停止配置は 1 の形。
    3. C が停止しない ⇔ M が停止しない。 -/
theorem urtm108_2_15_6_simulates_ctsh (C : CTSH) (w : List Ch) :
    Deterministic M ∧ Reversible M ∧
    (∀ ρ ∈ M, ρ.p ∈ sts ∧ ρ.q ∈ sts.map Tgt.go) ∧ sts.length = 108 ∧ M.length = 187 ∧
    (∀ r ∈ T, ∀ c : Cfg St Ps Sy, r.q.isGo = true → c.st = .go r.p → c.tape c.pos = r.s →
      StepN M (cost r) (E108 c) (E108 (fire r c)) ∧ (cost r = 3 ∨ cost r = 5 ∨ cost r = 7)) ∧
    (∀ n vf mf, CHaltsIn C n (w, 0) (vf, mf) →
      ∃ N rm, n ≤ N + 1 ∧ HaltsIn M N (E108 (encC15 C w)) (fin108 C vf mf rm)) ∧
    (∀ N e, HaltsIn M N (E108 (encC15 C w)) e →
      ∃ n vf mf rm, CHaltsIn C n (w, 0) (vf, mf) ∧ e = fin108 C vf mf rm) ∧
    ((∀ n f, ¬ CHaltsIn C n (w, 0) f) ↔ (∀ N e, ¬ HaltsIn M N (E108 (encC15 C w)) e)) := by
  have hb := urtm15_6_simulates_ctsh C w
  have hs := fs_simulates hyp hD hH156 det C w (encC15 C w) ⟨.q0, rfl⟩ (finCfg15 C)
    (finCfg15_pseudo C) ⟨hb.1, hb.2.1⟩
  refine ⟨det, rev, card.1, card.2.1, card.2.2, ?_, hs.1, hs.2.1, hs.2.2⟩
  intro r hr c hg hst hsr
  cases hq : r.q with
  | halt _ => rw [hq] at hg; cases hg
  | go q => exact ⟨step_sim hyp hr hq hst hsr, costs r hr hg⟩

end URTM.CTSH.U108_2_15_6
