/-
  URTM(115,2)（(17,5) の記号削減: Morita 2017 Thm 5.4 の改良＋状態の併合、docs/23）が任意の CTSH を模倣すること。

  (17,5) から停止規則 2 本を除いた機械に、記号の符号（3 ビット）b 000・y 100・n 101・∗ 110・$ 111、
  先書き v と経路の型（規則ごとに 3・5・7 ステップ）を選んだ Thm 5.4 の変換を施し（178 状態）、状態を併合したもの
  （115 状態・198 本、results/fewsym/records/urtm17-5.115.merge.json。2 記号化の LNS、docs/32 §3）。
  表は生成モジュール `URTM.Gen.FS115_2_17_5`（tools/gen_fewsym_lean.py が tools/fewsym_merge.py の表をそのまま写したもの）にある。

  合成するもの:
    1. `U17_5.urtm17_5_simulates_ctsh`
    2. `FewSym.fs_simulates`（停止規則の除去 `drop_simulates` を内部で使う）に、
       規則ごとの有限の検査 `FS115_2_17_5.cert`（カーネルの `decide`）と決定性 `FS115_2_17_5.det` を渡す。

  併合した機械は「T が規則の無い配置で止まる」場合の停止を保存しないが、(17,5) を Morita の初期配置から
  動かすと停止規則の読みでしか止まらない（停止配置はどれも疑似状態、1 の逆向きから）。`fs_simulates` はこれを内部で使う。

  生成モジュールに依存するので、`tools/gen_all_lean.sh`（CI）が書く `URTM.lean` 経由でビルドされる。
  未証明の穴・新規公理・native_decide を使わない。
-/
import URTM.CTSH17_5Main
import URTM.FewSym
import URTM.Gen.FS115_2_17_5

set_option maxRecDepth 100000

namespace URTM.CTSH.U115_2_17_5

open URTM URTM.KState URTM.CTSH URTM.SimLemmas URTM.FewSym URTM.Gen.K17_5
open URTM.Gen.FS115_2_17_5 (M E cost sts hyp det rev card costs)
open URTM.CTSH.U17_5 (encC17 finCfg17 urtm17_5_simulates_ctsh)

/-- 疑似状態へ入る規則の現状態: halt ← case_y_1（q1）が b を読む、null ← case_y_2（q2）が $ を読む。 -/
def f17 : Ps → St
  | .h0 => .q1
  | .h1 => .q2

theorem hH175 : HaltRulesId T f17 := by decide

/-- (17,5) の停止配置 `finCfg17` の状態は疑似状態（null か halt）。 -/
theorem finCfg17_pseudo (C : CTSH) (vf : List Ch) (mf : Nat) (rm : List Ch) :
    ∃ h, (finCfg17 C vf mf rm).st = .halt h := by
  cases vf with
  | nil => exact ⟨_, rfl⟩
  | cons _ _ => exact ⟨_, rfl⟩

/-- (17,5) の配置の符号化（各記号を 3 ビットに、ヘッドを 3 倍の位置＋桁 ce に、状態 q を併合後の [q^r] に）。 -/
def E115 (c : Cfg St Ps Sy) : Cfg Nat Ps Bool := enc E c

/-- 停止配置: (17,5) の停止配置から停止規則を 1 つ戻し、URTM(115,2) がブロックの中で止まるまで進めたもの。 -/
def fin115 (C : CTSH) (vf : List Ch) (mf : Nat) (rm : List Ch) : Cfg Nat Ps Bool :=
  pre M E (unhalt f17 (finCfg17 C vf mf rm))

/-- **主定理（(17,5) から作った URTM(115,2) は任意の CTSH を模倣する）**。`M`（生成された表）は決定的かつ可逆、
    状態は 115 個の `sts` に入り、記号は {0, 1}（`Bool`）、規則は 198 本。(17,5) の停止しない規則の 1 ステップを
    規則ごとに 3・5・7 ステップで模倣する。任意の CTSH C と初期語 w について、Morita の初期配置の符号化
    `E115 (encC17 C w)` から:

    1. C が (w, 0) から n ステップで停止 ID (vf, mf) に達するなら、M は停止し（N + 1 ≥ n）、停止配置は `fin115 C vf mf rm`。
    2. 逆に M が停止するなら C も停止し、停止配置は 1 の形。
    3. C が停止しない ⇔ M が停止しない。 -/
theorem urtm115_2_17_5_simulates_ctsh (C : CTSH) (w : List Ch) :
    Deterministic M ∧ Reversible M ∧
    (∀ ρ ∈ M, ρ.p ∈ sts ∧ ρ.q ∈ sts.map Tgt.go) ∧ sts.length = 115 ∧ M.length = 198 ∧
    (∀ r ∈ T, ∀ c : Cfg St Ps Sy, r.q.isGo = true → c.st = .go r.p → c.tape c.pos = r.s →
      StepN M (cost r) (E115 c) (E115 (fire r c)) ∧ (cost r = 3 ∨ cost r = 5 ∨ cost r = 7)) ∧
    (∀ n vf mf, CHaltsIn C n (w, 0) (vf, mf) →
      ∃ N rm, n ≤ N + 1 ∧ HaltsIn M N (E115 (encC17 C w)) (fin115 C vf mf rm)) ∧
    (∀ N e, HaltsIn M N (E115 (encC17 C w)) e →
      ∃ n vf mf rm, CHaltsIn C n (w, 0) (vf, mf) ∧ e = fin115 C vf mf rm) ∧
    ((∀ n f, ¬ CHaltsIn C n (w, 0) f) ↔ (∀ N e, ¬ HaltsIn M N (E115 (encC17 C w)) e)) := by
  have hb := urtm17_5_simulates_ctsh C w
  have hs := fs_simulates hyp hD hH175 det C w (encC17 C w) ⟨.q0, rfl⟩ (finCfg17 C)
    (finCfg17_pseudo C) ⟨hb.1, hb.2.1⟩
  refine ⟨det, rev, card.1, card.2.1, card.2.2, ?_, hs.1, hs.2.1, hs.2.2⟩
  intro r hr c hg hst hsr
  cases hq : r.q with
  | halt _ => rw [hq] at hg; cases hg
  | go q => exact ⟨step_sim hyp hr hq hst hsr, costs r hr hg⟩

end URTM.CTSH.U115_2_17_5
