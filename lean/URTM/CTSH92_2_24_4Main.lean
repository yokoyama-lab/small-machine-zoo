/-
  URTM(92,2)（(24,4) の記号削減: Morita 2017 Thm 5.4 の改良＋状態の併合、docs/23）が任意の CTSH を模倣すること。

  (24,4) から停止規則 2 本を除いた機械に、記号の符号（2 ビット）b 00・y 10・n 11・∗ 01、
  先書き v と経路の型（規則ごとに 2・4 ステップ）を選んだ Thm 5.4 の変換を施し（132 状態）、状態を併合したもの
  （92 状態・176 本、results/fewsym/records/urtm24-4.92.merge.json。2 記号化の LNS、docs/32 §3）。
  表は生成モジュール `URTM.Gen.FS92_2_24_4`（tools/gen_fewsym_lean.py が tools/fewsym_merge.py の表をそのまま写したもの）にある。
  (13,7) から作った URTM(92,2)（`CTSH92_2Main.lean`）とは別の機械。

  合成するもの:
    1. `U24_4.urtm24_4_simulates_ctsh`
    2. `FewSym.fs_simulates`（停止規則の除去 `drop_simulates` を内部で使う）に、
       規則ごとの有限の検査 `FS92_2_24_4.cert`（カーネルの `decide`）と決定性 `FS92_2_24_4.det` を渡す。

  併合した機械は「T が規則の無い配置で止まる」場合の停止を保存しないが、(24,4) を Morita の初期配置から
  動かすと停止規則の読みでしか止まらない（停止配置はどれも疑似状態、1 の逆向きから）。`fs_simulates` はこれを内部で使う。

  生成モジュールに依存するので、`tools/gen_all_lean.sh`（CI）が書く `URTM.lean` 経由でビルドされる。
  未証明の穴・新規公理・native_decide を使わない。
-/
import URTM.CTSH24_4Main
import URTM.FewSym
import URTM.Gen.FS92_2_24_4

set_option maxRecDepth 100000

namespace URTM.CTSH.U92_2_24_4

open URTM URTM.KState URTM.CTSH URTM.SimLemmas URTM.FewSym URTM.Gen.K24_4
open URTM.Gen.FS92_2_24_4 (M E cost sts hyp det rev card costs)
open URTM.CTSH.U24_4 (encC24 finCfg24 urtm24_4_simulates_ctsh)

/-- 疑似状態へ入る規則の現状態: null ← begin（q0）、halt ← case_y_2（q2）。 -/
def f24 : Ps → St
  | .h0 => .q0
  | .h1 => .q2

theorem hH244 : HaltRulesId T f24 := by decide

/-- (24,4) の停止配置 `finCfg24` の状態は疑似状態（null か halt）。 -/
theorem finCfg24_pseudo (C : CTSH) (vf : List Ch) (mf : Nat) (rm : List Ch) :
    ∃ h, (finCfg24 C vf mf rm).st = .halt h := by
  cases vf with
  | nil => exact ⟨_, rfl⟩
  | cons _ _ => exact ⟨_, rfl⟩

/-- (24,4) の配置の符号化（各記号を 2 ビットに、ヘッドを 2 倍の位置＋桁 ce に、状態 q を併合後の [q^r] に）。 -/
def E92 (c : Cfg St Ps Sy) : Cfg Nat Ps Bool := enc E c

/-- 停止配置: (24,4) の停止配置から停止規則を 1 つ戻し、URTM(92,2) がブロックの中で止まるまで進めたもの。 -/
def fin92 (C : CTSH) (vf : List Ch) (mf : Nat) (rm : List Ch) : Cfg Nat Ps Bool :=
  pre M E (unhalt f24 (finCfg24 C vf mf rm))

/-- **主定理（(24,4) から作った URTM(92,2) は任意の CTSH を模倣する）**。`M`（生成された表）は決定的かつ可逆、
    状態は 92 個の `sts` に入り、記号は {0, 1}（`Bool`）、規則は 176 本。(24,4) の停止しない規則の 1 ステップを
    規則ごとに 2・4 ステップで模倣する。任意の CTSH C と初期語 w について、Morita の初期配置の符号化
    `E92 (encC24 C w)` から:

    1. C が (w, 0) から n ステップで停止 ID (vf, mf) に達するなら、M は停止し（N + 1 ≥ n）、停止配置は `fin92 C vf mf rm`。
    2. 逆に M が停止するなら C も停止し、停止配置は 1 の形。
    3. C が停止しない ⇔ M が停止しない。 -/
theorem urtm92_2_24_4_simulates_ctsh (C : CTSH) (w : List Ch) :
    Deterministic M ∧ Reversible M ∧
    (∀ ρ ∈ M, ρ.p ∈ sts ∧ ρ.q ∈ sts.map Tgt.go) ∧ sts.length = 92 ∧ M.length = 176 ∧
    (∀ r ∈ T, ∀ c : Cfg St Ps Sy, r.q.isGo = true → c.st = .go r.p → c.tape c.pos = r.s →
      StepN M (cost r) (E92 c) (E92 (fire r c)) ∧ (cost r = 2 ∨ cost r = 4)) ∧
    (∀ n vf mf, CHaltsIn C n (w, 0) (vf, mf) →
      ∃ N rm, n ≤ N + 1 ∧ HaltsIn M N (E92 (encC24 C w)) (fin92 C vf mf rm)) ∧
    (∀ N e, HaltsIn M N (E92 (encC24 C w)) e →
      ∃ n vf mf rm, CHaltsIn C n (w, 0) (vf, mf) ∧ e = fin92 C vf mf rm) ∧
    ((∀ n f, ¬ CHaltsIn C n (w, 0) f) ↔ (∀ N e, ¬ HaltsIn M N (E92 (encC24 C w)) e)) := by
  have hb := urtm24_4_simulates_ctsh C w
  have hs := fs_simulates hyp hD hH244 det C w (encC24 C w) ⟨.q0, rfl⟩ (finCfg24 C)
    (finCfg24_pseudo C) ⟨hb.1, hb.2.1⟩
  refine ⟨det, rev, card.1, card.2.1, card.2.2, ?_, hs.1, hs.2.1, hs.2.2⟩
  intro r hr c hg hst hsr
  cases hq : r.q with
  | halt _ => rw [hq] at hg; cases hg
  | go q => exact ⟨step_sim hyp hr hq hst hsr, costs r hr hg⟩

end URTM.CTSH.U92_2_24_4
