/-
  URTM(85,2)（Morita 2017 Thm 5.4 の改良＋状態の併合、docs/23 §1–2 の構成、autoresearch の記録）が任意の CTSH を模倣すること。

  U85_2 は U13_7 から停止規則 2 本を除いた機械に、記号の符号（3 ビット）b 000・y 100・n 101・y1 001・n1 010・∗ 110・$ 111、
  先書き v と経路の型（規則ごとに 3・5・7 ステップ）を選んだ Thm 5.4 の変換を施し（137 状態）、状態を併合したもの
  （85 状態・153 本、autoresearch/frontier/search_lib/records/urtm13-7.85.merge.json）。表は生成モジュール `URTM.Gen.FS85_2`
  （tools/gen_fewsym_lean.py が tools/fewsym_merge.py の表をそのまま写したもの）にある。

  合成するもの:
    1. `U13_7.urtm13_7_simulates_ctsh`（CTSH13_7Main.lean）
    2. `FewSym.fs_simulates`（FewSym.lean。停止規則の除去 `drop_simulates` を内部で使う）に、
       規則ごとの有限の検査 `FS85_2.cert`（カーネルの `decide`）と決定性 `FS85_2.det` を渡す。

  併合した機械は「T が規則の無い配置で止まる」場合の停止を保存しないが、(13,7) を Morita の初期配置から
  動かすと停止規則の読みでしか止まらない（`nostuck13`、1 の逆向きから）。`fs_simulates` はこれを内部で
  同じ形で使う。

  生成モジュールに依存するので、`tools/gen_all_lean.sh`（CI）が書く `URTM.lean` 経由でビルドされる。
  未証明の穴・新規公理・native_decide を使わない。
-/
import URTM.CTSH13_7Main
import URTM.KStateSparse
import URTM.Gen.FS85_2

set_option maxRecDepth 100000

namespace URTM.CTSH.U85_2

open URTM URTM.KState URTM.CTSH URTM.SimLemmas URTM.FewSym URTM.Gen.K13_7
open URTM.KStateSparse (NoStuck)
open URTM.Gen.FS85_2 (M E cost sts hyp det rev card costs)
open URTM.CTSH.U13_7 (encC13 finCfg13 urtm13_7_simulates_ctsh)

/-- 疑似状態へ入る規則の現状態: null ← begin（q0）、halt ← case_y_1（q1）。 -/
def f13 : Ps → St
  | .h0 => .q0
  | .h1 => .q1

theorem hH13 : HaltRulesId T f13 := by decide

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

/-- U13_7 の配置の符号化（各記号を 3 ビットに、ヘッドを 3 倍の位置＋桁 ce に、状態 q を併合後の [q^r] に）。 -/
def E85 (c : Cfg St Ps Sy) : Cfg Nat Ps Bool := enc E c

/-- 停止配置: U13_7 の停止配置から停止規則を 1 つ戻し（begin / case_y_1 が b を読む配置）、
    U85_2 がブロックの中で止まるまで進めたもの。 -/
def fin85 (C : CTSH) (vf : List Ch) (mf : Nat) (rm : List Ch) : Cfg Nat Ps Bool :=
  pre M E (unhalt f13 (finCfg13 C vf mf rm))

/-- **主定理（URTM(85,2) は任意の CTSH を模倣する）**。U85_2 = `M`（生成された表）は決定的かつ可逆、
    状態は 85 個の `sts` に入り、記号は {0, 1}（`Bool`）、規則は 153 本。U13_7 の停止しない規則の 1 ステップを
    規則ごとに 3・5・7 ステップで模倣する。任意の CTSH C と初期語 w について、Morita の初期配置の符号化
    `E85 (encC13 C w)` から:

    1. C が (w, 0) から n ステップで停止 ID (vf, mf) に達するなら、U85_2 は停止し（N + 1 ≥ n）、停止配置は `fin85 C vf mf rm`。
    2. 逆に U85_2 が停止するなら C も停止し、停止配置は 1 の形。
    3. C が停止しない ⇔ U85_2 が停止しない。 -/
theorem urtm85_2_simulates_ctsh (C : CTSH) (w : List Ch) :
    Deterministic M ∧ Reversible M ∧
    (∀ ρ ∈ M, ρ.p ∈ sts ∧ ρ.q ∈ sts.map Tgt.go) ∧ sts.length = 85 ∧ M.length = 153 ∧
    (∀ r ∈ T, ∀ c : Cfg St Ps Sy, r.q.isGo = true → c.st = .go r.p → c.tape c.pos = r.s →
      StepN M (cost r) (E85 c) (E85 (fire r c)) ∧ (cost r = 3 ∨ cost r = 5 ∨ cost r = 7)) ∧
    (∀ n vf mf, CHaltsIn C n (w, 0) (vf, mf) →
      ∃ N rm, n ≤ N + 1 ∧ HaltsIn M N (E85 (encC13 C w)) (fin85 C vf mf rm)) ∧
    (∀ N e, HaltsIn M N (E85 (encC13 C w)) e →
      ∃ n vf mf rm, CHaltsIn C n (w, 0) (vf, mf) ∧ e = fin85 C vf mf rm) ∧
    ((∀ n f, ¬ CHaltsIn C n (w, 0) f) ↔ (∀ N e, ¬ HaltsIn M N (E85 (encC13 C w)) e)) := by
  have h13 := urtm13_7_simulates_ctsh C w
  have hs := fs_simulates hyp hD hH13 det C w (encC13 C w) ⟨.q0, rfl⟩ (finCfg13 C) (finCfg13_pseudo C)
    ⟨h13.1, h13.2.1⟩
  refine ⟨det, rev, card.1, card.2.1, card.2.2, ?_, hs.1, hs.2.1, hs.2.2⟩
  intro r hr c hg hst hsr
  cases hq : r.q with
  | halt _ => rw [hq] at hg; cases hg
  | go q => exact ⟨step_sim hyp hr hq hst hsr, costs r hr hg⟩

end URTM.CTSH.U85_2
