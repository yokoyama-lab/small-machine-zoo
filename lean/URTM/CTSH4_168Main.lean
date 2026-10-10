/-
  URTM(4,168)（Morita 2017, §7.3.8.1）が任意の CTSH を模倣すること。

  原典: U4_168 は U10_8 を Theorem 5.5（§5.3.4、4 状態化）で変換したもの（「δ4_168 has 381 quintuples」）。
  記述ファイル urtm4-168.txt の表が、U10_8 から停止規則 2 本（null・halt への 0 シフト）を除いた機械に
  Theorem 5.5 の変換をそのまま適用したものと**集合として一致する**ことを `decide` で確かめ
  （状態の番号は urtm10-8.txt の states の順 = 原典 p. 198 の番号 0..9）、次の 3 つを合成する:

    1. `U10_8.urtm10_8_simulates_ctsh`（CTSH10_8.lean）
    2. `SimLemmas.drop_simulates`（停止規則の除去。停止配置は停止規則を適用する直前の配置に戻る）
    3. `Conv55.conv_simulates`（Theorem 5.5 の変換の一般の模倣証明）

  生成モジュールに依存するので、`tools/gen_all_lean.sh`（CI）が書く `URTM.lean` 経由でビルドされる。
  未証明の穴・新規公理・native_decide を使わない。
-/
import URTM.CTSH10_8
import URTM.Conv55
import URTM.Gen.F4_168

set_option maxRecDepth 100000

namespace URTM.CTSH.U4_168

open URTM URTM.KState URTM.CTSH URTM.SimLemmas URTM.Conv55 URTM.Gen.K10_8 URTM.Gen.F4_168
open URTM.CTSH.U10_8 (encC finCfg urtm10_8_simulates_ctsh)

/-- U10_8 から停止規則を除いた機械（61 本）。 -/
def T10' : Machine St Ps Sy := dropHalt T

/-- 疑似状態へ入る規則の現状態: null ← begin（q0）、halt ← case_y_1（q1）。 -/
def f10 : Ps → St
  | .h0 => .q0
  | .h1 => .q1

/-- 状態の番号（urtm10-8.txt の states の順。原典 p. 198 の 0..9）。 -/
def idx10 : St → Nat
  | .q0 => 0 | .q1 => 1 | .q2 => 2 | .q3 => 3 | .q4 => 4
  | .q5 => 5 | .q6 => 6 | .q7 => 7 | .q8 => 8 | .q9 => 9

/-- 状態に入る向きが + か（原典の Q+）。T10' の規則から読む。 -/
def side10 (q : St) : Bool := T10'.any (fun r => r.q == .go q && r.d == .R)

theorem hH10 : HaltRulesId T f10 := by decide
theorem len10' : T10'.length = 61 := by decide

theorem hyp10 : Hyp T10' idx10 10 side10 ss where
  hS := hS
  hidx := by intro q; cases q <;> decide
  hinj := by intro p q h; cases p <;> cases q <;> first | rfl | exact absurd h (by decide)
  hG := by decide
  hside := by decide

/-- 記述ファイルの表（381 本）は、T10' に Theorem 5.5 の変換を適用したものに含まれる。 -/
theorem rules4_sub : ∀ ρ ∈ T4, ρ ∈ conv T10' idx10 10 side10 ss := by decide +kernel
/-- 逆に、変換の規則はすべて記述ファイルの表にある。 -/
theorem rules4_sup : ∀ ρ ∈ conv T10' idx10 10 side10 ss, ρ ∈ T4 := by decide +kernel
theorem len4 : T4.length = 381 := by decide

theorem sub10' : ∀ r ∈ T10', r ∈ T := fun _ hr => (mem_dropHalt.mp hr).1

/-- 決定性: T10' ⊆ U10_8 は決定的なので、変換も決定的（`conv_det`）。記述ファイルの表はその部分集合。 -/
theorem hD4 : Deterministic T4 :=
  Deterministic.mono rules4_sub (conv_det (Deterministic.mono sub10' hD) hyp10.hinj)
/-- 可逆性: 同様に `conv_rev`（原典 Theorem 5.5 の証明）。 -/
theorem hR4 : Reversible T4 :=
  Reversible.mono rules4_sub (conv_rev (Reversible.mono sub10' hR) hyp10.hinj hyp10.hside)

/-- U4_168 の記号の全体（原典の S4_168 = S ∪ S × {0↑..9↑} ∪ S × {0↓..9↓}、168 個）。 -/
def syms4 : List (FSym Sy) :=
  ss.map .pl ++ ss.flatMap (fun u => (List.range 10).flatMap (fun i => [.up u i, .dn u i]))

theorem syms4_ok : (∀ ρ ∈ T4, ρ.s ∈ syms4 ∧ ρ.t ∈ syms4) ∧ syms4.length = 168 := by decide +kernel

/-- U10_8 の配置の符号化（ヘッドの記号 s を [s, i↑]、状態 p_i を R0 / L0 に）。 -/
def E (c : Cfg St Ps Sy) : Cfg FSt Ps (FSym Sy) := enc idx10 side10 c

/-- 停止配置: U10_8 の停止配置から停止規則を 1 つ戻し（begin / case_y_1 が b を読む配置）、符号化したもの。 -/
def fin4 (C : CTSH) (vf : List Ch) (mf : Nat) (rm : List Ch) : Cfg FSt Ps (FSym Sy) :=
  E (unhalt f10 (finCfg C vf mf rm))

/-- **主定理（URTM(4,168) は任意の CTSH を模倣する）**。U4_168 = `T4`（記述ファイルの表）は決定的かつ可逆、
    記号は 168 個の `syms4` に入り、任意の CTSH C と初期語 w について、Morita の初期配置
    `E (encC C w)`（= `b ϕ₁(w^R_{k−1}) ∗ ⋯ ∗ ϕ₁(w^R_1) ∗ b $ R0 [ϕ₁(s), 0↑] ϕ₁(v) b`、w = s v）から:

    1. C が (w, 0) から n ステップで停止 ID (vf, mf) に達するなら、U4_168 は停止し（N + 1 ≥ n）、停止配置は
       `fin4 C vf mf rm`（U10_8 の停止配置から停止規則を戻して符号化したもの）。
    2. 逆に U4_168 が停止するなら C も停止し、停止配置は 1 の形。
    3. C が停止しない ⇔ U4_168 が停止しない。 -/
theorem urtm4_168_simulates_ctsh (C : CTSH) (w : List Ch) :
    Deterministic T4 ∧ Reversible T4 ∧
    (∀ ρ ∈ T4, ρ.s ∈ syms4 ∧ ρ.t ∈ syms4) ∧ syms4.length = 168 ∧
    (∀ n vf mf, CHaltsIn C n (w, 0) (vf, mf) →
      ∃ N rm, n ≤ N + 1 ∧ HaltsIn T4 N (E (encC C w)) (fin4 C vf mf rm)) ∧
    (∀ N e, HaltsIn T4 N (E (encC C w)) e →
      ∃ n vf mf rm, CHaltsIn C n (w, 0) (vf, mf) ∧ e = fin4 C vf mf rm) ∧
    ((∀ n f, ¬ CHaltsIn C n (w, 0) f) ↔ (∀ N e, ¬ HaltsIn T4 N (E (encC C w)) e)) := by
  have h10 := urtm10_8_simulates_ctsh C w
  have hfin : ∀ vf mf rm, ∃ h, (finCfg C vf mf rm).st = .halt h := by
    intro vf mf rm; cases vf <;> exact ⟨_, rfl⟩
  have hd := drop_simulates hD hH10 C w (encC C w) ⟨.q0, rfl⟩ (finCfg C) hfin ⟨h10.1, h10.2.1⟩
  have hDc : Deterministic (conv T10' idx10 10 side10 ss) := Deterministic.mono rules4_sup hD4
  have hc := conv_simulates hyp10 hDc C w (encC C w) ⟨.q0, rfl⟩
    (fun vf mf rm => unhalt f10 (finCfg C vf mf rm)) ⟨hd.1, hd.2.1⟩
  refine ⟨hD4, hR4, syms4_ok.1, syms4_ok.2, ?_, ?_, ?_⟩
  · intro n vf mf h
    obtain ⟨N, rm, hN, hh⟩ := hc.1 n vf mf h
    exact ⟨N, rm, hN, HaltsIn.congr rules4_sup rules4_sub hh⟩
  · intro N e he
    exact hc.2.1 N e (HaltsIn.congr rules4_sub rules4_sup he)
  · rw [hc.2.2]
    exact ⟨fun h N e he => h N e (HaltsIn.congr rules4_sub rules4_sup he),
      fun h N e he => h N e (HaltsIn.congr rules4_sup rules4_sub he)⟩

end URTM.CTSH.U4_168
