/-
  URTM(17,5) と、定理 B（ブロック化）で得る URTM(7,65)・URTM(8,50) が任意の CTSH を模倣すること。

  一般証明 `URTM.CTSH.U17_5.simulates`（CTSH17_5.lean、機械の型に依らない形）を、
  記述ファイル urtm17-5.txt から生成した 3 つのモジュールに具体化する:
    * `URTM.Gen.K17_5`     : U17_5 そのもの                       → `urtm17_5_simulates_ctsh`
    * `URTM.Gen.K17_5_b21` : 定理 B の入力（blocks (2,1)、7 状態 65 記号） → `urtm7_65_simulates_ctsh`
    * `URTM.Gen.K17_5_b22` : 定理 B の入力（blocks (2,2)、8 状態 50 記号） → `urtm8_50_simulates_ctsh`
  3 つは同じ記述ファイルから同じ生成器で作られるが、状態・記号の型は別々に宣言されている。
  そこで各モジュールについて、名前 `nm*` を与え、Table 7.3 の 69 本（`rules`）が
  生成された表 `T` と**集合として一致する**ことを `decide` で確かめてから一般定理を適用する。

  生成モジュールに依存するので、`tools/gen_all_lean.sh`（CI）が書く `URTM.lean` 経由でビルドされる。
  未証明の穴・新規公理・native_decide を使わない。
-/
import URTM.CTSH17_5
import URTM.Gen.K17_5
import URTM.Gen.K17_5_b21
import URTM.Gen.K17_5_b22

namespace URTM.CTSH.U17_5

open URTM URTM.KState URTM.KStateB URTM.CTSH

/-! ## 1. URTM(17,5) -/

section U17
open URTM.Gen.K17_5

/-- 生成器のコメントどおりの対応: 記号 s0=b s1=y s2=n s3=∗ s4=$、
    状態 q0=begin q1=case_y_1 q2=case_y_2 q3=copy_start q4..q6=copy_y_1..3 q7..q9=copy_n_1..3
    q10=copy_end_1 q11=copy_end_2 q12=cycle_end q13..q16=case_n_1..4、疑似状態 h0=halt h1=null。 -/
def nm17 : Names St Ps Sy :=
  { b := .s0, y := .s1, n := .s2, st := .s3, dl := .s4,
    begin := .q0, cy1 := .q1, cy2 := .q2, cs := .q3, cpy1 := .q4, cpy2 := .q5, cpy3 := .q6,
    cpn1 := .q7, cpn2 := .q8, cpn3 := .q9, ce1 := .q10, ce2 := .q11, cyc := .q12,
    cn1 := .q13, cn2 := .q14, cn3 := .q15, cn4 := .q16, halt := .h0, null := .h1 }

/-- Table 7.3（名前で書いた 69 本）は生成された表に含まれる。 -/
theorem rules17_sub : ∀ r ∈ rules nm17, r ∈ T := by decide
/-- 逆に、生成された表の規則はすべて Table 7.3 にある（表は 69 本ちょうど）。 -/
theorem rules17_sup : ∀ r ∈ T, r ∈ rules nm17 := by decide
theorem rules17_len : (rules nm17).length = 69 ∧ T.length = 69 := by decide

/-- Morita の初期配置 `b ϕ₁(w^R_{k−1}) ∗ ⋯ ∗ ϕ₁(w^R_1) ∗ b $ q_begin ϕ₁(w) b`。 -/
def encC17 (C : CTSH) (w : List Ch) : Cfg St Ps Sy := encC nm17 C w
/-- 停止配置（`finCfg` の (17,5) 版）。 -/
def finCfg17 (C : CTSH) (vf : List Ch) (mf : Nat) (rm : List Ch) : Cfg St Ps Sy :=
  finCfg nm17 C vf mf rm

/-- **主定理（URTM(17,5) は任意の CTSH を模倣する）**。任意の CTSH C（周期 k = |C| + 1、
    生成規則 C = [w₁, …, w_{k−1}]）と任意の初期語 w について、U17_5 = `T` を
    Morita の初期配置 `encC17 C w` から動かすと:

    1. C が (w, 0) から n ステップで停止 ID (vf, mf) に達するなら、U17_5 は n ステップ以上で停止し、
       停止配置は `finCfg17 C vf mf rm`: vf = λ なら疑似状態 null（テープ `b · RA(mf) · $ · ϕ₁(rm) · $`）、
       vf = Y v（mf = 0）なら halt（テープ `b · RA(0) · b · ϕ₁(rm) · $ · ϕ₁(v)`、$ が Y を表す）。
    2. 逆に U17_5 が `encC17 C w` から停止するなら、C も (w, 0) から停止し、停止配置は 1 の形。
    3. C が停止しない ⇔ U17_5 が停止しない。 -/
theorem urtm17_5_simulates_ctsh (C : CTSH) (w : List Ch) :
    (∀ n vf mf, CHaltsIn C n (w, 0) (vf, mf) →
      ∃ N rm, n ≤ N ∧ HaltsIn T N (encC17 C w) (finCfg17 C vf mf rm)) ∧
    (∀ N e, HaltsIn T N (encC17 C w) e →
      ∃ n vf mf rm, CHaltsIn C n (w, 0) (vf, mf) ∧ e = finCfg17 C vf mf rm) ∧
    ((∀ n f, ¬ CHaltsIn C n (w, 0) f) ↔ (∀ N e, ¬ HaltsIn T N (encC17 C w) e)) :=
  simulates rules17_sub hD C w

end U17

/-! ## 2. URTM(7,65)（定理 B、blocks (2,1)） -/

section U7
open URTM.Gen.K17_5_b21

/-- `K17_5_b21` の型での同じ名前（生成器のコメントの対応は K17_5 と同一）。 -/
def nm21 : Names St Ps Sy :=
  { b := .s0, y := .s1, n := .s2, st := .s3, dl := .s4,
    begin := .q0, cy1 := .q1, cy2 := .q2, cs := .q3, cpy1 := .q4, cpy2 := .q5, cpy3 := .q6,
    cpn1 := .q7, cpn2 := .q8, cpn3 := .q9, ce1 := .q10, ce2 := .q11, cyc := .q12,
    cn1 := .q13, cn2 := .q14, cn3 := .q15, cn4 := .q16, halt := .h0, null := .h1 }

theorem rules21_sub : ∀ r ∈ rules nm21, r ∈ T := by decide
theorem rules21_sup : ∀ r ∈ T, r ∈ rules nm21 := by decide

/-- **系（URTM(7,65)）**。定理 B の変換 T' = `convB T qs ss 2 1`（決定的かつ可逆、状態は 7 要素の
    `stUniverse 2 1`、記号は 65 要素の `symUniverse 12 ss` に入る）を、定理 B の符号化 E を通して
    見ると、`urtm17_5_simulates_ctsh` と同じ 3 項が成り立つ。 -/
theorem urtm7_65_simulates_ctsh (C : CTSH) (w : List Ch) :
    let T' := convB T qs ss 2 1
    let E := KStateB.enc T (canonBlk T qs 2 1) (canonOffB T qs 2 1)
    Deterministic T' ∧ Reversible T' ∧
    (∀ ρ ∈ T', ρ.p ∈ stUniverse 2 1 ∧ ∀ x, ρ.q = .go x → x ∈ stUniverse 2 1) ∧
    (stUniverse 2 1).length = 7 ∧
    (∀ ρ ∈ T', ρ.s ∈ symUniverse 12 ss ∧ ρ.t ∈ symUniverse 12 ss) ∧
    (symUniverse 12 ss).length = 65 ∧
    (∀ n vf mf, CHaltsIn C n (w, 0) (vf, mf) →
      ∃ N rm, n ≤ N ∧ HaltsIn T' N (E (encC nm21 C w)) (E (finCfg nm21 C vf mf rm))) ∧
    (∀ N e, HaltsIn T' N (E (encC nm21 C w)) e →
      ∃ n vf mf rm, CHaltsIn C n (w, 0) (vf, mf) ∧ e = E (finCfg nm21 C vf mf rm)) ∧
    ((∀ n f, ¬ CHaltsIn C n (w, 0) f) ↔ (∀ N e, ¬ HaltsIn T' N (E (encC nm21 C w)) e)) := by
  intro T' E
  obtain ⟨hDet, hRev, -, -, hF, hB, hDiv, hSt, hSy, h7, h65, -, -⟩ := main
  exact ⟨hDet, hRev, hSt, h7, hSy, h65, Sim.simulates_enc hF hB hDiv (simulates rules21_sub hD C w)⟩

end U7

/-! ## 3. URTM(8,50)（定理 B、blocks (2,2)） -/

section U8
open URTM.Gen.K17_5_b22

/-- `K17_5_b22` の型での同じ名前。 -/
def nm22 : Names St Ps Sy :=
  { b := .s0, y := .s1, n := .s2, st := .s3, dl := .s4,
    begin := .q0, cy1 := .q1, cy2 := .q2, cs := .q3, cpy1 := .q4, cpy2 := .q5, cpy3 := .q6,
    cpn1 := .q7, cpn2 := .q8, cpn3 := .q9, ce1 := .q10, ce2 := .q11, cyc := .q12,
    cn1 := .q13, cn2 := .q14, cn3 := .q15, cn4 := .q16, halt := .h0, null := .h1 }

theorem rules22_sub : ∀ r ∈ rules nm22, r ∈ T := by decide
theorem rules22_sup : ∀ r ∈ T, r ∈ rules nm22 := by decide

/-- **系（URTM(8,50)）**。定理 B の変換 T' = `convB T qs ss 2 2`（決定的かつ可逆、状態は 8 要素の
    `stUniverse 2 2`、記号は 50 要素の `symUniverse 9 ss` に入る）を、定理 B の符号化 E を通して
    見ると、`urtm17_5_simulates_ctsh` と同じ 3 項が成り立つ。 -/
theorem urtm8_50_simulates_ctsh (C : CTSH) (w : List Ch) :
    let T' := convB T qs ss 2 2
    let E := KStateB.enc T (canonBlk T qs 2 2) (canonOffB T qs 2 2)
    Deterministic T' ∧ Reversible T' ∧
    (∀ ρ ∈ T', ρ.p ∈ stUniverse 2 2 ∧ ∀ x, ρ.q = .go x → x ∈ stUniverse 2 2) ∧
    (stUniverse 2 2).length = 8 ∧
    (∀ ρ ∈ T', ρ.s ∈ symUniverse 9 ss ∧ ρ.t ∈ symUniverse 9 ss) ∧
    (symUniverse 9 ss).length = 50 ∧
    (∀ n vf mf, CHaltsIn C n (w, 0) (vf, mf) →
      ∃ N rm, n ≤ N ∧ HaltsIn T' N (E (encC nm22 C w)) (E (finCfg nm22 C vf mf rm))) ∧
    (∀ N e, HaltsIn T' N (E (encC nm22 C w)) e →
      ∃ n vf mf rm, CHaltsIn C n (w, 0) (vf, mf) ∧ e = E (finCfg nm22 C vf mf rm)) ∧
    ((∀ n f, ¬ CHaltsIn C n (w, 0) f) ↔ (∀ N e, ¬ HaltsIn T' N (E (encC nm22 C w)) e)) := by
  intro T' E
  obtain ⟨hDet, hRev, -, -, hF, hB, hDiv, hSt, hSy, h8, h50, -, -⟩ := main
  exact ⟨hDet, hRev, hSt, h8, hSy, h50, Sim.simulates_enc hF hB hDiv (simulates rules22_sub hD C w)⟩

end U8

end URTM.CTSH.U17_5
