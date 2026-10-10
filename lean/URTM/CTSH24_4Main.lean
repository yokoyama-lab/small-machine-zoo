/-
  URTM(24,4) が任意の CTSH を模倣すること（生成モジュールへの具体化）。

  一般証明 `URTM.CTSH.U24_4.simulates`（CTSH24_4.lean、機械の型に依らない形）を、
  記述ファイル urtm24-4.txt から生成した `URTM.Gen.K24_4` に具体化する。名前 `nm24` を与え、
  Table 7.5 の 84 本（`rules`）が生成された表 `T` と**集合として一致する**ことを `decide` で確かめてから
  一般定理を適用する。

  生成モジュールに依存するので、`tools/gen_all_lean.sh`（CI）が書く `URTM.lean` 経由でビルドされる。
  未証明の穴・新規公理・native_decide を使わない。
-/
import URTM.CTSH24_4
import URTM.Gen.K24_4

namespace URTM.CTSH.U24_4

open URTM URTM.KState URTM.CTSH URTM.Gen.K24_4

/-- 生成器のコメントどおりの対応: 記号 s0=b s1=y s2=n s3=∗、
    状態 q0=begin q1..q3=case_y_1..3 q4=copy_start q5..q9=copy_y_1..5 q10..q14=copy_n_1..5
    q15=copy_end_1 q16=copy_end_2 q17=cycle_end q18..q23=case_n_1..6、疑似状態 h0=null h1=halt。 -/
def nm24 : Names St Ps Sy :=
  { b := .s0, y := .s1, n := .s2, st := .s3,
    begin := .q0, cy1 := .q1, cy2 := .q2, cy3 := .q3, cs := .q4,
    cpy1 := .q5, cpy2 := .q6, cpy3 := .q7, cpy4 := .q8, cpy5 := .q9,
    cpn1 := .q10, cpn2 := .q11, cpn3 := .q12, cpn4 := .q13, cpn5 := .q14,
    ce1 := .q15, ce2 := .q16, cyc := .q17,
    cn1 := .q18, cn2 := .q19, cn3 := .q20, cn4 := .q21, cn5 := .q22, cn6 := .q23,
    halt := .h1, null := .h0 }

/-- Table 7.5（名前で書いた 84 本）は生成された表に含まれる。 -/
theorem rules24_sub : ∀ r ∈ rules nm24, r ∈ T := by decide
/-- 逆に、生成された表の規則はすべて Table 7.5 にある（表は 84 本ちょうど）。 -/
theorem rules24_sup : ∀ r ∈ T, r ∈ rules nm24 := by decide
theorem rules24_len : (rules nm24).length = 84 ∧ T.length = 84 := by decide

/-- Morita の初期配置（原典 p. 192）`b ϕ₁(w^R_{k−1}) ∗ ⋯ ∗ ϕ₁(w^R_1) ∗ b b q_begin ϕ₁(w) b`。 -/
def encC24 (C : CTSH) (w : List Ch) : Cfg St Ps Sy := encC nm24 C w
/-- 停止配置（`finCfg` の (24,4) 版）。 -/
def finCfg24 (C : CTSH) (vf : List Ch) (mf : Nat) (rm : List Ch) : Cfg St Ps Sy :=
  finCfg nm24 C vf mf rm

/-- **主定理（URTM(24,4) は任意の CTSH を模倣する）**。任意の CTSH C と任意の初期語 w について、
    U24_4 = `T` を Morita の初期配置 `encC24 C w` から動かすと:

    1. C が (w, 0) から n ステップで停止 ID (vf, mf) に達するなら、U24_4 は n ステップ以上で停止し、
       停止配置は `finCfg24 C vf mf rm`: vf = λ なら疑似状態 null（テープ `b · RA(mf) · b · ϕ₁(rm)`、
       ヘッドは末尾の b）、vf = Y v（mf = 0）なら halt（テープ `b · RA(0) · b · ϕ₁(rm) · ∗ · ϕ₁(v)`、
       ∗ が Y を表す。ヘッドは区切り 0 の b）。
    2. 逆に U24_4 が `encC24 C w` から停止するなら、C も (w, 0) から停止し、停止配置は 1 の形。
    3. C が停止しない ⇔ U24_4 が停止しない。 -/
theorem urtm24_4_simulates_ctsh (C : CTSH) (w : List Ch) :
    (∀ n vf mf, CHaltsIn C n (w, 0) (vf, mf) →
      ∃ N rm, n ≤ N ∧ HaltsIn T N (encC24 C w) (finCfg24 C vf mf rm)) ∧
    (∀ N e, HaltsIn T N (encC24 C w) e →
      ∃ n vf mf rm, CHaltsIn C n (w, 0) (vf, mf) ∧ e = finCfg24 C vf mf rm) ∧
    ((∀ n f, ¬ CHaltsIn C n (w, 0) f) ↔ (∀ N e, ¬ HaltsIn T N (encC24 C w) e)) :=
  simulates rules24_sub hD C w

end URTM.CTSH.U24_4
