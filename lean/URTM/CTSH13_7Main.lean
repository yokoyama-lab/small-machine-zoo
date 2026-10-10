/-
  URTM(13,7) が任意の CTSH を模倣すること（生成モジュールへの具体化）。

  一般証明 `URTM.CTSH.U13_7.simulates`（CTSH13_7.lean、機械の型に依らない形）を、
  記述ファイル urtm13-7.txt から生成した `URTM.Gen.K13_7` に具体化する。名前 `nm13` を与え、
  Table 7.1 の 59 本（`rules`）が生成された表 `T` と**集合として一致する**ことを `decide` で確かめてから
  一般定理を適用する。

  生成モジュールに依存するので、`tools/gen_all_lean.sh`（CI）が書く `URTM.lean` 経由でビルドされる。
  未証明の穴・新規公理・native_decide を使わない。
-/
import URTM.CTSH13_7
import URTM.Gen.K13_7

namespace URTM.CTSH.U13_7

open URTM URTM.KState URTM.CTSH URTM.Gen.K13_7

/-- 生成器のコメントどおりの対応: 記号 s0=b s1=y s2=n s3=Y(y1) s4=N(n1) s5=∗ s6=$、
    状態 q0=begin q1=case_y_1 q2=case_y_2 q3=case_y_n q4=copy_start q5..q7=copy_y_1..3
    q8..q10=copy_n_1..3 q11=copy_end q12=cycle_end、疑似状態 h0=null h1=halt。 -/
def nm13 : Names St Ps Sy :=
  { b := .s0, y := .s1, n := .s2, Y := .s3, N := .s4, st := .s5, dl := .s6,
    begin := .q0, cy1 := .q1, cy2 := .q2, cyn := .q3, cs := .q4, cpy1 := .q5, cpy2 := .q6,
    cpy3 := .q7, cpn1 := .q8, cpn2 := .q9, cpn3 := .q10, ce := .q11, cyc := .q12,
    halt := .h1, null := .h0 }

/-- Table 7.1（名前で書いた 59 本）は生成された表に含まれる。 -/
theorem rules13_sub : ∀ r ∈ rules nm13, r ∈ T := by decide
/-- 逆に、生成された表の規則はすべて Table 7.1 にある（表は 59 本ちょうど）。 -/
theorem rules13_sup : ∀ r ∈ T, r ∈ rules nm13 := by decide
theorem rules13_len : (rules nm13).length = 59 ∧ T.length = 59 := by decide

/-- Morita の初期配置 `b ϕ₁(w^R_{k−1}) ∗ ⋯ ∗ ϕ₁(w^R_1) ∗ b $ q_begin ϕ₁(w) b`。 -/
def encC13 (C : CTSH) (w : List Ch) : Cfg St Ps Sy := encC nm13 C w
/-- 停止配置（`finCfg` の (13,7) 版）。 -/
def finCfg13 (C : CTSH) (vf : List Ch) (mf : Nat) (rm : List Ch) : Cfg St Ps Sy :=
  finCfg nm13 C vf mf rm

/-- **主定理（URTM(13,7) は任意の CTSH を模倣する）**。任意の CTSH C（周期 k = |C| + 1、
    生成規則 C = [w₁, …, w_{k−1}]）と任意の初期語 w について、U13_7 = `T` を
    Morita の初期配置 `encC13 C w` から動かすと:

    1. C が (w, 0) から n ステップで停止 ID (vf, mf) に達するなら、U13_7 は n ステップ以上で停止し、
       停止配置は `finCfg13 C vf mf rm`: vf = λ なら疑似状態 null（テープ `b · RA(mf) · $ · ϕ₁(rm)`、
       ヘッドは末尾の b）、vf = Y v（mf = 0）なら halt（テープ `b · RA(0) · $ · ϕ₁(rm) · Y · ϕ₁(v)`、
       ヘッドは区切り 0 の b）。
    2. 逆に U13_7 が `encC13 C w` から停止するなら、C も (w, 0) から停止し、停止配置は 1 の形。
    3. C が停止しない ⇔ U13_7 が停止しない。 -/
theorem urtm13_7_simulates_ctsh (C : CTSH) (w : List Ch) :
    (∀ n vf mf, CHaltsIn C n (w, 0) (vf, mf) →
      ∃ N rm, n ≤ N ∧ HaltsIn T N (encC13 C w) (finCfg13 C vf mf rm)) ∧
    (∀ N e, HaltsIn T N (encC13 C w) e →
      ∃ n vf mf rm, CHaltsIn C n (w, 0) (vf, mf) ∧ e = finCfg13 C vf mf rm) ∧
    ((∀ n f, ¬ CHaltsIn C n (w, 0) f) ↔ (∀ N e, ¬ HaltsIn T N (encC13 C w) e)) :=
  simulates rules13_sub hD C w

end URTM.CTSH.U13_7
