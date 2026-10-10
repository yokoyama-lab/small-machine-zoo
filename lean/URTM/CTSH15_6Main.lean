/-
  URTM(15,6) が任意の CTSH を模倣すること（生成モジュールへの具体化）。

  一般証明 `URTM.CTSH.U15_6.simulates`（CTSH15_6.lean、機械の型に依らない形）を、
  記述ファイル urtm15-6.txt から生成した `URTM.Gen.K15_6` に具体化する。名前 `nm15` を与え、
  Table 7.4 の 64 本（`rules`）が生成された表 `T` と**集合として一致する**ことを `decide` で確かめてから
  一般定理を適用する。

  生成モジュールに依存するので、`tools/gen_all_lean.sh`（CI）が書く `URTM.lean` 経由でビルドされる。
  未証明の穴・新規公理・native_decide を使わない。
-/
import URTM.CTSH15_6
import URTM.Gen.K15_6

namespace URTM.CTSH.U15_6

open URTM URTM.KState URTM.CTSH URTM.Gen.K15_6

/-- 生成器のコメントどおりの対応: 記号 s0=b s1=y s2=n s3=∗ s4=$ s5=yd、
    状態 q0=begin q1=case_y_1 q2=case_y_2 q3=copy_start q4=copy_y q5=copy_n q6=copy_next_1
    q7=copy_next_2 q8=copy_end_1 q9=copy_end_2 q10=cycle_end q11..q14=case_n_1..4、
    疑似状態 h0=halt h1=null。 -/
def nm15 : Names St Ps Sy :=
  { b := .s0, y := .s1, n := .s2, st := .s3, dl := .s4, yd := .s5,
    begin := .q0, cy1 := .q1, cy2 := .q2, cs := .q3, cpy := .q4, cpn := .q5, cnx1 := .q6,
    cnx2 := .q7, ce1 := .q8, ce2 := .q9, cyc := .q10, cn1 := .q11, cn2 := .q12, cn3 := .q13,
    cn4 := .q14, halt := .h0, null := .h1 }

/-- Table 7.4（名前で書いた 64 本）は生成された表に含まれる。 -/
theorem rules15_sub : ∀ r ∈ rules nm15, r ∈ T := by decide
/-- 逆に、生成された表の規則はすべて Table 7.4 にある（表は 64 本ちょうど）。 -/
theorem rules15_sup : ∀ r ∈ T, r ∈ rules nm15 := by decide
theorem rules15_len : (rules nm15).length = 64 ∧ T.length = 64 := by decide

/-- Morita の初期配置 `b ϕ₁(w^R_{k−1}) ∗ ⋯ ∗ ϕ₁(w^R_1) ∗ b $ q_begin ϕ₁(w) b`。 -/
def encC15 (C : CTSH) (w : List Ch) : Cfg St Ps Sy := encC nm15 C w
/-- 停止配置（`finCfg` の (15,6) 版。形は (17,5) と同じ）。 -/
def finCfg15 (C : CTSH) (vf : List Ch) (mf : Nat) (rm : List Ch) : Cfg St Ps Sy :=
  finCfg nm15 C vf mf rm

/-- **主定理（URTM(15,6) は任意の CTSH を模倣する）**。任意の CTSH C と任意の初期語 w について、
    U15_6 = `T` を Morita の初期配置 `encC15 C w` から動かすと:

    1. C が (w, 0) から n ステップで停止 ID (vf, mf) に達するなら、U15_6 は n ステップ以上で停止し、
       停止配置は `finCfg15 C vf mf rm`: vf = λ なら疑似状態 null（テープ `b · RA(mf) · $ · ϕ₁(rm) · $`）、
       vf = Y v（mf = 0）なら halt（テープ `b · RA(0) · b · ϕ₁(rm) · $ · ϕ₁(v)`、$ が Y を表す）。
    2. 逆に U15_6 が `encC15 C w` から停止するなら、C も (w, 0) から停止し、停止配置は 1 の形。
    3. C が停止しない ⇔ U15_6 が停止しない。 -/
theorem urtm15_6_simulates_ctsh (C : CTSH) (w : List Ch) :
    (∀ n vf mf, CHaltsIn C n (w, 0) (vf, mf) →
      ∃ N rm, n ≤ N ∧ HaltsIn T N (encC15 C w) (finCfg15 C vf mf rm)) ∧
    (∀ N e, HaltsIn T N (encC15 C w) e →
      ∃ n vf mf rm, CHaltsIn C n (w, 0) (vf, mf) ∧ e = finCfg15 C vf mf rm) ∧
    ((∀ n f, ¬ CHaltsIn C n (w, 0) f) ↔ (∀ N e, ¬ HaltsIn T N (encC15 C w) e)) :=
  simulates rules15_sub hD C w

end URTM.CTSH.U15_6
