/-
  URTM(32,3) が任意の CTSH を模倣すること（生成モジュールへの具体化）。

  一般証明 `URTM.CTSH.U32_3.simulates`（CTSH32_3.lean、機械の型に依らない形）を、
  記述ファイル urtm32-3.txt から生成した `URTM.Gen.K32_3` に具体化する。名前 `nm32` を与え、
  Table 7.6 の 84 本（`rules`）が生成された表 `T` と**集合として一致する**ことを `decide` で確かめてから
  一般定理を適用する。

  生成モジュールに依存するので、`tools/gen_all_lean.sh`（CI）が書く `URTM.lean` 経由でビルドされる。
  未証明の穴・新規公理・native_decide を使わない。
-/
import URTM.CTSH32_3
import URTM.Gen.K32_3

namespace URTM.CTSH.U32_3

open URTM URTM.KState URTM.CTSH URTM.Gen.K32_3

/-- 生成器のコメントどおりの対応: 記号 s0=b s1=y s2=n、状態 q0=begin q1..q7=case_y_1..7
    q8=copy_start_1 q9=copy_start_2 q10..q13=copy_y_1..4 q14..q17=copy_next_1..4 q18..q21=copy_n_1..4
    q22=copy_end_1 q23=copy_end_2 q24=cycle_end q25..q31=case_n_1..7、疑似状態 h0=null h1=halt。 -/
def nm32 : Names St Ps Sy :=
  { b := .s0, y := .s1, n := .s2,
    begin := .q0, cy1 := .q1, cy2 := .q2, cy3 := .q3, cy4 := .q4, cy5 := .q5, cy6 := .q6, cy7 := .q7,
    cs1 := .q8, cs2 := .q9, cpy1 := .q10, cpy2 := .q11, cpy3 := .q12, cpy4 := .q13,
    cnx1 := .q14, cnx2 := .q15, cnx3 := .q16, cnx4 := .q17,
    cpn1 := .q18, cpn2 := .q19, cpn3 := .q20, cpn4 := .q21,
    ce1 := .q22, ce2 := .q23, cyc := .q24,
    cn1 := .q25, cn2 := .q26, cn3 := .q27, cn4 := .q28, cn5 := .q29, cn6 := .q30, cn7 := .q31,
    halt := .h1, null := .h0 }

/-- Table 7.6（名前で書いた 84 本）は生成された表に含まれる。 -/
theorem rules32_sub : ∀ r ∈ rules nm32, r ∈ T := by decide
/-- 逆に、生成された表の規則はすべて Table 7.6 にある（表は 84 本ちょうど）。 -/
theorem rules32_sup : ∀ r ∈ T, r ∈ rules nm32 := by decide
theorem rules32_len : (rules nm32).length = 84 ∧ T.length = 84 := by decide

/-- Morita の初期配置（原典 p. 194）`b ϕ₂(w^R_{k−1}) nn ⋯ nn ϕ₂(w^R_1) nn nb b q_begin ϕ₁(w) b`。 -/
def encC32 (C : CTSH) (w : List Ch) : Cfg St Ps Sy := encC nm32 C w
/-- 停止配置（`finCfg` の (32,3) 版）。 -/
def finCfg32 (C : CTSH) (vf : List Ch) (mf : Nat) (rm : List Ch) : Cfg St Ps Sy :=
  finCfg nm32 C vf mf rm

/-- **主定理（URTM(32,3) は任意の CTSH を模倣する）**。任意の CTSH C と任意の初期語 w について、
    U32_3 = `T` を Morita の初期配置 `encC32 C w` から動かすと:

    1. C が (w, 0) から n ステップで停止 ID (vf, mf) に達するなら、U32_3 は n ステップ以上で停止し、
       停止配置は `finCfg32 C vf mf rm`: vf = λ なら疑似状態 null（テープ `b · RA(mf) · b · ϕ₁(rm)`、
       ヘッドは末尾の b）、vf = Y v（mf = 0）なら halt（テープ `b · RA(0) · b · ϕ₁(rm) · b · ϕ₁(v)`、
       最後の b が Y を表す。ヘッドは相 0 のマーカー nb の b）。
    2. 逆に U32_3 が `encC32 C w` から停止するなら、C も (w, 0) から停止し、停止配置は 1 の形。
    3. C が停止しない ⇔ U32_3 が停止しない。 -/
theorem urtm32_3_simulates_ctsh (C : CTSH) (w : List Ch) :
    (∀ n vf mf, CHaltsIn C n (w, 0) (vf, mf) →
      ∃ N rm, n ≤ N ∧ HaltsIn T N (encC32 C w) (finCfg32 C vf mf rm)) ∧
    (∀ N e, HaltsIn T N (encC32 C w) e →
      ∃ n vf mf rm, CHaltsIn C n (w, 0) (vf, mf) ∧ e = finCfg32 C vf mf rm) ∧
    ((∀ n f, ¬ CHaltsIn C n (w, 0) f) ↔ (∀ N e, ¬ HaltsIn T N (encC32 C w) e)) :=
  simulates rules32_sub hD C w

end URTM.CTSH.U32_3
