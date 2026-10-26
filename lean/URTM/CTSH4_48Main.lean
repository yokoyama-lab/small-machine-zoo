/-
  URTM(4,48)（ε 逆向きの 4 状態化 ∘ URTM(10,8)、docs/20_five_state_2026-09-28.md §3）が
  任意の CTSH を模倣すること。

  * 一般定理 `URTM.KStateEps.econv_main`（KStateEps.lean）は、T の実行が疑似状態以外で止まらない
    （`NoStuck`）ことを仮定に、1 ステップ・停止・非停止の対応を与える。
  * (10,8) の CTSH 模倣の主定理 `urtm10_8_simulates_ctsh`（CTSH10_8.lean）と、
    「疑似状態以外で止まらない」（`U6_45.nostuck10`、CTSH6_45Main.lean）を合成する。
  * 具体の T' = `econv T qsE ss` は生成モジュール `URTM.Gen.KE10_8`（tools/gen_eps_lean.py）にあり、
    `tools/kstate5.py`（k4, ε₋ = −1）の表 `TpyE` と規則の並びまで一致し（`decide +kernel`）、
    記号の全体 `symUniverse 5 ss` は 48 要素、規則は 153 本。

  生成モジュールに依存するので、`tools/gen_all_lean.sh`（CI）が書く `URTM.lean` 経由でビルドされる。
  未証明の穴・新規公理・native_decide を使わない。
-/
import URTM.CTSH6_45Main
import URTM.Gen.KE10_8

namespace URTM.CTSH.U4_48

open URTM URTM.KState URTM.KStateSparse URTM.KStateEps URTM.CTSH URTM.Gen.K10_8
open URTM.Gen.KE10_8 (qsE TpyE hQE econv_eq_py)
open URTM.CTSH.U6_45 (finCfg10_pseudo nostuck10)

/-- **主定理（URTM(4,48) は任意の CTSH を模倣する）**。T' = `econv T qsE ss`
    （ε 逆向きの 4 状態化を (10,8) に適用したもの。4 状態・記号は 48 要素の `symUniverse 5 ss` に入る・
    規則 153 本・決定的可逆、Python の生成表 `TpyE` と一致）を符号化 `E = enc T (ecanonOff T qsE)` を
    通して見ると、任意の CTSH C と初期語 w について:

    1. C が (w, 0) から n ステップで停止 ID (vf, mf) に達するなら、T' は E (encC C w) から
       n ステップ以上で停止し、停止配置は E (finCfg C vf mf rm)。
    2. 逆に T' が E (encC C w) から停止するなら、C も (w, 0) から停止し、停止配置は 1 の形。
    3. C が停止しない ⇔ T' が停止しない。 -/
theorem urtm4_48_simulates_ctsh (C : CTSH) (w : List Ch) :
    let T' := econv T qsE ss
    let E := enc T (ecanonOff T qsE)
    Deterministic T' ∧ Reversible T' ∧
    (∀ x : KSt, x ∈ [KSt.Hp, .Hm, .Ap, .Am]) ∧
    (∀ ρ ∈ T', ρ.s ∈ symUniverse 5 ss ∧ ρ.t ∈ symUniverse 5 ss) ∧
    (symUniverse 5 ss).length = 48 ∧ T'.length = 153 ∧ T' = TpyE ∧
    (∀ n vf mf, CHaltsIn C n (w, 0) (vf, mf) →
      ∃ N rm, n ≤ N ∧ HaltsIn T' N (E (U10_8.encC C w)) (E (U10_8.finCfg C vf mf rm))) ∧
    (∀ N e, HaltsIn T' N (E (U10_8.encC C w)) e →
      ∃ n vf mf rm, CHaltsIn C n (w, 0) (vf, mf) ∧ e = E (U10_8.finCfg C vf mf rm)) ∧
    ((∀ n f, ¬ CHaltsIn C n (w, 0) f) ↔ (∀ N e, ¬ HaltsIn T' N (E (U10_8.encC C w)) e)) := by
  intro T' E
  obtain ⟨hD', hR', -, hF, hB, hN, hsym, -⟩ := econv_main (ss := ss) hW hD hR hQE hS
  obtain ⟨hM, h48, -, h153, -⟩ := URTM.Gen.KE10_8.card
  rw [hM] at hsym
  refine ⟨hD', hR', KSt_all, hsym, h48, ?_, econv_eq_py,
    compose_ctsh E (finCfg10_pseudo C) (nostuck10 C w) (U10_8.urtm10_8_simulates_ctsh C w) hF hB hN⟩
  show (econv T qsE ss).length = 153
  rw [econv_eq_py]; exact h153

end URTM.CTSH.U4_48
