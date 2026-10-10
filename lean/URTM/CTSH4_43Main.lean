/-
  tools/gen_symmerge_lean.py が results/symmerge-2026-10-05/records/urtm10-8.k4.r46.m43.json から生成。手で編集しないこと。

  記号の併合で URTM(4,43) になる、併合前のブロック化の表（urtm10-8 から。状態 4・記号 46・
  五つ組 157。生成モジュール `URTM.Gen.KB4_43`）が任意の CTSH を模倣すること。証明は
  CTSH4_46Main と同じ: 一般定理 `KStateBlocks.bconv_main`（生成モジュールの `main`）、基底の CTSH の模倣定理
  `URTM.CTSH.U10_8.urtm10_8_simulates_ctsh`、基底の実行が疑似状態以外で止まらないこと（`URTM.CTSH.U6_45.nostuck10`）を `compose_ctsh` で合成する。
  未証明の穴・新規公理・native_decide を使わない。
-/
import URTM.CTSH6_45Main
import URTM.Gen.KB4_43

namespace URTM.CTSH.SM4_43

open URTM URTM.KState URTM.KStateSparse URTM.KStateBlocks URTM.CTSH URTM.Gen.K10_8
open URTM.Gen.KB4_43 (spB qsB ssB TpyB symB)

/-- **併合前の表は任意の CTSH を模倣する**。T' = `bconv T spB qsB ssB`（状態は `Fin 4`・記号は 46 要素の
    `symB` に入る・規則 157 本・決定的可逆、Python の生成表 `TpyB` と一致）を符号化 `E = benc T spB` を
    通して見ると、CTSH4_46Main の主定理と同じ 3 つの対応が成り立つ。 -/
theorem blocks_simulates_ctsh (C : CTSH) (w : List Ch) :
    let T' := bconv T spB qsB ssB
    let E := benc T spB
    Deterministic T' ∧ Reversible T' ∧ (∀ x : Fin 4, ∃ ρ ∈ T', ρ.p = x) ∧
    (∀ ρ ∈ T', ρ.s ∈ symB ∧ ρ.t ∈ symB) ∧ symB.length = 46 ∧ symB.Nodup ∧
    T'.length = 157 ∧ T' = TpyB ∧
    (∀ n vf mf, CHaltsIn C n (w, 0) (vf, mf) →
      ∃ N rm, n ≤ N ∧ HaltsIn T' N (E (URTM.CTSH.U10_8.encC C w)) (E (URTM.CTSH.U10_8.finCfg C vf mf rm))) ∧
    (∀ N e, HaltsIn T' N (E (URTM.CTSH.U10_8.encC C w)) e →
      ∃ n vf mf rm, CHaltsIn C n (w, 0) (vf, mf) ∧ e = E (URTM.CTSH.U10_8.finCfg C vf mf rm)) ∧
    ((∀ n f, ¬ CHaltsIn C n (w, 0) f) ↔ (∀ N e, ¬ HaltsIn T' N (E (URTM.CTSH.U10_8.encC C w)) e)) := by
  intro T' E
  obtain ⟨hD', hR', hsym, hsl, hsn, hst, hlen, hT, -, hF, hB, hN⟩ := URTM.Gen.KB4_43.main
  exact ⟨hD', hR', hst, hsym, hsl, hsn, hlen, hT,
    compose_ctsh E (URTM.CTSH.U6_45.finCfg10_pseudo C) (URTM.CTSH.U6_45.nostuck10 C w) (URTM.CTSH.U10_8.urtm10_8_simulates_ctsh C w) hF hB hN⟩

end URTM.CTSH.SM4_43
