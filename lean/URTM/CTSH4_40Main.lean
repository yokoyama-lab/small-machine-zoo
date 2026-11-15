/-
  tools/gen_symmerge_lean.py が results/symmerge-2026-10-05/records/urtm11-7.k4.r47.m40.json から生成。手で編集しないこと。

  記号の併合で URTM(4,40) になる、併合前のブロック化の表（urtm11-7 から。状態 4・記号 47・
  五つ組 151。生成モジュール `URTM.Gen.KB4_40`）が任意の CTSH を模倣すること。証明は
  CTSH4_46Main と同じ: 一般定理 `KStateBlocks.bconv_main`（生成モジュールの `main`）、基底の CTSH の模倣定理
  `URTM.CTSH.U11_7.urtm11_7_simulates_ctsh`、基底の実行が疑似状態以外で止まらないこと（`URTM.CTSH.U11_7.nostuck11`）を `compose_ctsh` で合成する。
  未証明の穴・新規公理・native_decide を使わない。
-/
import URTM.CTSH11_7Blocks
import URTM.Gen.KB4_40

namespace URTM.CTSH.SM4_40

open URTM URTM.KState URTM.KStateSparse URTM.KStateBlocks URTM.CTSH URTM.Gen.K13_7
open URTM.CTSH.U11_7 (T11 hW11 hR11)
open URTM.Gen.KB4_40 (spB qsB ssB TpyB symB)

/-- **併合前の表は任意の CTSH を模倣する**。T' = `bconv T11 spB qsB ssB`（状態は `Fin 4`・記号は 47 要素の
    `symB` に入る・規則 151 本・決定的可逆、Python の生成表 `TpyB` と一致）を符号化 `E = benc T11 spB` を
    通して見ると、CTSH4_46Main の主定理と同じ 3 つの対応が成り立つ。 -/
theorem blocks_simulates_ctsh (C : CTSH) (w : List Ch) :
    let T' := bconv T11 spB qsB ssB
    let E := benc T11 spB
    Deterministic T' ∧ Reversible T' ∧ (∀ x : Fin 4, ∃ ρ ∈ T', ρ.p = x) ∧
    (∀ ρ ∈ T', ρ.s ∈ symB ∧ ρ.t ∈ symB) ∧ symB.length = 47 ∧ symB.Nodup ∧
    T'.length = 151 ∧ T' = TpyB ∧
    (∀ n vf mf, CHaltsIn C n (w, 0) (vf, mf) →
      ∃ N rm, n ≤ N ∧ HaltsIn T' N (E (URTM.CTSH.U11_7.encC11 C w)) (E (URTM.CTSH.U11_7.finCfg11 C vf mf rm))) ∧
    (∀ N e, HaltsIn T' N (E (URTM.CTSH.U11_7.encC11 C w)) e →
      ∃ n vf mf rm, CHaltsIn C n (w, 0) (vf, mf) ∧ e = E (URTM.CTSH.U11_7.finCfg11 C vf mf rm)) ∧
    ((∀ n f, ¬ CHaltsIn C n (w, 0) f) ↔ (∀ N e, ¬ HaltsIn T' N (E (URTM.CTSH.U11_7.encC11 C w)) e)) := by
  intro T' E
  obtain ⟨hD', hR', hsym, hsl, hsn, hst, hlen, hT, -, hF, hB, hN⟩ := URTM.Gen.KB4_40.main
  exact ⟨hD', hR', hst, hsym, hsl, hsn, hlen, hT,
    compose_ctsh E (URTM.CTSH.U11_7.finCfg11_pseudo C) (URTM.CTSH.U11_7.nostuck11 C w) (URTM.CTSH.U11_7.urtm11_7_simulates_ctsh C w) hF hB hN⟩

end URTM.CTSH.SM4_40
