/-
  URTM(4,46)（ブロック分け × 役割の併合 × ε ∘ URTM(10,8)、docs/22_eps_blocks_2026-09-28.md §3.2）が
  任意の CTSH を模倣すること。

  * 一般定理 `URTM.KStateBlocks.bconv_main`（KStateBlocks.lean）は、T' が決定的であること（具体機械では
    カーネルの `decide`）と、T の実行が疑似状態以外で止まらない（`NoStuck`）ことを仮定に、
    1 ステップ・停止・非停止の対応を与える。
  * (10,8) の CTSH 模倣の主定理 `urtm10_8_simulates_ctsh`（CTSH10_8.lean）と、
    「疑似状態以外で止まらない」（`U6_45.nostuck10`、CTSH6_45Main.lean）を合成する。
  * 具体の T' = `bconv T spB qsB ssB` は生成モジュール `URTM.Gen.KB4_46`（tools/gen_blocks_lean.py）にあり、
    `tools/kstate_blocks.py` の表 `TpyB`（解は results/kstate_blocks/records/urtm4-46.json）と
    規則の並びまで一致し（`decide +kernel`）、ブロック (2,2)、状態は `Fin 4`（どれも現れる）、
    記号の全体 `symB` は 46 要素、規則は 157 本。

  生成モジュールに依存するので、`tools/gen_all_lean.sh`（CI）が書く `URTM.lean` 経由でビルドされる。
  未証明の穴・新規公理・native_decide を使わない。
-/
import URTM.CTSH6_45Main
import URTM.Gen.KB4_46

namespace URTM.CTSH.U4_46

open URTM URTM.KState URTM.KStateSparse URTM.KStateBlocks URTM.CTSH URTM.Gen.K10_8
open URTM.Gen.KB4_46 (spB qsB ssB TpyB symB)
open URTM.CTSH.U6_45 (finCfg10_pseudo nostuck10)

/-- **主定理（URTM(4,46) は任意の CTSH を模倣する）**。T' = `bconv T spB qsB ssB`
    （ブロック (2,2)・役割の併合・ε を (10,8) に適用したもの。状態は `Fin 4`・記号は 46 要素の `symB` に入る・
    規則 157 本・決定的可逆、Python の生成表 `TpyB` と一致）を符号化 `E = benc T spB` を通して見ると、
    任意の CTSH C と初期語 w について:

    1. C が (w, 0) から n ステップで停止 ID (vf, mf) に達するなら、T' は E (encC C w) から
       n ステップ以上で停止し、停止配置は E (finCfg C vf mf rm)。
    2. 逆に T' が E (encC C w) から停止するなら、C も (w, 0) から停止し、停止配置は 1 の形。
    3. C が停止しない ⇔ T' が停止しない。 -/
theorem urtm4_46_simulates_ctsh (C : CTSH) (w : List Ch) :
    let T' := bconv T spB qsB ssB
    let E := benc T spB
    Deterministic T' ∧ Reversible T' ∧ (∀ x : Fin 4, ∃ ρ ∈ T', ρ.p = x) ∧
    (∀ ρ ∈ T', ρ.s ∈ symB ∧ ρ.t ∈ symB) ∧ symB.length = 46 ∧ symB.Nodup ∧
    T'.length = 157 ∧ T' = TpyB ∧
    (∀ n vf mf, CHaltsIn C n (w, 0) (vf, mf) →
      ∃ N rm, n ≤ N ∧ HaltsIn T' N (E (U10_8.encC C w)) (E (U10_8.finCfg C vf mf rm))) ∧
    (∀ N e, HaltsIn T' N (E (U10_8.encC C w)) e →
      ∃ n vf mf rm, CHaltsIn C n (w, 0) (vf, mf) ∧ e = E (U10_8.finCfg C vf mf rm)) ∧
    ((∀ n f, ¬ CHaltsIn C n (w, 0) f) ↔ (∀ N e, ¬ HaltsIn T' N (E (U10_8.encC C w)) e)) := by
  intro T' E
  obtain ⟨hD', hR', hsym, hsl, hsn, hst, hlen, hT, -, hF, hB, hN⟩ := URTM.Gen.KB4_46.main
  exact ⟨hD', hR', hst, hsym, hsl, hsn, hlen, hT,
    compose_ctsh E (finCfg10_pseudo C) (nostuck10 C w) (U10_8.urtm10_8_simulates_ctsh C w) hF hB hN⟩

end URTM.CTSH.U4_46
