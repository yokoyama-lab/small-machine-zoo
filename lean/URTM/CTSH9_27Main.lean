/-
  URTM(9,27)（ブロック分け × 役割の併合 × ε ∘ URTM(15,6)、docs/22_eps_blocks_2026-09-28.md §1 の枠組み、autoresearch の記録）が
  任意の CTSH を模倣すること。

  * 一般定理 `URTM.KStateBlocks.bconv_main`（KStateBlocks.lean）は、T' が決定的であること（具体機械では
    カーネルの `decide`）と、T の実行が疑似状態以外で止まらない（`NoStuck`）ことを仮定に、
    1 ステップ・停止・非停止の対応を与える。
  * (15,6) の CTSH 模倣の主定理 `urtm15_6_simulates_ctsh`（CTSH15_6Main.lean）と、
    「疑似状態以外で止まらない」（`U9_37.nostuck15`、CTSH9_37Main.lean）を合成する。
  * 具体の T' = `bconv T spB qsB ssB` は生成モジュール `URTM.Gen.KB9_27`（tools/gen_blocks_lean.py）にあり、
    `tools/kstate_blocks.py` の表 `TpyB`（解は autoresearch/frontier/search_lib/records/kb_urtm15-6.9-27.json）と
    規則の並びまで一致し（`decide +kernel`）、ブロック (5,4)、状態は `Fin 9`（どれも現れる）、
    記号の全体 `symB` は 27 要素、規則は 164 本。

  生成モジュールに依存するので、`tools/gen_all_lean.sh`（CI）が書く `URTM.lean` 経由でビルドされる。
  未証明の穴・新規公理・native_decide を使わない。
-/
import URTM.CTSH9_37Main
import URTM.Gen.KB9_27

namespace URTM.CTSH.U9_27

open URTM URTM.KState URTM.KStateSparse URTM.KStateBlocks URTM.CTSH URTM.Gen.K15_6
open URTM.Gen.KB9_27 (spB qsB ssB TpyB symB)
open URTM.CTSH.U9_37 (finCfg15_pseudo nostuck15)
open URTM.CTSH.U15_6 (encC15 finCfg15 urtm15_6_simulates_ctsh)

/-- **主定理（URTM(9,27) は任意の CTSH を模倣する）**。T' = `bconv T spB qsB ssB`
    （ブロック (5,4)・役割の併合・ε を (15,6) に適用したもの。状態は `Fin 9`・記号は 27 要素の `symB` に入る・
    規則 164 本・決定的可逆、Python の生成表 `TpyB` と一致）を符号化 `E = benc T spB` を通して見ると、
    任意の CTSH C と初期語 w について:

    1. C が (w, 0) から n ステップで停止 ID (vf, mf) に達するなら、T' は E (encC C w) から
       n ステップ以上で停止し、停止配置は E (finCfg C vf mf rm)。
    2. 逆に T' が E (encC C w) から停止するなら、C も (w, 0) から停止し、停止配置は 1 の形。
    3. C が停止しない ⇔ T' が停止しない。 -/
theorem urtm9_27_simulates_ctsh (C : CTSH) (w : List Ch) :
    let T' := bconv T spB qsB ssB
    let E := benc T spB
    Deterministic T' ∧ Reversible T' ∧ (∀ x : Fin 9, ∃ ρ ∈ T', ρ.p = x) ∧
    (∀ ρ ∈ T', ρ.s ∈ symB ∧ ρ.t ∈ symB) ∧ symB.length = 27 ∧ symB.Nodup ∧
    T'.length = 164 ∧ T' = TpyB ∧
    (∀ n vf mf, CHaltsIn C n (w, 0) (vf, mf) →
      ∃ N rm, n ≤ N ∧ HaltsIn T' N (E (encC15 C w)) (E (finCfg15 C vf mf rm))) ∧
    (∀ N e, HaltsIn T' N (E (encC15 C w)) e →
      ∃ n vf mf rm, CHaltsIn C n (w, 0) (vf, mf) ∧ e = E (finCfg15 C vf mf rm)) ∧
    ((∀ n f, ¬ CHaltsIn C n (w, 0) f) ↔ (∀ N e, ¬ HaltsIn T' N (E (encC15 C w)) e)) := by
  intro T' E
  obtain ⟨hD', hR', hsym, hsl, hsn, hst, hlen, hT, -, hF, hB, hN⟩ := URTM.Gen.KB9_27.main
  exact ⟨hD', hR', hst, hsym, hsl, hsn, hlen, hT,
    compose_ctsh E (finCfg15_pseudo C) (nostuck15 C w) (urtm15_6_simulates_ctsh C w) hF hB hN⟩

end URTM.CTSH.U9_27
