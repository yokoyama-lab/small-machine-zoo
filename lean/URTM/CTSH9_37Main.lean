/-
  URTM(9,37)（1 ブロック 3 状態の変換の疎版 ∘ URTM(15,6)、docs/15_sparse_counters_2026-09-27.md §6）が
  任意の CTSH を模倣すること。

  * 疎版の一般定理 `URTM.KStatePure.spconv_main`（KStatePure.lean）は、T の実行が疑似状態以外で
    止まらない（`NoStuck`）ことを仮定に、1 ステップ・停止・非停止の対応を与える。
  * (15,6) の CTSH 模倣の主定理 `urtm15_6_simulates_ctsh`（CTSH15_6Main.lean）の 2 番目
    （停止配置は必ず `finCfg15`）から、`encC15 C w` からの実行は疑似状態 null / halt でしか止まらない
    （`nostuck15`）。
  * 具体の疎版 `spconv T LP qs ss` は生成モジュール `URTM.Gen.PS15_6`（tools/kstate_sparse_pure.py
    --lean）にあり、Python の表 `TpyP` と規則の並びまで一致し（`decide +kernel`）、規則 220 本、
    記号は 37 要素の `symPy`、状態は 9 要素の `stPy` に入る。

  生成モジュールに依存するので、`tools/gen_all_lean.sh`（CI）が書く `URTM.lean` 経由でビルドされる。
  未証明の穴・新規公理・native_decide を使わない。
-/
import URTM.CTSH15_6Main
import URTM.Gen.PS15_6

namespace URTM.CTSH.U9_37

open URTM URTM.KState URTM.KStateSparse URTM.KStatePure URTM.CTSH URTM.Gen.K15_6
open URTM.Gen.PS15_6 (LP TpyP symPy stPy hG spconv_eq_py card syms_sts)
open URTM.CTSH.U15_6 (encC15 finCfg15 urtm15_6_simulates_ctsh)

/-- (15,6) の停止配置 `finCfg15` の状態は疑似状態（null か halt）。 -/
theorem finCfg15_pseudo (C : CTSH) (vf : List Ch) (mf : Nat) (rm : List Ch) :
    ∃ h, (finCfg15 C vf mf rm).st = .halt h := by
  cases vf with
  | nil => exact ⟨_, rfl⟩
  | cons _ _ => exact ⟨_, rfl⟩

/-- (15,6) を Morita の初期配置から動かすと、疑似状態以外では止まらない
    （規則の無い組 (q, s) に出会わない）。 -/
theorem nostuck15 (C : CTSH) (w : List Ch) : NoStuck T (encC15 C w) := by
  intro N e he
  obtain ⟨n, vf, mf, rm, _, rfl⟩ := (urtm15_6_simulates_ctsh C w).2.1 N e he
  exact finCfg15_pseudo C vf mf rm

/-- **主定理（URTM(9,37) は任意の CTSH を模倣する）**。T' = `spconv T LP qs ss`
    （1 ブロック 3 状態の変換の疎版を (15,6) に適用したもの。状態は 9 要素の `stPy`・記号は 37 要素の
    `symPy` に入る・規則 220 本・決定的可逆、Python の生成表 `TpyP` と一致）を符号化 `E = penc T LP` を
    通して見ると、任意の CTSH C と初期語 w について:

    1. C が (w, 0) から n ステップで停止 ID (vf, mf) に達するなら、T' は E (encC15 C w) から
       n ステップ以上で停止し、停止配置は E (finCfg15 C vf mf rm)。
    2. 逆に T' が E (encC15 C w) から停止するなら、C も (w, 0) から停止し、停止配置は 1 の形。
    3. C が停止しない ⇔ T' が停止しない。 -/
theorem urtm9_37_simulates_ctsh (C : CTSH) (w : List Ch) :
    let T' := spconv T LP qs ss
    let E := penc T LP
    Deterministic T' ∧ Reversible T' ∧
    (∀ ρ ∈ T', ρ.p ∈ stPy ∧ ∀ x, ρ.q = .go x → x ∈ stPy) ∧ stPy.length = 9 ∧ stPy.Nodup ∧
    (∀ ρ ∈ T', ρ.s ∈ symPy ∧ ρ.t ∈ symPy) ∧ symPy.length = 37 ∧ symPy.Nodup ∧
    T'.length = 220 ∧ T' = TpyP ∧
    (∀ n vf mf, CHaltsIn C n (w, 0) (vf, mf) →
      ∃ N rm, n ≤ N ∧ HaltsIn T' N (E (encC15 C w)) (E (finCfg15 C vf mf rm))) ∧
    (∀ N e, HaltsIn T' N (E (encC15 C w)) e →
      ∃ n vf mf rm, CHaltsIn C n (w, 0) (vf, mf) ∧ e = E (finCfg15 C vf mf rm)) ∧
    ((∀ n f, ¬ CHaltsIn C n (w, 0) f) ↔ (∀ N e, ¬ HaltsIn T' N (E (encC15 C w)) e)) := by
  intro T' E
  obtain ⟨hD', hR', -, hF, hB, hN⟩ := spconv_main (qs := qs) (ss := ss) hW hD hR hQ hS hG
  obtain ⟨hlen, hsl, hsn, hql, hqn⟩ := URTM.Gen.PS15_6.card
  have hT : T' = TpyP := spconv_eq_py
  have hs := sts_syms_of (M := T') (by rw [hT]; exact syms_sts)
  refine ⟨hD', hR', hs.1, hql, hqn, hs.2, hsl, hsn, hT ▸ hlen, hT,
    compose_ctsh E (finCfg15_pseudo C) (nostuck15 C w) (urtm15_6_simulates_ctsh C w) hF hB hN⟩

end URTM.CTSH.U9_37
