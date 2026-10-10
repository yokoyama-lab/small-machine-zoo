/-
  URTM(6,45)（1 ブロック 3 状態の変換の疎版 ∘ URTM(10,8)、docs/15_sparse_counters_2026-09-27.md §6）が
  任意の CTSH を模倣すること。

  * 疎版の一般定理 `URTM.KStatePure.spconv_main`（KStatePure.lean）は、T の実行が疑似状態以外で
    止まらない（`NoStuck`）ことを仮定に、1 ステップ・停止・非停止の対応を与える。
  * (10,8) の CTSH 模倣の主定理 `urtm10_8_simulates_ctsh`（CTSH10_8.lean）の 2 番目
    （停止配置は必ず `finCfg`）から、`encC C w` からの実行は疑似状態 null / halt でしか止まらない
    （`nostuck10`）。
  * 具体の疎版 `spconv T LP qs ss` は生成モジュール `URTM.Gen.PS10_8`（tools/kstate_sparse_pure.py
    --lean）にあり、Python の表 `TpyP` と規則の並びまで一致し（`decide +kernel`）、規則 211 本、
    記号は 45 要素の `symPy`、状態は 6 要素の `stPy` に入る。

  生成モジュールに依存するので、`tools/gen_all_lean.sh`（CI）が書く `URTM.lean` 経由でビルドされる。
  未証明の穴・新規公理・native_decide を使わない。
-/
import URTM.CTSH10_8
import URTM.Gen.PS10_8

namespace URTM.CTSH.U6_45

open URTM URTM.KState URTM.KStateSparse URTM.KStatePure URTM.CTSH URTM.Gen.K10_8
open URTM.Gen.PS10_8 (LP TpyP symPy stPy hG spconv_eq_py card syms_sts)

/-- (10,8) の停止配置 `finCfg` の状態は疑似状態（null か halt）。 -/
theorem finCfg10_pseudo (C : CTSH) (vf : List Ch) (mf : Nat) (rm : List Ch) :
    ∃ h, (U10_8.finCfg C vf mf rm).st = .halt h := by
  cases vf with
  | nil => exact ⟨_, rfl⟩
  | cons _ _ => exact ⟨_, rfl⟩

/-- (10,8) を Morita の初期配置から動かすと、疑似状態以外では止まらない
    （規則の無い組 (q, s) に出会わない）。 -/
theorem nostuck10 (C : CTSH) (w : List Ch) : NoStuck T (U10_8.encC C w) := by
  intro N e he
  obtain ⟨n, vf, mf, rm, _, rfl⟩ := (U10_8.urtm10_8_simulates_ctsh C w).2.1 N e he
  exact finCfg10_pseudo C vf mf rm

/-- **主定理（URTM(6,45) は任意の CTSH を模倣する）**。T' = `spconv T LP qs ss`
    （1 ブロック 3 状態の変換の疎版を (10,8) に適用したもの。状態は 6 要素の `stPy`・記号は 45 要素の
    `symPy` に入る・規則 211 本・決定的可逆、Python の生成表 `TpyP` と一致）を符号化 `E = penc T LP` を
    通して見ると、任意の CTSH C と初期語 w について:

    1. C が (w, 0) から n ステップで停止 ID (vf, mf) に達するなら、T' は E (encC C w) から
       n ステップ以上で停止し、停止配置は E (finCfg C vf mf rm)。
    2. 逆に T' が E (encC C w) から停止するなら、C も (w, 0) から停止し、停止配置は 1 の形。
    3. C が停止しない ⇔ T' が停止しない。 -/
theorem urtm6_45_simulates_ctsh (C : CTSH) (w : List Ch) :
    let T' := spconv T LP qs ss
    let E := penc T LP
    Deterministic T' ∧ Reversible T' ∧
    (∀ ρ ∈ T', ρ.p ∈ stPy ∧ ∀ x, ρ.q = .go x → x ∈ stPy) ∧ stPy.length = 6 ∧ stPy.Nodup ∧
    (∀ ρ ∈ T', ρ.s ∈ symPy ∧ ρ.t ∈ symPy) ∧ symPy.length = 45 ∧ symPy.Nodup ∧
    T'.length = 211 ∧ T' = TpyP ∧
    (∀ n vf mf, CHaltsIn C n (w, 0) (vf, mf) →
      ∃ N rm, n ≤ N ∧ HaltsIn T' N (E (U10_8.encC C w)) (E (U10_8.finCfg C vf mf rm))) ∧
    (∀ N e, HaltsIn T' N (E (U10_8.encC C w)) e →
      ∃ n vf mf rm, CHaltsIn C n (w, 0) (vf, mf) ∧ e = E (U10_8.finCfg C vf mf rm)) ∧
    ((∀ n f, ¬ CHaltsIn C n (w, 0) f) ↔ (∀ N e, ¬ HaltsIn T' N (E (U10_8.encC C w)) e)) := by
  intro T' E
  obtain ⟨hD', hR', -, hF, hB, hN⟩ := spconv_main (qs := qs) (ss := ss) hW hD hR hQ hS hG
  obtain ⟨hlen, hsl, hsn, hql, hqn⟩ := URTM.Gen.PS10_8.card
  have hT : T' = TpyP := spconv_eq_py
  have hs := sts_syms_of (M := T') (by rw [hT]; exact syms_sts)
  refine ⟨hD', hR', hs.1, hql, hqn, hs.2, hsl, hsn, hT ▸ hlen, hT,
    compose_ctsh E (finCfg10_pseudo C) (nostuck10 C w) (U10_8.urtm10_8_simulates_ctsh C w) hF hB hN⟩

end URTM.CTSH.U6_45
