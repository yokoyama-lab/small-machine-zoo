/-
  URTM(9,40)（1 ブロック 3 状態の変換の**密な版** ∘ URTM(17,5)。旧リポ small-urtm-autoresearch の
  docs/08 が 2026-08-22 に得た点）が任意の CTSH を模倣すること。

  * 密な版の一般定理 `URTM.KStatePure.pconv_main`（KStatePureDense.lean）を、(17,5) の Q₊（10 状態）を
    5 状態ずつの 2 ブロック、Q₋（7 状態）を 1 ブロックにしたブロック分け `LD` に当てる。
    状態 9（3 ブロック × 3）、記号 40（素の 5 個と計数 [i, s]、i = 0..6）。
  * (17,5) の CTSH 模倣と「疑似状態以外で止まらない」（`nostuck17`）を合成する。
  * 旧リポの表とは、疑似状態へ入る規則 A' の扱いだけが違う（CTSH6_48Main.lean と同じ）。

  生成モジュールに依存するので、`tools/gen_all_lean.sh`（CI）が書く `URTM.lean` 経由でビルドされる。
  未証明の穴・新規公理・native_decide を使わない。
-/
import URTM.CTSH17_5Main
import URTM.KStatePureDense

set_option maxRecDepth 100000

namespace URTM.CTSH.U9_40

open URTM URTM.KState URTM.KStateSparse URTM.KStatePure URTM.CTSH URTM.Gen.K17_5

/-- ブロック分け: Q₊（10 状態）を 5 状態ずつの 2 ブロック、Q₋（7 状態）を 1 ブロック。 -/
def qplus : List St := qs.filter (fun q => dir T q == .R)
def blocksD : List (List St) := [qplus.take 5, qplus.drop 5, qs.filter (fun q => dir T q == .L)]
def LD : Layout St := layoutOf T blocksD

theorem hGL : GoodL T LD qs := by decide +kernel
theorem hG : Good T LD := good_of_L hQ hGL

/-- 記号の全体（素の 5 個と計数 [i, s]、i = 0..6）。 -/
def symD : List (KSym Sy) := ss.map .pl ++ (List.range 7).flatMap (fun i => ss.map (.ctr i))
/-- 状態の全体（3 ブロック × 3）。 -/
def stD : List PSt :=
  [.z .R 0, .z .L 0, .o .R 0, .z .R 1, .z .L 1, .o .R 1, .z .L 2, .z .R 2, .o .L 2]

theorem syms_sts : ∀ ρ ∈ pconv T LD ss, ρ.s ∈ symD ∧ ρ.t ∈ symD ∧ ρ.p ∈ stD ∧ tgtIn stD ρ.q = true := by
  decide +kernel
theorem card : symD.length = 40 ∧ symD.Nodup ∧ stD.length = 9 ∧ stD.Nodup ∧ qplus.length = 10 ∧
    (pconv T LD ss).length = 239 := by decide +kernel

/-- (17,5) の停止配置 `finCfg17` の状態は疑似状態（null か halt）。 -/
theorem finCfg17_pseudo (C : CTSH) (vf : List Ch) (mf : Nat) (rm : List Ch) :
    ∃ h, (U17_5.finCfg17 C vf mf rm).st = .halt h := by
  cases vf with
  | nil => exact ⟨_, rfl⟩
  | cons _ _ => exact ⟨_, rfl⟩

/-- (17,5) を Morita の初期配置から動かすと、疑似状態以外では止まらない。 -/
theorem nostuck17 (C : CTSH) (w : List Ch) : NoStuck T (U17_5.encC17 C w) := by
  intro N e he
  obtain ⟨n, vf, mf, rm, _, rfl⟩ := (U17_5.urtm17_5_simulates_ctsh C w).2.1 N e he
  exact finCfg17_pseudo C vf mf rm

/-- **主定理（URTM(9,40) は任意の CTSH を模倣する）**。T' = `pconv T LD ss`（密な版を (17,5) に適用。
    状態は 9 要素の `stD`・記号は 40 要素の `symD` に入る・規則 239 本・決定的可逆）を
    符号化 `E = penc T LD` を通して見ると、任意の CTSH C と初期語 w について停止・停止配置・非停止が対応する。 -/
theorem urtm9_40_simulates_ctsh (C : CTSH) (w : List Ch) :
    let T' := pconv T LD ss
    let E := penc T LD
    Deterministic T' ∧ Reversible T' ∧
    (∀ ρ ∈ T', ρ.p ∈ stD ∧ ∀ x, ρ.q = .go x → x ∈ stD) ∧ stD.length = 9 ∧ stD.Nodup ∧
    (∀ ρ ∈ T', ρ.s ∈ symD ∧ ρ.t ∈ symD) ∧ symD.length = 40 ∧ symD.Nodup ∧ T'.length = 239 ∧
    (∀ n vf mf, CHaltsIn C n (w, 0) (vf, mf) →
      ∃ N rm, n ≤ N ∧ HaltsIn T' N (E (U17_5.encC17 C w)) (E (U17_5.finCfg17 C vf mf rm))) ∧
    (∀ N e, HaltsIn T' N (E (U17_5.encC17 C w)) e →
      ∃ n vf mf rm, CHaltsIn C n (w, 0) (vf, mf) ∧ e = E (U17_5.finCfg17 C vf mf rm)) ∧
    ((∀ n f, ¬ CHaltsIn C n (w, 0) f) ↔ (∀ N e, ¬ HaltsIn T' N (E (U17_5.encC17 C w)) e)) := by
  intro T' E
  obtain ⟨hD', hR', hF, hB, hN⟩ := pconv_main (qs := qs) (ss := ss) hW hD hR hQ hS hG
  obtain ⟨hsl, hsn, hql, hqn, -, hlen⟩ := card
  have hs := sts_syms_of (M := T') syms_sts
  refine ⟨hD', hR', hs.1, hql, hqn, hs.2, hsl, hsn, hlen,
    compose_ctsh E (finCfg17_pseudo C) (nostuck17 C w) (U17_5.urtm17_5_simulates_ctsh C w) hF hB hN⟩

end URTM.CTSH.U9_40
