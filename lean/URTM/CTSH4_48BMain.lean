/-
  URTM(4,48)（ε 逆向きの 4 状態化 ∘ URTM(10,8)、docs/20 §3）を、ブロック分けの変換 `bconv` の
  1 ブロックずつの場合として書き直し、任意の CTSH を模倣することを示す。

  (4,48) の既存の証明（CTSH4_48Main.lean）は `KStateEps.econv` の表 `TpyE` についてのもので、
  状態の型は `KSt`。Def. 7.1 の万能性（lean-univ）は `bconv` の表に対する共通部分
  （`BlockGen.isUTMStrict_block`）を持つので、同じ表を `bconv` で作る:

  * 解 results/kstate_blocks/records/urtm4-48.json: ブロック (1,1)、計数値と番兵は
    results/kstate5/urtm10-8.k4.eps-.json（(4,48) の解）のまま、併合 H+1; H-1; O+1&D-1; D+1&O-1。
  * 生成モジュール `URTM.Gen.KB4_48`（tools/gen_blocks_lean.py）の `TpyB` は 4 状態・48 記号・153 規則。
  * `same_as_eps`: 状態の名前を `Fin 4 → KSt`（0 ↦ Hp, 1 ↦ Am, 2 ↦ Ap, 3 ↦ Hm）で付け替えると、
    `TpyB` と `TpyE` は同じ規則の集合で、長さも等しい（カーネルの `decide`）。つまり同じ機械である。

  生成モジュールに依存するので、`tools/gen_all_lean.sh`（CI）が書く `URTM.lean` 経由でビルドされる。
  未証明の穴・新規公理・native_decide を使わない。
-/
import URTM.CTSH6_45Main
import URTM.Gen.KB4_48
import URTM.Gen.KE10_8

namespace URTM.CTSH.U4_48B

open URTM URTM.KState URTM.KStateSparse URTM.KStateBlocks URTM.CTSH URTM.Gen.K10_8
open URTM.Gen.KB4_48 (spB qsB ssB TpyB symB)
open URTM.Gen.KE10_8 (TpyE)
open URTM.CTSH.U6_45 (finCfg10_pseudo nostuck10)

/-- `Fin 4` の状態の `KSt` での名前（生成モジュールの「状態の番号」: 0=hp1, 1=op1_dm1, 2=dp1_om1, 3=hm1）。 -/
def ren (x : Fin 4) : KSt := [KSt.Hp, .Am, .Ap, .Hm].getD x.val .Hm

/-- 規則の状態の名前の付け替え。 -/
def renR (ρ : Rule (Fin 4) Ps (KSym Sy)) : Rule KSt Ps (KSym Sy) :=
  ⟨ren ρ.p, ρ.s, ρ.t, ρ.d, match ρ.q with
    | .go x => .go (ren x)
    | .halt h => .halt h⟩

/-- **`TpyB` は (4,48) の表 `TpyE` と同じ機械**: 状態の名前を `ren`（単射）で付け替えると、規則の集合が
    一致し、長さも等しい。 -/
theorem same_as_eps :
    Function.Injective ren ∧ (∀ ρ ∈ TpyB, renR ρ ∈ TpyE) ∧ (∀ ρ ∈ TpyE, ∃ σ ∈ TpyB, renR σ = ρ) ∧
    TpyB.length = TpyE.length := by
  refine ⟨?_, by decide +kernel⟩
  intro a b h
  revert a b
  decide

/-- **主定理（URTM(4,48) は任意の CTSH を模倣する、`bconv` の表で）**。T' = `bconv T spB qsB ssB`
    （ブロック (1,1)・役割の併合・ε を (10,8) に適用したもの。状態は `Fin 4`・記号は 48 要素の `symB` に入る・
    規則 153 本・決定的可逆、Python の生成表 `TpyB` と一致）を符号化 `E = benc T spB` を通して見ると、
    任意の CTSH C と初期語 w について:

    1. C が (w, 0) から n ステップで停止 ID (vf, mf) に達するなら、T' は E (encC C w) から
       n ステップ以上で停止し、停止配置は E (finCfg C vf mf rm)。
    2. 逆に T' が E (encC C w) から停止するなら、C も (w, 0) から停止し、停止配置は 1 の形。
    3. C が停止しない ⇔ T' が停止しない。 -/
theorem urtm4_48_simulates_ctsh (C : CTSH) (w : List Ch) :
    let T' := bconv T spB qsB ssB
    let E := benc T spB
    Deterministic T' ∧ Reversible T' ∧ (∀ x : Fin 4, ∃ ρ ∈ T', ρ.p = x) ∧
    (∀ ρ ∈ T', ρ.s ∈ symB ∧ ρ.t ∈ symB) ∧ symB.length = 48 ∧ symB.Nodup ∧
    T'.length = 153 ∧ T' = TpyB ∧
    (∀ n vf mf, CHaltsIn C n (w, 0) (vf, mf) →
      ∃ N rm, n ≤ N ∧ HaltsIn T' N (E (U10_8.encC C w)) (E (U10_8.finCfg C vf mf rm))) ∧
    (∀ N e, HaltsIn T' N (E (U10_8.encC C w)) e →
      ∃ n vf mf rm, CHaltsIn C n (w, 0) (vf, mf) ∧ e = E (U10_8.finCfg C vf mf rm)) ∧
    ((∀ n f, ¬ CHaltsIn C n (w, 0) f) ↔ (∀ N e, ¬ HaltsIn T' N (E (U10_8.encC C w)) e)) := by
  intro T' E
  obtain ⟨hD', hR', hsym, hsl, hsn, hst, hlen, hT, -, hF, hB, hN⟩ := URTM.Gen.KB4_48.main
  exact ⟨hD', hR', hst, hsym, hsl, hsn, hlen, hT,
    compose_ctsh E (finCfg10_pseudo C) (nostuck10 C w) (U10_8.urtm10_8_simulates_ctsh C w) hF hB hN⟩

end URTM.CTSH.U4_48B
