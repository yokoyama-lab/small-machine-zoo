/-
  URTM(4,88)（定理 A の 4 状態化 ∘ URTM(10,8)）を、状態の型を `Fin 4`、配置の符号化をブロックの変換の
  `benc` にして書き直し、任意の CTSH を模倣することを示す。

  Def. 7.1 の万能性（lean-univ）の共通部分 `Base10_8.isUTMStrict_block10` は、状態が `Fin k` で
  符号化が `benc` の機械についてのものなので、その形に合わせる。表は定理 A の変換 `conv T qs ss`
  （= 生成表 `Tpy`、223 規則、`conv_eq_py`）の状態の名前を `idx`（Hp ↦ 0, Hm ↦ 1, Ap ↦ 2, Am ↦ 3、
  逆写像 `nam`）で付け替えただけである（`TpyR_eq_conv`）。

  * `spH`: 1 ブロック、計数値は定理 A の標準の番号付け `canonOff T qs`、H の役割は `H (dir q)`。
    `benc` が見るのは H の役割と計数値だけで、番兵と O・D の役割は使わない。
  * `benc_eq`: `benc T spH = renC idx ∘ enc T (canonOff T qs)`。
  * `urtm4_88B_simulates_ctsh`: 既存の `U10_8.urtm4_88_simulates_ctsh` を付け替え（`KStateRen`）で移したもの。

  未証明の穴・新規公理・native_decide を使わない。
-/
import URTM.CTSH10_8
import URTM.KStateBlocks
import URTM.KStateRen

namespace URTM.CTSH.U4_88B

open URTM URTM.KState URTM.KStateBlocks URTM.KStateRen URTM.CTSH URTM.Gen.K10_8
open URTM.CTSH.U10_8 (encC finCfg)

/-- `KSt` の状態の番号。 -/
def idx : KSt → Fin 4
  | .Hp => 0
  | .Hm => 1
  | .Ap => 2
  | .Am => 3

/-- 番号から `KSt` の名前へ（`idx` の逆写像）。 -/
def nam (x : Fin 4) : KSt := [KSt.Hp, .Hm, .Ap, .Am].getD x.val .Am

theorem nam_idx (a : KSt) : nam (idx a) = a := by cases a <;> rfl
theorem idx_nam (x : Fin 4) : idx (nam x) = x := by revert x; decide

/-- URTM(4,88) の表（状態は `Fin 4`）。 -/
def TpyR : Machine (Fin 4) Ps (KSym Sy) := Tpy.map (renR idx)

/-- **`TpyR` は定理 A の変換の表の状態の名前を付け替えたもの**。 -/
theorem TpyR_eq_conv : TpyR = (conv T qs ss).map (renR idx) := by rw [conv_eq_py]; rfl

/-- 1 ブロック、計数値は `canonOff T qs`、役割は定理 A の状態 H(d)・A(opp d)・A(d)。 -/
def spH : BSpec St 4 where
  blk _ := 0
  v := canonOff T qs
  sg _ _ := 0
  cls r d _ := idx (match r with
    | .h => H d
    | .o => A (opp d)
    | .d => A d)

theorem benc_eq (c : Cfg St Ps Sy) : benc T spH c = renC idx (enc T (canonOff T qs) c) := by
  rcases c with ⟨st, pos, tape⟩
  cases st with
  | go p => simp only [benc, enc, renC, renT, rst, spH]
  | halt h => simp only [benc, enc, renC, renT]

theorem TpyR_det : Deterministic TpyR := by decide +kernel
theorem TpyR_rev : Reversible TpyR := by decide +kernel

theorem idx_inj : ∀ a b, idx a = idx b → a = b := fun a b h => by
  rw [← nam_idx a, ← nam_idx b, h]

theorem fwd (C : CTSH) (w : List Ch) (n : Nat) (vf : List Ch) (mf : Nat)
    (h : CHaltsIn C n (w, 0) (vf, mf)) :
    ∃ N rm, n ≤ N ∧ HaltsIn TpyR N (benc T spH (encC C w)) (benc T spH (finCfg C vf mf rm)) := by
  obtain ⟨-, -, -, -, hF, -, -⟩ := U10_8.urtm4_88_simulates_ctsh C w
  obtain ⟨N, rm, hn, hh⟩ := hF n vf mf h
  refine ⟨N, rm, hn, ?_⟩
  rw [benc_eq, benc_eq, TpyR_eq_conv]
  exact haltsIn_ren idx_inj hh

theorem bwd (C : CTSH) (w : List Ch) (N : Nat) (e : Cfg (Fin 4) Ps (KSym Sy))
    (h : HaltsIn TpyR N (benc T spH (encC C w)) e) :
    ∃ n vf mf rm, CHaltsIn C n (w, 0) (vf, mf) ∧ e = benc T spH (finCfg C vf mf rm) := by
  obtain ⟨-, -, -, -, -, hB, -⟩ := U10_8.urtm4_88_simulates_ctsh C w
  rw [benc_eq, TpyR_eq_conv] at h
  obtain ⟨n, vf, mf, rm, hc, he⟩ := hB N _ (haltsIn_ren_rev nam_idx idx_nam h)
  refine ⟨n, vf, mf, rm, hc, ?_⟩
  rw [benc_eq, ← he, renC_renC idx_nam]

theorem div (C : CTSH) (w : List Ch) :
    (∀ n f, ¬ CHaltsIn C n (w, 0) f) ↔ (∀ N e, ¬ HaltsIn TpyR N (benc T spH (encC C w)) e) := by
  obtain ⟨-, -, -, -, -, -, hDiv⟩ := U10_8.urtm4_88_simulates_ctsh C w
  rw [hDiv, benc_eq, TpyR_eq_conv]
  constructor
  · intro hno N e h
    exact hno N _ (haltsIn_ren_rev nam_idx idx_nam h)
  · intro hno N e h
    exact hno N _ (haltsIn_ren idx_inj h)

/-- **主定理（URTM(4,88) は任意の CTSH を模倣する、`Fin 4` の表と `benc` で）**。任意の CTSH C と
    初期語 w について:

    1. C が (w, 0) から n ステップで停止 ID (vf, mf) に達するなら、`TpyR` は E (encC C w) から
       n ステップ以上で停止し、停止配置は E (finCfg C vf mf rm)。
    2. 逆に `TpyR` が E (encC C w) から停止するなら、C も (w, 0) から停止し、停止配置は 1 の形。
    3. C が停止しない ⇔ `TpyR` が停止しない。 -/
theorem urtm4_88B_simulates_ctsh (C : CTSH) (w : List Ch) :
    let E := benc T spH
    Deterministic TpyR ∧ Reversible TpyR ∧
    (∀ n vf mf, CHaltsIn C n (w, 0) (vf, mf) →
      ∃ N rm, n ≤ N ∧ HaltsIn TpyR N (E (encC C w)) (E (finCfg C vf mf rm))) ∧
    (∀ N e, HaltsIn TpyR N (E (encC C w)) e →
      ∃ n vf mf rm, CHaltsIn C n (w, 0) (vf, mf) ∧ e = E (finCfg C vf mf rm)) ∧
    ((∀ n f, ¬ CHaltsIn C n (w, 0) f) ↔ (∀ N e, ¬ HaltsIn TpyR N (E (encC C w)) e)) :=
  ⟨TpyR_det, TpyR_rev, fwd C w, bwd C w, div C w⟩

end URTM.CTSH.U4_88B
