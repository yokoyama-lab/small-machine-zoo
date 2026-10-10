/-
  **停止が決定不能な五つ組表**（Morita 形式の TM 1 台）を Mathlib から組み立てる。

  道筋: 万能の部分再帰関数 x ↦ ⟦x⟧(0) を計算する `Turing.ToPartrec.Code` を 1 つ固定し（`UC`）、
  Mathlib の翻訳 `PartrecToTM2`（有限台 `codeSupp`）→ `TM2to1` → `TM1to0` で TM0 機械にし、
  `TM0Quint.lean` の翻訳で五つ組表 `tblU` にする。入力 x の初期 ID `zidU x` は x の 2 進表記を
  並べたもので、x ↦ `zidU x` は原始再帰的（`zidU_primrec`）。

  **表は 1 つに固定する**ので、コードから表への翻訳が計算可能であることは要らない
  （要るのは入力の符号化 x ↦ `zidU x` の計算可能性だけ）。
-/
import Mathlib.Computability.TuringMachine.ToPartrec
import Mathlib.Computability.Halting
import URTMMeta.TM0Quint

namespace URTM.Meta
open URTM Turing StateTransition
open Turing.PartrecToTM2 (Γ' K' Cont' trNormal codeSupp trList trNat trNum)

/-! ### 万能コード -/

/-- x ↦ ⟦x⟧(0) を計算する ToPartrec のコードがある。 -/
theorem exists_univ_code : ∃ U : ToPartrec.Code, ∀ x : ℕ,
    (U.eval [x]).Dom ↔ ((Denumerable.ofNat Nat.Partrec.Code x).eval 0).Dom := by
  have hp : Partrec fun x : ℕ => (Denumerable.ofNat Nat.Partrec.Code x).eval 0 :=
    Nat.Partrec.Code.eval_part.comp (Computable.ofNat _) (Computable.const 0)
  obtain ⟨U, hU⟩ := ToPartrec.Code.exists_code (Nat.Partrec'.part_iff₁.mpr hp)
  refine ⟨U, fun x => ?_⟩
  have h := hU ⟨[x], rfl⟩
  change U.eval [x] = _ at h
  rw [h]
  simp [List.Vector.head]

noncomputable def UC : ToPartrec.Code := Classical.choose exists_univ_code

theorem UC_spec (x : ℕ) :
    (UC.eval [x]).Dom ↔ ((Denumerable.ofNat Nat.Partrec.Code x).eval 0).Dom :=
  Classical.choose_spec exists_univ_code x

/-! ### Mathlib の翻訳の連鎖 -/

instance : Fintype K' :=
  ⟨{K'.main, K'.rev, K'.aux, K'.stack}, by intro x; cases x <;> simp⟩

/-- 状態の型（始状態を `UC` の開始ラベルにするための別名）。 -/
def ΛU := PartrecToTM2.Λ'

noncomputable instance : Inhabited ΛU := ⟨trNormal UC Cont'.halt⟩

/-- TM2 機械（Mathlib の `PartrecToTM2.tr`）。 -/
def M2 : ΛU → TM2.Stmt (fun _ : K' => Γ') ΛU (Option Γ') := PartrecToTM2.tr

theorem M2_supports : TM2.Supports M2 (codeSupp UC Cont'.halt) :=
  PartrecToTM2.tr_supports UC Cont'.halt

/-- TM1 機械。 -/
noncomputable def M1 := TM2to1.tr M2

/-- テープ記号。 -/
abbrev Γ₁ := TM2to1.Γ' K' (fun _ : K' => Γ')

instance : DecidableEq Γ₁ := inferInstanceAs (DecidableEq (Bool × (K' → Option Γ')))

/-- TM0 機械。 -/
noncomputable def M0 := TM1to0.tr M1

abbrev Λ₀ := TM1to0.Λ' M1

noncomputable instance : DecidableEq Λ₀ := Classical.decEq _

noncomputable def S0 : Finset Λ₀ := TM1to0.trStmts M1 (TM2to1.trSupp M2 (codeSupp UC Cont'.halt))

theorem M0_supports : TM0.Supports M0 ↑S0 :=
  TM1to0.tr_supports M1 (TM2to1.tr_supports M2 M2_supports)

/-- TM2 の初期配置は `PartrecToTM2.init` と同じ。 -/
theorem init_eq (v : List ℕ) :
    (TM2.init K'.main (trList v) : TM2.Cfg (fun _ : K' => Γ') ΛU (Option Γ')) =
      PartrecToTM2.init UC v := by
  unfold TM2.init PartrecToTM2.init
  congr 1
  funext k; cases k <;> rfl

/-- 入力 x の TM1/TM0 テープ。 -/
def tapeU (x : ℕ) : List Γ₁ := TM2to1.trInit K'.main (trList [x])

/-- 連鎖: TM0 機械 `M0` が `tapeU x` から止まる ⟺ ⟦x⟧(0) が定義される。 -/
theorem M0_halts_iff (x : ℕ) :
    (eval (TM0.step M0) (TM0.init (tapeU x))).Dom ↔
      ((Denumerable.ofNat Nat.Partrec.Code x).eval 0).Dom := by
  have h0 : (eval (TM0.step M0) (TM0.init (tapeU x))).Dom ↔ (TM0.eval M0 (tapeU x)).Dom := by
    unfold TM0.eval; simp
  rw [h0, M0, TM1to0.tr_eval, M1, tapeU, TM2to1.tr_eval_dom]
  unfold TM2.eval
  simp only [Part.map_Dom]
  rw [init_eq]
  have := PartrecToTM2.tr_eval UC [x]
  change eval (TM2.step PartrecToTM2.tr) (PartrecToTM2.init UC [x]) = _ at this
  change (eval (TM2.step PartrecToTM2.tr) (PartrecToTM2.init UC [x])).Dom ↔ _
  rw [this, ← UC_spec]
  simp

/-! ### 五つ組表と入力の符号化 -/

/-- **停止が決定不能な五つ組表**（Morita 形式の 1 テープ TM。可逆とは限らない）。 -/
noncomputable def tblU : List Quint := tblOf M0 S0

/-- 入力の区切り記号（スタックの底の印つき）の番号。 -/
noncomputable def cMark : ℕ :=
  symN ((true, Function.update (fun _ => none) K'.main (some Γ'.cons)) : Γ₁)

/-- 2 進の桁記号の番号。 -/
noncomputable def cBit (a : Γ') : ℕ :=
  symN ((false, Function.update (fun _ => none) K'.main (some a)) : Γ₁)

/-- 入力 x の 2 進表記（上の桁から）を記号番号で。 -/
noncomputable def binU (x : ℕ) : List ℕ := (trNat x).reverse.map cBit

/-- 入力 x の初期 ID。 -/
noncomputable def zidU (x : ℕ) : ZID := (stN S0 default, [], cMark :: binU x)

theorem tapeU_map (x : ℕ) : (tapeU x).map symN = cMark :: binU x := by
  simp [tapeU, TM2to1.trInit, binU, cMark, cBit, trList, List.reverse_append]
  exact ⟨rfl, fun _ _ => rfl⟩

/-- **`tblU` の停止 ⟺ 部分再帰関数の停止**。 -/
theorem tblU_halts_iff (x : ℕ) :
    ZHalts tblU (zidU x) ↔ ((Denumerable.ofNat Nat.Partrec.Code x).eval 0).Dom := by
  rw [← M0_halts_iff, tm0_halts_iff M0 S0 M0_supports, tapeU_map]
  rfl

/-! ### 入力の符号化は原始再帰的 -/

theorem trNum_bit1 (n : Num) : trNum (Num.bit1 n) = Γ'.bit1 :: trNum n := by
  cases n <;> rfl

theorem trNum_bit0 (n : Num) (h : n ≠ 0) : trNum (Num.bit0 n) = Γ'.bit0 :: trNum n := by
  cases n with
  | zero => exact absurd rfl h
  | pos p => rfl

theorem trNat_rec (m : ℕ) (hm : m ≠ 0) :
    trNat m = (if m % 2 = 0 then Γ'.bit0 else Γ'.bit1) :: trNat (m / 2) := by
  have hb : m = Nat.bit (decide (m % 2 = 1)) (m / 2) := by
    rw [Nat.bit_val]; by_cases h : m % 2 = 1 <;> simp [h] <;> omega
  unfold trNat
  rw [← Num.ofNat'_eq, ← Num.ofNat'_eq, hb, Num.ofNat'_bit, Nat.bit_div_two, Nat.bit_mod_two]
  by_cases h : m % 2 = 1
  · simp only [h, decide_true, cond_true, Bool.toNat_true, one_ne_zero, if_false]
    exact trNum_bit1 _
  · have h0 : m % 2 = 0 := by omega
    simp only [h, decide_false, cond_false, Bool.toNat_false, if_true]
    apply trNum_bit0
    rw [Num.ofNat'_eq]
    intro e
    have := Num.to_of_nat (m / 2)
    rw [e] at this
    simp at this
    omega

/-- 1 桁ずつ取り出す。 -/
noncomputable def bstep (p : ℕ × List ℕ) : ℕ × List ℕ :=
  if p.1 = 0 then p else (p.1 / 2, (if p.1 % 2 = 0 then cBit Γ'.bit0 else cBit Γ'.bit1) :: p.2)

theorem bstep_iter : ∀ k m (acc : List ℕ), m < 2 ^ k →
    bstep^[k] (m, acc) = (0, (trNat m).reverse.map cBit ++ acc)
  | 0, m, acc, h => by
    have : m = 0 := by simp at h; omega
    subst this; simp
  | k + 1, m, acc, h => by
    rw [Function.iterate_succ_apply]
    by_cases hm : m = 0
    · subst hm
      have hf : bstep (0, acc) = (0, acc) := by simp [bstep]
      rw [hf, Function.iterate_fixed hf]; simp
    · have hs : bstep (m, acc) =
          (m / 2, (if m % 2 = 0 then cBit Γ'.bit0 else cBit Γ'.bit1) :: acc) := by
        simp [bstep, hm]
      have hlt : m / 2 < 2 ^ k := by rw [pow_succ] at h; omega
      rw [hs, bstep_iter k (m / 2) _ hlt, trNat_rec m hm]
      by_cases h2 : m % 2 = 0 <;> simp [h2]

theorem binU_eq (x : ℕ) : binU x = (bstep^[x] (x, [])).2 := by
  rw [bstep_iter x x [] (Nat.lt_two_pow_self)]; simp [binU]

theorem bstep_primrec : Primrec bstep := by
  have h := Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 0)) Primrec.id
    (Primrec.pair (Primrec.nat_div.comp Primrec.fst (Primrec.const 2))
      (Primrec.list_cons.comp
        (Primrec.ite (Primrec.eq.comp (Primrec.nat_mod.comp Primrec.fst (Primrec.const 2))
          (Primrec.const 0)) (Primrec.const (cBit Γ'.bit0)) (Primrec.const (cBit Γ'.bit1)))
        Primrec.snd))
  exact h.of_eq fun p => rfl

theorem zidU_primrec : Primrec zidU := by
  have hb : Primrec binU := by
    have := Primrec.nat_iterate Primrec.id (Primrec.pair Primrec.id (Primrec.const []))
      (bstep_primrec.comp Primrec.snd).to₂
    exact (Primrec.snd.comp this).of_eq fun x => (binU_eq x).symm
  exact (Primrec.pair (Primrec.const _) (Primrec.pair (Primrec.const [])
    (Primrec.list_cons.comp (Primrec.const cMark) hb))).of_eq fun x => rfl

/-! ### 決定不能性 -/

/-- **`tblU` の入力族 `zidU x` 上の停止は決定不能。** -/
theorem tblU_undecidable : ¬ ComputablePred fun x : ℕ => ZHalts tblU (zidU x) := by
  intro h
  apply ComputablePred.halting_problem 0
  obtain ⟨f, hf, hfe⟩ := ComputablePred.computable_iff.mp h
  refine ComputablePred.computable_iff.mpr ⟨fun T => f (Encodable.encode T),
    hf.comp Computable.encode, ?_⟩
  funext T
  have := congrFun hfe (Encodable.encode T)
  show (T.eval 0).Dom = (f (Encodable.encode T) = true)
  rw [← this, tblU_halts_iff, Denumerable.ofNat_encode]

/-- **`tblU` の停止問題（有限 ID 上）は決定不能。** -/
theorem tblU_halting_undecidable : ¬ ComputablePred (ZHalts tblU) := by
  intro h
  apply tblU_undecidable
  obtain ⟨f, hf, hfe⟩ := ComputablePred.computable_iff.mp h
  refine ComputablePred.computable_iff.mpr ⟨fun x => f (zidU x), hf.comp zidU_primrec.to_comp, ?_⟩
  funext x
  exact congrFun hfe (zidU x)

end URTM.Meta
