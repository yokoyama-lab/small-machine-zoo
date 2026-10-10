/-
  2 状態 RTM の停止問題は（有限 ID 上で）計算可能に判定できる — Mathlib の `ComputablePred` として。

  `zhalts_iff_bound`（`Zipper.lean`）で停止は「`zbound` 歩回して止まっているか」に等しい。
  ここではその判定関数が原始再帰的（`Primrec`）であることを示す:
  表引き・1 歩・反復・上界（べき乗を含む）をそれぞれ Mathlib の原始再帰の組み合わせで書く。
-/
import Mathlib.Computability.Halting
import URTMMeta.Zipper

namespace URTM.Meta
open URTM URTM.TwoState

/-! ### 表引きと 1 歩 -/

theorem look_primrec (tbl : List Quint) : Primrec₂ (look tbl) := by
  induction tbl with
  | nil => exact (Primrec.const none).to₂
  | cons r tbl ih =>
    have hp : PrimrecPred fun x : Nat × Nat => r.p = x.1 ∧ r.s = x.2 :=
      PrimrecPred.and (Primrec.eq.comp (Primrec.const r.p) Primrec.fst)
        (Primrec.eq.comp (Primrec.const r.s) Primrec.snd)
    have := Primrec.ite hp (Primrec.const (some (rhs r))) ih
    exact this.of_eq fun x => by simp only [look]

theorem headD_primrec : Primrec fun l : List Nat => l.headD 0 :=
  Primrec.list_headI.of_eq fun l => by cases l <;> rfl

theorem mv_primrec : Primrec₂ mv := by
  have o := (Primrec.fst : Primrec fun x : (Nat × Nat × Nat) × ZID => x.1)
  have z := (Primrec.snd : Primrec fun x : (Nat × Nat × Nat) × ZID => x.2)
  have ot := Primrec.fst.comp o
  have od := Primrec.fst.comp (Primrec.snd.comp o)
  have oq := Primrec.snd.comp (Primrec.snd.comp o)
  have zL := Primrec.fst.comp (Primrec.snd.comp z)
  have zR := Primrec.snd.comp (Primrec.snd.comp z)
  have mL := Primrec.pair oq (Primrec.pair (Primrec.list_tail.comp zL)
    (Primrec.list_cons.comp (headD_primrec.comp zL) (Primrec.list_cons.comp ot (Primrec.list_tail.comp zR))))
  have mZ := Primrec.pair oq (Primrec.pair zL (Primrec.list_cons.comp ot (Primrec.list_tail.comp zR)))
  have mR := Primrec.pair oq (Primrec.pair (Primrec.list_cons.comp ot zL) (Primrec.list_tail.comp zR))
  have h := Primrec.ite (Primrec.eq.comp od (Primrec.const 0))
    mL (Primrec.ite (Primrec.eq.comp od (Primrec.const 1)) mZ mR)
  exact h.of_eq fun x => by simp only [mv]

theorem zstep_primrec (tbl : List Quint) : Primrec (zstep tbl) := by
  have hl : Primrec fun z : ZID => look tbl z.1 (z.2.2.headD 0) :=
    (look_primrec tbl).comp Primrec.fst (headD_primrec.comp (Primrec.snd.comp Primrec.snd))
  have hm : Primrec₂ fun (z : ZID) (o : Nat × Nat × Nat) => mv o z :=
    mv_primrec.comp Primrec.snd Primrec.fst
  exact (Primrec.option_map hl hm).of_eq fun z => rfl

/-! ### 反復 -/

theorem iter_none (g : ZID → Option ZID) :
    ∀ n, (fun o : Option ZID => o.bind g)^[n] none = none
  | 0 => rfl
  | n + 1 => by rw [Function.iterate_succ_apply]; exact iter_none g n

theorem zrun_eq_iter (tbl : List Quint) :
    ∀ n (z : ZID), zrun tbl n z = (fun o : Option ZID => o.bind (zstep tbl))^[n] (some z)
  | 0, _ => rfl
  | n + 1, z => by
    rw [Function.iterate_succ_apply]
    show _ = (fun o : Option ZID => o.bind (zstep tbl))^[n] (zstep tbl z)
    unfold zrun
    cases zstep tbl z with
    | none => exact (iter_none _ n).symm
    | some z' => exact zrun_eq_iter tbl n z'

/-! ### 上界 -/

theorem pow_primrec : Primrec₂ fun n w : Nat => n ^ w := by
  have h : Primrec fun p : Nat × Nat => (fun x => x * p.1)^[p.2] 1 :=
    Primrec.nat_iterate Primrec.snd (Primrec.const 1)
      (Primrec.nat_mul.comp Primrec.snd (Primrec.fst.comp Primrec.fst)).to₂
  refine h.of_eq fun p => ?_
  obtain ⟨n, w⟩ := p
  simp only
  induction w with
  | zero => rfl
  | succ w ih => rw [Function.iterate_succ_apply', ih, Nat.pow_succ]

theorem csize_primrec : Primrec₂ csize := by
  have h := Primrec.nat_mul.comp (pow_primrec.comp Primrec.fst Primrec.snd)
    (Primrec.nat_mul.comp Primrec.snd (Primrec.const 3))
  exact h.of_eq fun p => rfl

/-- `bnd` を自然数だけで書いたもの（窓の幅 w = |L| + |R|）。 -/
def bndN (nsym w : Nat) : Nat :=
  csize nsym (w + 1 + 2 * (csize nsym (w + 1) * (2 * nsym + 3) + 1) + 2) + csize nsym (w + 3)
    + csize nsym (w + 3)

theorem bnd_eq (nsym m n : Nat) : bnd nsym (-(m : Int)) (n : Int) = bndN nsym (m + n) := by
  unfold bnd bndN haltBound entBound winW monoBound
  have h1 : ((n : Int) - -(m : Int) + 1).toNat = m + n + 1 := by omega
  have h2 : ((n : Int) - -(m : Int) + 3).toNat = m + n + 3 := by omega
  have h3 : (- -(m : Int) - -(n : Int) + 3).toNat = m + n + 3 := by omega
  rw [h1, h2, h3]

theorem bndN_primrec : Primrec₂ bndN := by
  have ns := (Primrec.fst : Primrec fun p : Nat × Nat => p.1)
  have w := (Primrec.snd : Primrec fun p : Nat × Nat => p.2)
  have add := Primrec.nat_add
  have mul := Primrec.nat_mul
  have c := fun {f g : Nat × Nat → Nat} (hf : Primrec f) (hg : Primrec g) => csize_primrec.comp hf hg
  have w1 := add.comp w (Primrec.const 1)
  have w3 := add.comp w (Primrec.const 3)
  have e := add.comp (mul.comp (c ns w1) (add.comp (mul.comp (Primrec.const 2) ns) (Primrec.const 3)))
    (Primrec.const 1)
  have hb := add.comp (add.comp (c ns (add.comp (add.comp w1 (mul.comp (Primrec.const 2) e))
    (Primrec.const 2))) (c ns w3)) (c ns w3)
  exact hb.of_eq fun p => rfl

theorem lmax_primrec : Primrec lmax := by
  have h : Primrec fun l : List Nat => l.foldr (fun b s => max b s) 0 :=
    Primrec.list_foldr Primrec.id (Primrec.const 0)
      (Primrec.nat_max.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂
  exact h.of_eq fun l => rfl

theorem zbound_primrec (tbl : List Quint) : Primrec (zbound tbl) := by
  have zL := (Primrec.fst.comp Primrec.snd : Primrec fun z : ZID => z.2.1)
  have zR := (Primrec.snd.comp Primrec.snd : Primrec fun z : ZID => z.2.2)
  have hn : Primrec (nsymOf tbl) :=
    Primrec.nat_max.comp (Primrec.const _)
      (Primrec.nat_add.comp (lmax_primrec.comp (Primrec.list_append.comp zL zR)) (Primrec.const 1))
  have h := Primrec.nat_add.comp (bndN_primrec.comp hn
    (Primrec.nat_add.comp (Primrec.list_length.comp zL) (Primrec.list_length.comp zR)))
    (Primrec.const 1)
  refine h.of_eq fun z => ?_
  unfold zbound
  rw [bnd_eq]

/-! ### 判定関数と主定理 -/

/-- 判定関数: `zbound` 歩回して止まっているか。 -/
def zdecide (tbl : List Quint) (z : ZID) : Bool := (zrun tbl (zbound tbl z) z).isNone

theorem zdecide_primrec (tbl : List Quint) : Primrec (zdecide tbl) := by
  have hr : Primrec fun z : ZID => zrun tbl (zbound tbl z) z := by
    have := Primrec.nat_iterate (zbound_primrec tbl) (Primrec.option_some)
      ((Primrec.option_bind Primrec.snd ((zstep_primrec tbl).comp Primrec.snd).to₂).to₂ :
        Primrec₂ fun (_ : ZID) (o : Option ZID) => o.bind (zstep tbl))
    exact this.of_eq fun z => (zrun_eq_iter tbl _ z).symm
  exact (Primrec.not.comp (Primrec.option_isSome.comp hr)).of_eq fun z => by
    unfold zdecide; cases zrun tbl (zbound tbl z) z <;> rfl

/-- **2 状態 RTM の停止問題は有限 ID 上で計算可能に判定できる。** -/
theorem halting_computable {tbl : List Quint} {q₀ q₁ qf : Nat} (hT : TwoStateRTM tbl q₀ q₁ qf) :
    ComputablePred (ZHalts tbl) := by
  refine ComputablePred.computable_iff.mpr ⟨zdecide tbl, (zdecide_primrec tbl).to_comp, ?_⟩
  funext z
  apply propext
  rw [zhalts_iff_bound hT]
  unfold zdecide
  cases zrun tbl (zbound tbl z) z <;> simp

end URTM.Meta
