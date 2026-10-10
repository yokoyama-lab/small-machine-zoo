/-
  **Computability of the encoder `c10_8`** (docs/24 Phase C2, encoder goal).

  `c10_8_primrec : Primrec Chain10_8.c10_8`, hence `c10_8_computable : Computable c10_8`.

  Nothing is redefined: every component of `c10_8` (`L0.tbl`, `L1.enc`, `L1.progW`,
  `TRMToTag.tagP`/`prodOf`/`W`, `Fin.Sb`, `TagToCTSH.bin`/`phi`/`phiW`/`prodOf`/`ctsh`,
  `U10_8.encList`) is shown primitive recursive as it stands; where the definition is a
  structural recursion that Mathlib's combinators do not match directly (`trim`, `num`, `look`,
  `rp`, `bin`, `Nat.log2`, the case tables of `TRMToTag.prodOf`), an equation with a
  combinator-friendly right-hand side is proved first.

  `Primcodable` instances (all via `Primcodable.ofEquiv`): `Dir ≃ Fin 3`,
  `Quint ≃ ℕ × ℕ × ℕ × Dir × ℕ`, `Ch ≃ Bool`, `Op ≃ (Bool × ℕ) ⊕ (Bool × ℕ) ⊕ (ℕ × ℕ) ⊕ (ℕ × ℕ)`.
-/
import LeanUniv.Chain10_8
import Mathlib.Computability.Primrec.List

namespace URTM.Univ.ComputableEnc
open URTM URTM.Spec URTM.Univ
open URTM.CTSH (Ch)
open URTM.Univ.TRM (Op)
open Primrec

variable {α β γ σ : Type} [Primcodable α] [Primcodable β] [Primcodable γ] [Primcodable σ]

/-! ### `Primcodable` instances -/

/-- `Dir ≃ Fin 3`. -/
def dirEquiv : Dir ≃ Fin 3 where
  toFun | .L => 0 | .Z => 1 | .R => 2
  invFun i := if i.val = 0 then .L else if i.val = 1 then .Z else .R
  left_inv d := by cases d <;> rfl
  right_inv
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
    | ⟨2, _⟩ => rfl

instance : Primcodable Dir := Primcodable.ofEquiv _ dirEquiv
instance : Finite Dir := Finite.of_equiv _ dirEquiv.symm

/-- `Quint ≃ ℕ × ℕ × ℕ × Dir × ℕ` (fields `p, s, t, d, q`). -/
def quintEquiv : Quint ≃ ℕ × ℕ × ℕ × Dir × ℕ where
  toFun r := (r.p, r.s, r.t, r.d, r.q)
  invFun x := ⟨x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Primcodable Quint := Primcodable.ofEquiv _ quintEquiv

/-- `Ch ≃ Bool` (`Y ↦ true`). -/
def chEquiv : Ch ≃ Bool where
  toFun | .Y => true | .N => false
  invFun b := if b then .Y else .N
  left_inv c := by cases c <;> rfl
  right_inv b := by cases b <;> rfl

instance : Primcodable Ch := Primcodable.ofEquiv _ chEquiv
instance : Finite Ch := Finite.of_equiv _ chEquiv.symm

/-- `Op ≃ (Bool × ℕ) ⊕ (Bool × ℕ) ⊕ (ℕ × ℕ) ⊕ (ℕ × ℕ)` (constructor order). -/
def opEquiv : Op ≃ (Bool × ℕ) ⊕ (Bool × ℕ) ⊕ (ℕ × ℕ) ⊕ (ℕ × ℕ) where
  toFun
    | .dbl1 b j => .inl (b, j)
    | .dbl2 b j => .inr (.inl (b, j))
    | .half1 j₀ j₁ => .inr (.inr (.inl (j₀, j₁)))
    | .half2 j₀ j₁ => .inr (.inr (.inr (j₀, j₁)))
  invFun
    | .inl (b, j) => .dbl1 b j
    | .inr (.inl (b, j)) => .dbl2 b j
    | .inr (.inr (.inl (j₀, j₁))) => .half1 j₀ j₁
    | .inr (.inr (.inr (j₀, j₁))) => .half2 j₀ j₁
  left_inv o := by cases o <;> rfl
  right_inv s := by rcases s with ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ <;> rfl

instance : Primcodable Op := Primcodable.ofEquiv _ opEquiv

/-! ### Generic combinators -/

theorem nat_pow : Primrec₂ ((· ^ ·) : ℕ → ℕ → ℕ) := Primrec₂.unpaired'.1 Nat.Primrec.pow

theorem log2_eq_findGreatest (n : ℕ) : Nat.log2 n = Nat.findGreatest (fun k => 2 ^ k ≤ n) n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  apply le_antisymm
  · have h := (Nat.le_log2 hn.ne').1 le_rfl
    exact Nat.le_findGreatest ((Nat.lt_two_pow_self (n := n.log2)).le.trans h) h
  · exact (Nat.le_log2 hn.ne').2 (Nat.findGreatest_spec (P := fun k => 2 ^ k ≤ n) (m := 0)
      (Nat.zero_le _) (by simp; omega))

theorem nat_log2 : Primrec Nat.log2 :=
  (nat_findGreatest (p := fun n k => 2 ^ k ≤ n) Primrec.id
    (nat_le.comp (nat_pow.comp (const 2) snd) fst : PrimrecPred fun a : ℕ × ℕ => 2 ^ a.2 ≤ a.1)).of_eq
    fun n => (log2_eq_findGreatest n).symm

theorem list_replicate : Primrec₂ (fun (n : ℕ) (a : α) => List.replicate n a) :=
  (list_map (list_range.comp fst) (snd.comp fst).to₂).of_eq fun p => by
    dsimp only
    rw [List.map_const', List.length_range]

omit [Primcodable α] in
theorem rp_eq (n : ℕ) (a b : α) : Tag2.rp n a b = (List.replicate n [a, b]).flatten := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Tag2.rp_succ, List.replicate_succ, List.flatten_cons, ih]; rfl

/-- `Tag2.rp`, in the composable form. -/
theorem rp_comp {f : γ → ℕ} {g h : γ → α} (hf : Primrec f) (hg : Primrec g) (hh : Primrec h) :
    Primrec fun x => Tag2.rp (f x) (g x) (h x) :=
  (list_flatten.comp (list_replicate.comp hf
    (list_cons.comp hg (list_cons.comp hh (const []))))).of_eq fun _ => (rp_eq _ _ _).symm

theorem lmax_primrec : Primrec L1.lmax :=
  (list_foldr Primrec.id (const 0) (nat_max.comp (fst.comp snd) (snd.comp snd)).to₂).of_eq
    fun _ => rfl

theorem bool_toNat : Primrec Bool.toNat := dom_finite _


/-! ### Quintuples, directions, symbols, instructions -/

theorem quint_equiv : Primrec quintEquiv := Primrec.of_equiv
theorem quint_p : Primrec Quint.p := (fst.comp quint_equiv).of_eq fun _ => rfl
theorem quint_s : Primrec Quint.s := (fst.comp (snd.comp quint_equiv)).of_eq fun _ => rfl
theorem quint_t : Primrec Quint.t := (fst.comp (snd.comp (snd.comp quint_equiv))).of_eq fun _ => rfl
theorem quint_d : Primrec Quint.d :=
  (fst.comp (snd.comp (snd.comp (snd.comp quint_equiv)))).of_eq fun _ => rfl
theorem quint_q : Primrec Quint.q :=
  (snd.comp (snd.comp (snd.comp (snd.comp quint_equiv)))).of_eq fun _ => rfl

/-- The direction read by `quintOfNat`. -/
def dirOfNat (n : ℕ) : Dir := if n = 0 then .L else if n = 1 then .Z else .R

theorem dirOfNat_primrec : Primrec dirOfNat :=
  ite (Primrec.eq.comp Primrec.id (const 0)) (const _)
    (ite (Primrec.eq.comp Primrec.id (const 1)) (const _) (const _))

theorem quintOfNat_eq (x : ℕ × ℕ × ℕ × ℕ × ℕ) :
    quintOfNat x = quintEquiv.symm (x.1, x.2.1, x.2.2.1, dirOfNat x.2.2.2.1, x.2.2.2.2) := by
  obtain ⟨a, b, c, d, e⟩ := x
  rcases d with _ | _ | d <;> rfl

theorem quintOfNat_primrec : Primrec quintOfNat :=
  ((Primrec.of_equiv_symm (e := quintEquiv)).comp
    (pair fst (pair (fst.comp snd) (pair (fst.comp (snd.comp snd))
      (pair (dirOfNat_primrec.comp (fst.comp (snd.comp (snd.comp snd))))
        (snd.comp (snd.comp (snd.comp snd)))))))).of_eq fun x => (quintOfNat_eq x).symm

theorem dnum_primrec : Primrec L0.dnum := dom_finite _
theorem loN_primrec : Primrec U10_8.loN := dom_finite _

theorem ch_of_bool : Primrec fun b : Bool => (if b then Ch.Y else Ch.N) := dom_finite _

theorem op_symm : Primrec opEquiv.symm := Primrec.of_equiv_symm
theorem op_equiv : Primrec opEquiv := Primrec.of_equiv

theorem dbl1_comp {f : γ → Bool} {g : γ → ℕ} (hf : Primrec f) (hg : Primrec g) :
    Primrec fun x => Op.dbl1 (f x) (g x) :=
  (op_symm.comp (sumInl.comp (pair hf hg))).of_eq fun _ => rfl
theorem dbl2_comp {f : γ → Bool} {g : γ → ℕ} (hf : Primrec f) (hg : Primrec g) :
    Primrec fun x => Op.dbl2 (f x) (g x) :=
  (op_symm.comp (sumInr.comp (sumInl.comp (pair hf hg)))).of_eq fun _ => rfl
theorem half1_comp {f g : γ → ℕ} (hf : Primrec f) (hg : Primrec g) :
    Primrec fun x => Op.half1 (f x) (g x) :=
  (op_symm.comp (sumInr.comp (sumInr.comp (sumInl.comp (pair hf hg))))).of_eq fun _ => rfl
theorem half2_comp {f g : γ → ℕ} (hf : Primrec f) (hg : Primrec g) :
    Primrec fun x => Op.half2 (f x) (g x) :=
  (op_symm.comp (sumInr.comp (sumInr.comp (sumInr.comp (pair hf hg))))).of_eq fun _ => rfl

theorem natPair_comp {f g : γ → ℕ} (hf : Primrec f) (hg : Primrec g) :
    Primrec fun x => Nat.pair (f x) (g x) := Primrec₂.natPair.comp hf hg

theorem pow_comp {f g : γ → ℕ} (hf : Primrec f) (hg : Primrec g) :
    Primrec fun x => f x ^ g x := nat_pow.comp hf hg

/-! ### L0: the table -/

theorem tbl_primrec : Primrec L0.tbl :=
  (list_map (Primrec.ofNat (List (ℕ × ℕ × ℕ × ℕ × ℕ))) (quintOfNat_primrec.comp snd).to₂).of_eq
    fun _ => rfl

/-! ### Table scalars -/

theorem symbols_primrec : Primrec symbols :=
  list_flatMap Primrec.id
    (list_cons.comp (quint_s.comp snd) (list_cons.comp (quint_t.comp snd) (const []))).to₂

theorem states_primrec : Primrec states :=
  list_flatMap Primrec.id
    (list_cons.comp (quint_p.comp snd) (list_cons.comp (quint_q.comp snd) (const []))).to₂

theorem width_primrec : Primrec L1.width :=
  (succ.comp (nat_log2.comp (lmax_primrec.comp symbols_primrec))).of_eq fun _ => rfl

theorem Qm_primrec : Primrec Fin.Qm := lmax_primrec.comp states_primrec

theorem Kb_primrec : Primrec Fin.Kb :=
  nat_add.comp (nat_add.comp Qm_primrec (pow_comp (const 2) width_primrec)) (const 3)

theorem Rb_comp {f : γ → ℕ} (hf : Primrec f) : Primrec fun x => Fin.Rb (f x) :=
  natPair_comp hf (natPair_comp hf (natPair_comp hf (natPair_comp hf hf)))

theorem Nb_primrec : Primrec Fin.Nb :=
  nat_add.comp (natPair_comp Kb_primrec (natPair_comp Kb_primrec (natPair_comp Kb_primrec
    (natPair_comp Kb_primrec (Rb_comp Kb_primrec))))) (const 1)

theorem Sb_primrec : Primrec Fin.Sb := nat_add.comp (const 3) (nat_mul.comp (const 18) Nb_primrec)

/-! ### L1: the encoder -/

theorem consT_primrec : Primrec₂ L0.consT :=
  ite (PrimrecPred.and (Primrec.eq.comp fst (const 0)) (Primrec.eq.comp snd (const [])))
    (const []) list_cons

theorem trim_eq (l : List ℕ) : L0.trim l = l.foldr L0.consT [] := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [L0.trim, List.foldr_cons, ih]

theorem trim_primrec : Primrec L0.trim :=
  (list_foldr Primrec.id (const []) (consT_primrec.comp (fst.comp snd) (snd.comp snd)).to₂).of_eq
    fun l => (trim_eq l).symm

theorem norm_primrec : Primrec L0.norm :=
  pair fst (pair (trim_primrec.comp (fst.comp snd)) (trim_primrec.comp (snd.comp snd)))

theorem num_eq (B : ℕ) (l : List ℕ) : L1.num B l = l.foldr (fun a s => a + B * s) 0 := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [L1.num, List.foldr_cons, ih]

theorem num_primrec : Primrec₂ L1.num :=
  (list_foldr snd (const 0)
    (nat_add.comp (fst.comp snd) (nat_mul.comp (fst.comp fst) (snd.comp snd))).to₂).of_eq
    fun p => (num_eq p.1 p.2).symm

theorem lRd_comp {f g h k : γ → ℕ} (hf : Primrec f) (hg : Primrec g) (hh : Primrec h)
    (hk : Primrec k) : Primrec fun x => L1.lRd (f x) (g x) (h x) (k x) :=
  natPair_comp (const 0) (natPair_comp hf (natPair_comp hg (natPair_comp hh hk)))

theorem lPush_comp {f g h k : γ → ℕ} (hf : Primrec f) (hg : Primrec g) (hh : Primrec h)
    (hk : Primrec k) : Primrec fun x => L1.lPush (f x) (g x) (h x) (k x) :=
  natPair_comp (const 1) (natPair_comp hf (natPair_comp hg (natPair_comp hh hk)))

theorem lNrm_comp {f : γ → ℕ} (hf : Primrec f) : Primrec fun x => L1.lNrm (f x) :=
  natPair_comp (const 2) hf

theorem lNrm'_comp {f : γ → ℕ} (hf : Primrec f) : Primrec fun x => L1.lNrm' (f x) :=
  natPair_comp (const 3) hf

/-- `L1.enc`, as a function of `(T, z)`. -/
theorem l1enc_primrec : Primrec₂ L1.enc := by
  have T := (fst : Primrec fun p : List Quint × Code => p.1)
  have z := (snd : Primrec fun p : List Quint × Code => p.2)
  have B := pow_comp (const 2) (width_primrec.comp T)
  exact (pair (ite (Primrec.eq.comp (norm_primrec.comp z) z)
      (lRd_comp (const 0) (fst.comp z) (const 0) (const 0)) (lNrm_comp (fst.comp z)))
    (pair (num_primrec.comp B (fst.comp (snd.comp z)))
      (num_primrec.comp B (snd.comp (snd.comp z))))).of_eq fun _ => rfl

/-! ### L2: the canonical word -/

theorem sym_comp {f g : γ → ℕ} (hf : Primrec f) (hg : Primrec g) :
    Primrec fun x => TRMToTag.sym (f x) (g x) :=
  nat_add.comp (nat_add.comp (const 3) (nat_mul.comp (const 18) hf)) hg

theorem W_comp {f g h : γ → ℕ} (hf : Primrec f) (hg : Primrec g) (hh : Primrec h) :
    Primrec fun x => TRMToTag.W (f x) (g x) (h x) :=
  (list_cons.comp (sym_comp hf (const 0)) (list_cons.comp (const 0)
    (list_append.comp (rp_comp hg (sym_comp hf (const 1)) (const 0))
      (list_cons.comp (sym_comp hf (const 2)) (list_cons.comp (const 0)
        (rp_comp hh (sym_comp hf (const 3)) (const 0))))))).of_eq fun _ => rfl

theorem tagEnc_primrec : Primrec TRMToTag.enc :=
  W_comp fst (fst.comp snd) (snd.comp snd)


/-! ### L1: the program -/

theorem rhs_primrec : Primrec L0.rhs :=
  pair quint_t (pair (dnum_primrec.comp quint_d) quint_q)

theorem look_eq (T : List Quint) (q s : ℕ) :
    L0.look T q s = T.foldr (fun r acc => if r.p = q ∧ r.s = s then some (L0.rhs r) else acc) none := by
  induction T with
  | nil => rfl
  | cons r T ih => simp only [L0.look, List.foldr_cons, ih]

theorem look_comp {f : γ → List Quint} {g h : γ → ℕ} (hf : Primrec f) (hg : Primrec g)
    (hh : Primrec h) : Primrec fun x => L0.look (f x) (g x) (h x) :=
  (list_foldr hf (const none)
    (ite (PrimrecPred.and (Primrec.eq.comp (quint_p.comp (fst.comp snd)) (hg.comp fst))
        (Primrec.eq.comp (quint_s.comp (fst.comp snd)) (hh.comp fst)))
      (option_some.comp (rhs_primrec.comp (fst.comp snd))) (snd.comp snd)).to₂).of_eq
    fun x => (look_eq (f x) (g x) (h x)).symm

theorem bit_comp {f g : γ → ℕ} (hf : Primrec f) (hg : Primrec g) :
    Primrec fun x => L1.bit (f x) (g x) :=
  (Primrec.eq.comp (nat_mod.comp (nat_div.comp hf (pow_comp (const 2) hg)) (const 2))
    (const 1)).decide

theorem pushOp_comp {r v k c : γ → ℕ} (hr : Primrec r) (hv : Primrec v) (hk : Primrec k)
    (hc : Primrec c) : Primrec fun x => L1.pushOp (r x) (v x) (k x) (c x) := by
  have hk1 := nat_sub.comp hk (const 1)
  have hb := bit_comp hv hk1
  have hj := ite (nat_le.comp hk (const 1)) hc (lPush_comp hr hv hk1 hc)
  exact ite (Primrec.eq.comp hr (const 1)) (dbl1_comp hb hj) (dbl2_comp hb hj)

theorem act_comp {w : γ → ℕ} {o : γ → ℕ × ℕ × ℕ} (hw : Primrec w) (ho : Primrec o) :
    Primrec fun x => L1.act (w x) (o x) := by
  have t := fst.comp ho
  have d := fst.comp (snd.comp ho)
  have q := snd.comp (snd.comp ho)
  exact ite (Primrec.eq.comp d (const 0))
    (pushOp_comp (const 2) t hw (lRd_comp (const 1) q (const 0) (const 0)))
    (ite (Primrec.eq.comp d (const 1))
      (pushOp_comp (const 2) t hw (lRd_comp (const 0) q (const 0) (const 0)))
      (pushOp_comp (const 1) t hw (lRd_comp (const 0) q (const 0) (const 0))))

/-- `L1.progW`, as a function of `(T, w, i)`. -/
theorem progW_primrec : Primrec fun p : List Quint × ℕ × ℕ => L1.progW p.1 p.2.1 p.2.2 := by
  have T := (fst : Primrec fun p : List Quint × ℕ × ℕ => p.1)
  have w := (fst.comp snd : Primrec fun p : List Quint × ℕ × ℕ => p.2.1)
  have i := (snd.comp snd : Primrec fun p : List Quint × ℕ × ℕ => p.2.2)
  have u0 := fst.comp (unpair.comp i)
  have i1 := snd.comp (unpair.comp i)
  have m := fst.comp (unpair.comp i1)
  have i2 := snd.comp (unpair.comp i1)
  have q := fst.comp (unpair.comp i2)
  have i3 := snd.comp (unpair.comp i2)
  have j := fst.comp (unpair.comp i3)
  have acc := snd.comp (unpair.comp i3)
  have j1 := nat_add.comp j (const 1)
  have acc2 := nat_add.comp acc (pow_comp (const 2) j)
  have rd := ite (Primrec.eq.comp m (const 0))
    (half2_comp (lRd_comp (const 0) q j1 acc) (lRd_comp (const 0) q j1 acc2))
    (half1_comp (lRd_comp (const 1) q j1 acc) (lRd_comp (const 1) q j1 acc2))
  have lk := option_map (look_comp T q acc) (act_comp (w.comp fst) snd).to₂
  have ps := option_some.comp (pushOp_comp (const 2) acc w (lRd_comp (const 0) q (const 0) (const 0)))
  have h0 := ite (nat_lt.comp j w) (option_some.comp rd) (ite (Primrec.eq.comp m (const 0)) lk ps)
  have h1 := option_some.comp (pushOp_comp m q j acc)
  have h2 := option_some.comp (dbl1_comp (const false) (lNrm'_comp i1))
  have h3 := option_some.comp (half1_comp (lRd_comp (const 0) i1 (const 0) (const 0))
    (lRd_comp (const 0) i1 (const 0) (const 0)))
  exact (ite (Primrec.eq.comp u0 (const 0)) h0 (ite (Primrec.eq.comp u0 (const 1)) h1
    (ite (Primrec.eq.comp u0 (const 2)) h2 (ite (Primrec.eq.comp u0 (const 3)) h3
      (const none))))).of_eq fun _ => rfl

/-! ### L2: the productions -/

open TRMToTag in
/-- The case table of `prodOf i (.dbl1 b j)`. -/
def tabDbl1 (b : Bool) (j : ℕ) : List (Option (List ℕ)) :=
  [some ([sym j 0, xS] ++ Tag2.rp b.toNat (sym j 1) xS), some [sym j 1, xS, sym j 1, xS],
    some [sym j 2, xS], some [sym j 3, xS]]

open TRMToTag in
/-- The case table of `prodOf i (.dbl2 b j)`. -/
def tabDbl2 (b : Bool) (j : ℕ) : List (Option (List ℕ)) :=
  [some [sym j 0, xS], some [sym j 1, xS], some ([sym j 2, xS] ++ Tag2.rp b.toNat (sym j 3) xS),
    some [sym j 3, xS, sym j 3, xS]]

/-- A symbol given by a code `(sel, k)`: the filler `k` (`sel = 0`), or `sym i k`,
    `sym j₀ k`, `sym j₁ k` (`sel = 1, 2, ≥ 3`). -/
def interp (i j₀ j₁ : ℕ) (e : ℕ × ℕ) : ℕ :=
  if e.1 = 0 then e.2 else if e.1 = 1 then TRMToTag.sym i e.2
  else if e.1 = 2 then TRMToTag.sym j₀ e.2 else TRMToTag.sym j₁ e.2

/-- The case table of `prodOf i (.half1 j₀ j₁)`, as symbol codes. -/
def codeHalf1 : List (List (ℕ × ℕ)) :=
  [[(1, 4)], [(1, 5)], [(1, 6), (1, 7)], [(1, 8), (1, 9)], [(1, 10), (1, 11)], [(1, 12), (1, 13)],
    [(1, 14), (0, 1)], [(0, 1), (1, 16), (0, 1)], [(1, 15), (0, 1)], [(1, 17), (0, 1)],
    [(3, 0), (0, 0)], [(2, 0), (0, 0)], [(3, 1), (0, 0)], [(2, 1), (0, 0)],
    [(3, 2), (0, 0)], [(3, 3), (0, 0)], [(2, 2), (0, 0)], [(2, 3), (0, 0)]]

/-- The case table of `prodOf i (.half2 j₀ j₁)`, as symbol codes. -/
def codeHalf2 : List (List (ℕ × ℕ)) :=
  [[(1, 4), (0, 1)], [(1, 5), (0, 1)], [(1, 6)], [(1, 7)], [(1, 8), (1, 9)], [(1, 10), (1, 11)],
    [(1, 12), (1, 13)], [(1, 14), (1, 15)],
    [(3, 0), (0, 0)], [(0, 2), (2, 0), (0, 0)], [(3, 1), (0, 0)], [(2, 1), (0, 0)],
    [(3, 2), (0, 0)], [(2, 2), (0, 0)], [(3, 3), (0, 0)], [(2, 3), (0, 0)]]

/-- A code table read at `(i, j₀, j₁)`. -/
def tabOf (C : List (List (ℕ × ℕ))) (i j₀ j₁ : ℕ) : List (Option (List ℕ)) :=
  C.map fun e => some (e.map (interp i j₀ j₁))

theorem prodOf_dbl1 (i : ℕ) (b : Bool) (j κ : ℕ) :
    TRMToTag.prodOf i (.dbl1 b j) κ = (tabDbl1 b j).getD κ none := by
  match κ with
  | 0 | 1 | 2 | 3 => rfl
  | κ + 4 => rfl

theorem prodOf_dbl2 (i : ℕ) (b : Bool) (j κ : ℕ) :
    TRMToTag.prodOf i (.dbl2 b j) κ = (tabDbl2 b j).getD κ none := by
  match κ with
  | 0 | 1 | 2 | 3 => rfl
  | κ + 4 => rfl

theorem prodOf_half1 (i j₀ j₁ κ : ℕ) :
    TRMToTag.prodOf i (.half1 j₀ j₁) κ = (tabOf codeHalf1 i j₀ j₁).getD κ none := by
  match κ with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 | 16 | 17 => rfl
  | κ + 18 => rfl

theorem prodOf_half2 (i j₀ j₁ κ : ℕ) :
    TRMToTag.prodOf i (.half2 j₀ j₁) κ = (tabOf codeHalf2 i j₀ j₁).getD κ none := by
  match κ with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 => rfl
  | κ + 16 => rfl


theorem interp_comp {i j₀ j₁ : γ → ℕ} {e : γ → ℕ × ℕ} (hi : Primrec i) (hj₀ : Primrec j₀)
    (hj₁ : Primrec j₁) (he : Primrec e) : Primrec fun x => interp (i x) (j₀ x) (j₁ x) (e x) :=
  ite (Primrec.eq.comp (fst.comp he) (const 0)) (snd.comp he)
    (ite (Primrec.eq.comp (fst.comp he) (const 1)) (sym_comp hi (snd.comp he))
      (ite (Primrec.eq.comp (fst.comp he) (const 2)) (sym_comp hj₀ (snd.comp he))
        (sym_comp hj₁ (snd.comp he))))

theorem tabOf_comp (C : List (List (ℕ × ℕ))) {i j₀ j₁ : γ → ℕ} (hi : Primrec i)
    (hj₀ : Primrec j₀) (hj₁ : Primrec j₁) : Primrec fun x => tabOf C (i x) (j₀ x) (j₁ x) :=
  list_map (const C) (option_some.comp (list_map snd
    (interp_comp (hi.comp (fst.comp fst)) (hj₀.comp (fst.comp fst)) (hj₁.comp (fst.comp fst))
      snd).to₂)).to₂

theorem tabDbl1_comp {b : γ → Bool} {j : γ → ℕ} (hb : Primrec b) (hj : Primrec j) :
    Primrec fun x => tabDbl1 (b x) (j x) :=
  list_cons.comp (option_some.comp (list_append.comp
      (list_cons.comp (sym_comp hj (const 0)) (list_cons.comp (const 0) (const [])))
      (rp_comp (bool_toNat.comp hb) (sym_comp hj (const 1)) (const 0))))
    (list_cons.comp (option_some.comp (list_cons.comp (sym_comp hj (const 1))
        (list_cons.comp (const 0) (list_cons.comp (sym_comp hj (const 1))
          (list_cons.comp (const 0) (const []))))))
      (list_cons.comp (option_some.comp (list_cons.comp (sym_comp hj (const 2))
          (list_cons.comp (const 0) (const []))))
        (list_cons.comp (option_some.comp (list_cons.comp (sym_comp hj (const 3))
          (list_cons.comp (const 0) (const [])))) (const []))))

theorem tabDbl2_comp {b : γ → Bool} {j : γ → ℕ} (hb : Primrec b) (hj : Primrec j) :
    Primrec fun x => tabDbl2 (b x) (j x) :=
  list_cons.comp (option_some.comp (list_cons.comp (sym_comp hj (const 0))
      (list_cons.comp (const 0) (const []))))
    (list_cons.comp (option_some.comp (list_cons.comp (sym_comp hj (const 1))
        (list_cons.comp (const 0) (const []))))
      (list_cons.comp (option_some.comp (list_append.comp
          (list_cons.comp (sym_comp hj (const 2)) (list_cons.comp (const 0) (const [])))
          (rp_comp (bool_toNat.comp hb) (sym_comp hj (const 3)) (const 0))))
        (list_cons.comp (option_some.comp (list_cons.comp (sym_comp hj (const 3))
          (list_cons.comp (const 0) (list_cons.comp (sym_comp hj (const 3))
            (list_cons.comp (const 0) (const [])))))) (const []))))

/-- `TRMToTag.prodOf`, as a function of `(i, op, κ)`. -/
theorem prodOf_primrec : Primrec fun p : ℕ × Op × ℕ => TRMToTag.prodOf p.1 p.2.1 p.2.2 := by
  have G := list_getD (none : Option (List ℕ))
  have h1 : Primrec₂ fun (p : ℕ × Op × ℕ) (bj : Bool × ℕ) => (tabDbl1 bj.1 bj.2).getD p.2.2 none :=
    (G.comp (tabDbl1_comp (fst.comp snd) (snd.comp snd)) (snd.comp (snd.comp fst))).to₂
  have h2 : Primrec₂ fun (p : ℕ × Op × ℕ) (bj : Bool × ℕ) => (tabDbl2 bj.1 bj.2).getD p.2.2 none :=
    (G.comp (tabDbl2_comp (fst.comp snd) (snd.comp snd)) (snd.comp (snd.comp fst))).to₂
  have h3 : Primrec₂ fun (p : ℕ × Op × ℕ) (jj : ℕ × ℕ) =>
      (tabOf codeHalf1 p.1 jj.1 jj.2).getD p.2.2 none :=
    (G.comp (tabOf_comp codeHalf1 (fst.comp fst) (fst.comp snd) (snd.comp snd))
      (snd.comp (snd.comp fst))).to₂
  have h4 : Primrec₂ fun (p : ℕ × Op × ℕ) (jj : ℕ × ℕ) =>
      (tabOf codeHalf2 p.1 jj.1 jj.2).getD p.2.2 none :=
    (G.comp (tabOf_comp codeHalf2 (fst.comp fst) (fst.comp snd) (snd.comp snd))
      (snd.comp (snd.comp fst))).to₂
  have h34 : Primrec₂ fun (p : ℕ × Op × ℕ) (s : (ℕ × ℕ) ⊕ (ℕ × ℕ)) =>
      Sum.casesOn (motive := fun _ => Option (List ℕ)) s
        (fun jj => (tabOf codeHalf1 p.1 jj.1 jj.2).getD p.2.2 none)
        (fun jj => (tabOf codeHalf2 p.1 jj.1 jj.2).getD p.2.2 none) :=
    (sumCasesOn snd (h3.comp (fst.comp fst) snd).to₂ (h4.comp (fst.comp fst) snd).to₂).to₂
  have h234 : Primrec₂ fun (p : ℕ × Op × ℕ) (s : (Bool × ℕ) ⊕ (ℕ × ℕ) ⊕ (ℕ × ℕ)) =>
      Sum.casesOn (motive := fun _ => Option (List ℕ)) s
        (fun bj => (tabDbl2 bj.1 bj.2).getD p.2.2 none)
        (fun s => Sum.casesOn (motive := fun _ => Option (List ℕ)) s
          (fun jj => (tabOf codeHalf1 p.1 jj.1 jj.2).getD p.2.2 none)
          (fun jj => (tabOf codeHalf2 p.1 jj.1 jj.2).getD p.2.2 none)) :=
    (sumCasesOn snd (h2.comp (fst.comp fst) snd).to₂ (h34.comp (fst.comp fst) snd).to₂).to₂
  refine (sumCasesOn (op_equiv.comp (fst.comp snd)) h1 h234).of_eq fun p => ?_
  obtain ⟨i, op, κ⟩ := p
  cases op with
  | dbl1 b j => exact (prodOf_dbl1 i b j κ).symm
  | dbl2 b j => exact (prodOf_dbl2 i b j κ).symm
  | half1 j₀ j₁ => exact (prodOf_half1 i j₀ j₁ κ).symm
  | half2 j₀ j₁ => exact (prodOf_half2 i j₀ j₁ κ).symm

/-- `tagOf T x = tagP (L1.prog T) x`, as a function of `(T, x)`. -/
theorem tagOf_primrec : Primrec₂ Chain10_8.tagOf := by
  have T := (fst : Primrec fun p : List Quint × ℕ => p.1)
  have n := (snd : Primrec fun p : List Quint × ℕ => p.2)
  have lab := nat_div.comp (nat_sub.comp n (const 3)) (const 18)
  have kap := nat_mod.comp (nat_sub.comp n (const 3)) (const 18)
  have hp := progW_primrec.comp (pair T (pair (width_primrec.comp T) lab))
  have hb := option_bind hp (prodOf_primrec.comp (pair (lab.comp fst) (pair snd (kap.comp fst)))).to₂
  exact (ite (nat_lt.comp n (const 3)) (const none) hb).of_eq fun _ => rfl


/-! ### L3: the CTSH and ϕ -/

theorem bin_eq (k x : ℕ) :
    TagToCTSH.bin k x = ((List.range k).map fun i => if x / 2 ^ i % 2 = 1 then Ch.Y else Ch.N).reverse := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    rw [TagToCTSH.bin, ih, List.range_succ_eq_map, List.map_cons, List.map_map, List.reverse_cons]
    simp [Function.comp_def, Nat.div_div_eq_div_mul, pow_succ']

theorem bin_primrec : Primrec₂ TagToCTSH.bin :=
  (list_reverse.comp (list_map (list_range.comp fst)
    (ite (Primrec.eq.comp (nat_mod.comp (nat_div.comp (snd.comp fst) (pow_comp (const 2) snd))
      (const 2)) (const 1)) (const Ch.Y) (const Ch.N)).to₂)).of_eq fun p => (bin_eq p.1 p.2).symm

/-- ϕ for the table `T`, as a function of `(T, x)`. -/
theorem phi_primrec :
    Primrec₂ fun (T : List Quint) (x : ℕ) => TagToCTSH.phi (Fin.Sb T) (Chain10_8.tagOf T) x := by
  have T := (fst : Primrec fun p : List Quint × ℕ => p.1)
  have x := (snd : Primrec fun p : List Quint × ℕ => p.2)
  have S := Sb_primrec.comp T
  have hs : Primrec₂ fun (p : List Quint × ℕ) (_ : List ℕ) =>
      List.replicate (p.2 + 1) Ch.N ++ Ch.Y :: List.replicate (Fin.Sb p.1 - p.2 - 1) Ch.N :=
    (list_append.comp (list_replicate.comp (succ.comp (x.comp fst)) (const Ch.N))
      (list_cons.comp (const Ch.Y) (list_replicate.comp
        (nat_sub.comp (nat_sub.comp (S.comp fst) (x.comp fst)) (const 1)) (const Ch.N)))).to₂
  have hn := list_cons.comp (const Ch.Y) (bin_primrec.comp S x)
  refine (option_casesOn (tagOf_primrec.comp T x) hn hs).to₂.of_eq fun T x => ?_
  rcases h : Chain10_8.tagOf T x with _ | w <;> simp [TagToCTSH.phi, h]

theorem phiW_primrec :
    Primrec₂ fun (T : List Quint) (w : List ℕ) => TagToCTSH.phiW (Fin.Sb T) (Chain10_8.tagOf T) w :=
  list_flatMap snd (phi_primrec.comp (fst.comp fst) snd).to₂

theorem ctshProd_primrec :
    Primrec₂ fun (T : List Quint) (j : ℕ) => TagToCTSH.prodOf (Fin.Sb T) (Chain10_8.tagOf T) j := by
  have T := (fst : Primrec fun p : List Quint × ℕ => p.1)
  have j := (snd : Primrec fun p : List Quint × ℕ => p.2)
  refine (ite (nat_lt.comp j (Sb_primrec.comp T))
    (option_casesOn (tagOf_primrec.comp T j) (const []) (phiW_primrec.comp (T.comp fst) snd).to₂)
    (const [])).to₂.of_eq fun T j => ?_
  simp only [TagToCTSH.prodOf]
  split_ifs <;> rcases Chain10_8.tagOf T j with _ | w <;> rfl

theorem ctshOf_primrec : Primrec Chain10_8.ctshOf :=
  (list_map (list_range.comp (nat_add.comp (nat_mul.comp (const 2) Sb_primrec) (const 1)))
    ctshProd_primrec).of_eq fun T => by simp only [Chain10_8.ctshOf, TagToCTSH.ctsh]

theorem wordOf_primrec : Primrec₂ Chain10_8.wordOf :=
  (phiW_primrec.comp fst (tagEnc_primrec.comp (l1enc_primrec.comp fst snd))).of_eq fun _ => rfl

/-! ### L4 and the encoder -/

theorem encList_primrec : Primrec₂ U10_8.encList := by
  have C := (fst : Primrec fun p : URTM.CTSH.CTSH × List Ch => p.1)
  have w := (snd : Primrec fun p : URTM.CTSH.CTSH × List Ch => p.2)
  have fl := list_flatMap C (list_cons.comp (const 6) (list_map snd (loN_primrec.comp snd).to₂)).to₂
  exact (pair (const 0) (pair (list_append.comp (list_cons.comp (const 7) (list_cons.comp (const 0) fl))
    (const [0])) (list_map w (loN_primrec.comp snd).to₂))).of_eq fun _ => rfl

/-- **The encoder `c10_8` is primitive recursive.** -/
theorem c10_8_primrec : Primrec Chain10_8.c10_8 :=
  encList_primrec.comp (ctshOf_primrec.comp (tbl_primrec.comp fst))
    (wordOf_primrec.comp (tbl_primrec.comp fst) snd)

/-- **The encoder `c10_8` is computable** (Phase C2, encoder goal). -/
theorem c10_8_computable : Computable Chain10_8.c10_8 := c10_8_primrec.to_comp

end URTM.Univ.ComputableEnc
