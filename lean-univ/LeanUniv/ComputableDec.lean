/-
  **Computability of the decoder `d10_8`** (docs/24 §3, Phase C2).

  `d10_8 g = (U10_8.readU g).bind fun p => decMid p.1 p.2.1` with
  `decMid ℓ v = (TRMToTag.dec (TagToCTSH.decWord ((ℓ - 1) / 2) v)).bind L1.dec`.

  Every piece is shown `Primrec` with Mathlib's combinators; the two fuel-bounded structural
  recursions (`TagToCTSH.chunks`, `L1.digs`) are rewritten as a `Nat.iterate` of one step on an
  accumulator (`unf`, `unf_iterate`), and the repetition `rp` as an iterate of a double cons.
  No definition of another module is changed. `CTSH.Ch` gets a `Primcodable` structure through
  `Ch ≃ Bool`; it is only a local instance, since the final statement does not mention `Ch`.
-/
import LeanUniv.Chain10_8
import Mathlib.Computability.Primrec.List

namespace URTM.Univ.ComputableDec
open Primrec

set_option linter.unusedSectionVars false

variable {α β γ : Type*} [Primcodable α] [Primcodable β] [Primcodable γ]

theorem nat_pow : Primrec₂ ((· ^ ·) : ℕ → ℕ → ℕ) := Primrec₂.unpaired'.1 Nat.Primrec.pow

theorem nat_bne (k : ℕ) : Primrec fun a : ℕ => a != k :=
  (Primrec.not.comp (Primrec.beq.comp .id (const k))).of_eq fun _ => rfl

/-- `List.count` on `ℕ` as a right fold. -/
theorem count_eq_foldr (a : ℕ) (l : List ℕ) :
    l.count a = l.foldr (fun b n => bif b == a then n + 1 else n) 0 := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    have h' : (b == a) = decide (b = a) := rfl
    by_cases h : b = a <;> simp [h, h', ih]

theorem list_count {f : α → ℕ} {l : α → List ℕ} (hf : Primrec f) (hl : Primrec l) :
    Primrec fun x => (l x).count (f x) :=
  (list_foldr hl (const 0) (cond (Primrec.beq.comp (fst.comp snd) (hf.comp fst))
    (succ.comp (snd.comp snd)) (snd.comp snd)).to₂).of_eq fun x => by rw [count_eq_foldr]

theorem list_isEmpty : Primrec (@List.isEmpty β) :=
  (Primrec.beq.comp list_length (const 0)).of_eq fun l => by cases l <;> rfl

/-! ### Fuel-bounded unfolding, as an iteration -/

/-- `unf stop out nxt f b`: emit `out b` and continue at `nxt b` until `stop`, at most `f` times. -/
def unf (stop : β → Bool) (out : β → γ) (nxt : β → β) : ℕ → β → List γ
  | 0, _ => []
  | f + 1, b => bif stop b then [] else out b :: unf stop out nxt f (nxt b)

/-- One step of `unf` on an accumulator. -/
def unfStep (stop : β → Bool) (out : β → γ) (nxt : β → β) (s : List γ × β) : List γ × β :=
  bif stop s.2 then s else (s.1 ++ [out s.2], nxt s.2)

theorem unf_iterate (stop : β → Bool) (out : β → γ) (nxt : β → β) (f : ℕ) (acc : List γ) (b : β) :
    ((unfStep stop out nxt)^[f] (acc, b)).1 = acc ++ unf stop out nxt f b := by
  induction f generalizing acc b with
  | zero => simp [unf]
  | succ f ih =>
    rw [Function.iterate_succ_apply]
    cases h : stop b
    · simp [unfStep, unf, h, ih]
    · have hfix : unfStep stop out nxt (acc, b) = (acc, b) := by simp [unfStep, h]
      rw [hfix, Function.iterate_fixed hfix]
      simp [unf, h]

theorem unf_primrec {stop : α → β → Bool} {out : α → β → γ} {nxt : α → β → β} {f : α → ℕ}
    {b : α → β} (hs : Primrec₂ stop) (ho : Primrec₂ out) (hn : Primrec₂ nxt) (hf : Primrec f)
    (hb : Primrec b) : Primrec fun x => unf (stop x) (out x) (nxt x) (f x) (b x) := by
  have hstep : Primrec₂ fun x s => unfStep (stop x) (out x) (nxt x) s :=
    (cond (hs.comp fst (snd.comp snd)) snd
      (pair (list_concat.comp (fst.comp snd) (ho.comp fst (snd.comp snd)))
        (hn.comp fst (snd.comp snd)))).to₂
  exact (fst.comp (nat_iterate hf (pair (const ([] : List γ)) hb) hstep)).of_eq fun x => by
    simp [unf_iterate]

/-! ### Repetition -/

def rpI (n : ℕ) (a b : ℕ) : List ℕ := (fun l => a :: b :: l)^[n] []

theorem rpI_primrec {n a b : α → ℕ} (hn : Primrec n) (ha : Primrec a) (hb : Primrec b) :
    Primrec fun x => rpI (n x) (a x) (b x) :=
  nat_iterate hn (const []) (list_cons.comp (ha.comp fst) (list_cons.comp (hb.comp fst) snd)).to₂


theorem rp_eq (n a b : ℕ) : Tag2.rp n a b = rpI n a b := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Tag2.rp_succ, ih, rpI, rpI, Function.iterate_succ_apply']

/-! ### `CTSH.Ch` as a primcodable type (local) -/

open URTM.CTSH (Ch)

/-- `Y ↦ true`, `N ↦ false`. -/
def chEquiv : Ch ≃ Bool where
  toFun c := match c with | .Y => true | .N => false
  invFun b := bif b then .Y else .N
  left_inv c := by cases c <;> rfl
  right_inv b := by cases b <;> rfl

@[reducible] def chPrimcodable : Primcodable Ch := Primcodable.ofEquiv Bool chEquiv
attribute [local instance] chPrimcodable

theorem ch_finite : Finite Ch := Finite.of_equiv Bool chEquiv.symm
attribute [local instance] ch_finite

/-! ### ϕ⁻¹ (`TagToCTSH.decWord`) -/

section Phi
open TagToCTSH

/-- `N ↦ true`. -/
def isNc : Ch → Bool
  | .N => true
  | .Y => false

theorem leadN_eq (l : List Ch) :
    leadN l = l.foldr (fun c n => bif isNc c then n + 1 else 0) 0 := by
  induction l with
  | nil => rfl
  | cons c l ih => cases c <;> simp [leadN, isNc, ih]

theorem leadN_primrec : Primrec leadN :=
  (list_foldr .id (const 0) (cond ((dom_finite isNc).comp (fst.comp snd))
    (succ.comp (snd.comp snd)) (const 0)).to₂).of_eq fun l => by rw [leadN_eq]; rfl

theorem binval_primrec : Primrec binval :=
  (list_foldl .id (const 0) (nat_add.comp (nat_double.comp (fst.comp snd))
    ((dom_finite bitv).comp (snd.comp snd))).to₂).of_eq fun _ => rfl

theorem decBlock_primrec : Primrec decBlock :=
  (list_casesOn (.id : Primrec fun m : List Ch => m) (const 0)
    (cond (Primrec.beq.comp (fst.comp snd) (const Ch.Y)) (binval_primrec.comp (snd.comp snd))
      (nat_sub.comp (leadN_primrec.comp (list_cons.comp (fst.comp snd) (snd.comp snd)))
        (const 1))).to₂).of_eq fun l => by
    rcases l with _ | ⟨_ | _, r⟩ <;> rfl

theorem chunks_eq {δ : Type} (n f : ℕ) (l : List δ) :
    chunks n f l = unf (fun l => l.isEmpty) (fun l => l.take n) (fun l => l.drop n) f l := by
  induction f generalizing l with
  | zero => rfl
  | succ f ih => cases l <;> simp [chunks, unf, ih]

theorem decWord_primrec : Primrec₂ decWord := by
  have hc : Primrec fun p : ℕ × List Ch =>
      unf (fun l => l.isEmpty) (fun l => l.take (p.1 + 1)) (fun l => l.drop (p.1 + 1))
        p.2.length p.2 :=
    unf_primrec (list_isEmpty.comp snd).to₂ (list_take.comp (succ.comp (fst.comp fst)) snd).to₂
      (list_drop.comp (succ.comp (fst.comp fst)) snd).to₂ (list_length.comp snd) snd
  have h : Primrec fun p : ℕ × List Ch => decWord p.1 p.2 :=
    (list_map hc (decBlock_primrec.comp snd).to₂).of_eq fun p => by
      simp only [decWord, chunks_eq]
  exact h

end Phi

/-! ### The 2-TS readback (`TRMToTag.dec`) -/

section Tag
open TRMToTag

theorem sym_primrec {i κ : α → ℕ} (hi : Primrec i) (hκ : Primrec κ) :
    Primrec fun x => sym (i x) (κ x) :=
  (nat_add.comp (nat_add.comp (const 3) (nat_mul.comp (const 18) hi)) hκ).of_eq fun _ => rfl

theorem W_primrec {i X Y : α → ℕ} (hi : Primrec i) (hX : Primrec X) (hY : Primrec Y) :
    Primrec fun x => W (i x) (X x) (Y x) :=
  (list_cons.comp (sym_primrec hi (const 0)) (list_cons.comp (const xS)
    (list_append.comp (rpI_primrec hX (sym_primrec hi (const 1)) (const xS))
      (list_cons.comp (sym_primrec hi (const 2)) (list_cons.comp (const xS)
        (rpI_primrec hY (sym_primrec hi (const 3)) (const xS))))))).of_eq fun x => by
    simp [W, rp_eq]

/-- The body of `TRMToTag.dec` on a nonempty word `l` with head `a`. -/
def decCore (a : ℕ) (l : List ℕ) : Option TRM.Cfg :=
  if W ((a - 3) / 18) (l.count (sym ((a - 3) / 18) 1)) (l.count (sym ((a - 3) / 18) 3)) = l then
    some ((a - 3) / 18, l.count (sym ((a - 3) / 18) 1), l.count (sym ((a - 3) / 18) 3))
  else none

theorem decCore_primrec : Primrec₂ decCore := by
  have hi : Primrec fun p : ℕ × List ℕ => (p.1 - 3) / 18 :=
    nat_div.comp (nat_sub.comp fst (const 3)) (const 18)
  have hX : Primrec fun p : ℕ × List ℕ => p.2.count (sym ((p.1 - 3) / 18) 1) :=
    list_count (sym_primrec hi (const 1)) snd
  have hY : Primrec fun p : ℕ × List ℕ => p.2.count (sym ((p.1 - 3) / 18) 3) :=
    list_count (sym_primrec hi (const 3)) snd
  exact (Primrec.ite (Primrec.eq.comp (W_primrec hi hX hY) snd)
    (option_some.comp (pair hi (pair hX hY))) (const none)).to₂

theorem tagDec_primrec : Primrec TRMToTag.dec :=
  (list_casesOn (.id : Primrec fun l : List ℕ => l) (const none)
    (decCore_primrec.comp (fst.comp snd) (list_cons.comp (fst.comp snd) (snd.comp snd))).to₂).of_eq
    fun l => by cases l <;> rfl

end Tag

/-! ### The TRM readback (`L1.dec`) -/

section TRMDec
open L1

theorem digs_eq (B f X : ℕ) :
    digs B f X = unf (fun X => X == 0) (fun X => X % B) (fun X => X / B) f X := by
  induction f generalizing X with
  | zero => rfl
  | succ f ih =>
    by_cases h : X = 0
    · simp [digs, unf, h]
    · have h' : (X == 0) = false := by simpa using h
      simp [digs, unf, h, h', ih]

theorem digs_primrec {B f X : α → ℕ} (hB : Primrec B) (hf : Primrec f) (hX : Primrec X) :
    Primrec fun x => digs (B x) (f x) (X x) :=
  (unf_primrec (Primrec.beq.comp snd (const 0)).to₂ (nat_mod.comp snd (hB.comp fst)).to₂
    (nat_div.comp snd (hB.comp fst)).to₂ hf hX).of_eq fun x => by rw [digs_eq]

theorem consT_primrec {s : α → ℕ} {l : α → List ℕ} (hs : Primrec s) (hl : Primrec l) :
    Primrec fun x => L0.consT (s x) (l x) :=
  (Primrec.ite (PrimrecPred.and (Primrec.eq.comp hs (const 0)) (Primrec.eq.comp hl (const [])))
    (const []) (list_cons.comp hs hl)).of_eq fun _ => rfl

theorem l1Dec_primrec : Primrec L1.dec := by
  -- the components of the label `y.1 = pair m (pair r (pair q (pair w s)))`
  have u : Primrec fun y : TRM.Cfg => y.1.unpair := unpair.comp fst
  have u2 : Primrec fun y : TRM.Cfg => y.1.unpair.2.unpair := unpair.comp (snd.comp u)
  have u3 : Primrec fun y : TRM.Cfg => y.1.unpair.2.unpair.2.unpair := unpair.comp (snd.comp u2)
  have u4 : Primrec fun y : TRM.Cfg => y.1.unpair.2.unpair.2.unpair.2.unpair :=
    unpair.comp (snd.comp u3)
  have hB : Primrec fun y : TRM.Cfg => 2 ^ y.1.unpair.2.unpair.2.unpair.2.unpair.1 :=
    nat_pow.comp (const 2) (fst.comp u4)
  have hX : Primrec fun y : TRM.Cfg => y.2.1 := fst.comp snd
  have hY : Primrec fun y : TRM.Cfg => y.2.2 := snd.comp snd
  exact (Primrec.ite (PrimrecPred.and (Primrec.eq.comp (fst.comp u) (const 0))
      (Primrec.eq.comp (fst.comp u2) (const 0)))
    (option_some.comp (pair (fst.comp u3) (pair (digs_primrec hB hX hX)
      (consT_primrec (snd.comp u4) (digs_primrec hB hY hY)))))
    (const none)).of_eq fun y => rfl

end TRMDec

/-! ### The list-level readout (`U10_8.readU`) -/

section Read
open U10_8

theorem chOf_primrec : Primrec chOf :=
  (cond (Primrec.beq.comp .id (const 1)) (const Ch.Y) (const Ch.N)).of_eq fun n => by
    rcases n with _ | _ | n <;> rfl

/-- `readU` with its `match` as a `List.casesOn`. -/
def readU' (g : Spec.Code) : Option (ℕ × URTM.CTSH.ID) :=
  List.casesOn ((g.2.1.reverse ++ g.2.2).dropWhile (· != 7)) none fun _ post =>
    some (((g.2.1.reverse ++ g.2.2).takeWhile (· != 7)).count 6,
      (((post.dropWhile (fun a => a == 4 || a == 5)).takeWhile (fun a => a == 1 || a == 2)).map
        chOf,
       (((g.2.1.reverse ++ g.2.2).takeWhile (· != 7)).reverse.takeWhile (· != 0)).count 6))

theorem readU_eq' (g : Spec.Code) : readU g = readU' g := by
  simp only [readU, readU']
  split <;> simp_all

theorem readU_primrec : Primrec readU := by
  have hL : Primrec fun g : Spec.Code => g.2.1.reverse ++ g.2.2 :=
    list_append.comp (list_reverse.comp (fst.comp snd)) (snd.comp snd)
  have hpre : Primrec fun g : Spec.Code => (g.2.1.reverse ++ g.2.2).takeWhile (· != 7) :=
    (list_takeWhile (nat_bne 7)).comp hL
  have p45 : Primrec fun a : ℕ => a == 4 || a == 5 :=
    Primrec.or.comp (Primrec.beq.comp .id (const 4)) (Primrec.beq.comp .id (const 5))
  have p12 : Primrec fun a : ℕ => a == 1 || a == 2 :=
    Primrec.or.comp (Primrec.beq.comp .id (const 1)) (Primrec.beq.comp .id (const 2))
  have hpost : Primrec fun q : Spec.Code × (ℕ × List ℕ) =>
      (((q.2.2.dropWhile (fun a => a == 4 || a == 5)).takeWhile (fun a => a == 1 || a == 2)).map
        chOf) :=
    list_map ((list_takeWhile p12).comp ((list_dropWhile p45).comp (snd.comp snd)))
      (chOf_primrec.comp snd).to₂
  refine (list_casesOn ((list_dropWhile (nat_bne 7)).comp hL) (const none)
    (option_some.comp (pair (list_count (const 6) (hpre.comp fst)) (pair hpost
      (list_count (const 6) ((list_takeWhile (nat_bne 0)).comp
        (list_reverse.comp (hpre.comp fst))))))).to₂).of_eq fun g => ?_
  rw [readU_eq']; rfl

end Read

/-! ### The decoder -/

open Chain10_8 in
theorem decMid_primrec : Primrec₂ decMid :=
  Primrec.to₂ <| (option_bind (f := fun p : ℕ × List Ch => TRMToTag.dec (TagToCTSH.decWord ((p.1 - 1) / 2) p.2)) (tagDec_primrec.comp (decWord_primrec.comp
      (nat_div.comp (nat_sub.comp fst (const 1)) (const 2)) snd))
    (l1Dec_primrec.comp snd).to₂).of_eq fun _ => rfl

theorem d10_8_primrec : Primrec Chain10_8.d10_8 :=
  (option_bind readU_primrec
    (decMid_primrec.comp (fst.comp snd) (fst.comp (snd.comp snd))).to₂).of_eq fun _ => rfl

/-- **The decoder of the (10,8) chain is computable** (one of the two hypotheses of
    `Chain10_8.exists_urtm_10_8_of_computable`). -/
theorem d10_8_computable : Computable Chain10_8.d10_8 := d10_8_primrec.to_comp

end URTM.Univ.ComputableDec
