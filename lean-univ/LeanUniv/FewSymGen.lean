/-
  **Symbol reductions are UTMs in the sense of Def. 7.1: the generic part** (docs/24, docs/23).

  A symbol reduction `M` of a base machine `T` (`URTM.FewSym`) writes every symbol `s` of `T` as a
  block of `k` bits `E.code s` and simulates `T` from the encoded initial configuration
  (`FewSym.fs_simulates`). Where `T` applies a halting quintuple (reading `hs h` in the state `f h`),
  `M` runs inside the head block and halts there (`FewSym.pre`): in the state `fs h`, with the head
  `dd h` cells into the block, the block holding the code of `ws h` (a finite fact, `decide`).
  For URTM(85,2) (`U85_2.lean`) the run is empty (`dd h = 0`, `ws h = hs h`); for the other
  reductions it can move the head inside the block and rewrite it.

  * `decK k d`: decode a list in blocks of `k` cells (`ComputableDec.unf`); `dR tab k` / `dL tab k`:
    the block read to the right / to the left, looked up in `tab`.
  * `readFS`: the readout. From the state number `q` of the halting ID: move the head back `off q`
    cells to the start of its block (`realign`), replace the head block by `fx q` (the code of the
    symbol that `T` read when it halted, `fixH`), decode both lists and apply the base readout `R`
    in the state `stm q`. It depends only on the ID (`readFS_toID`) and is primitive recursive
    (`readFS_primrec`).
  * `encFS`: the encoder; every cell of the base code becomes its block.
  * `isUTMStrict_fewsym`: `IsUTMStrict (numT num M)` from the simulation of `fs_simulates`, the base's
    final configurations read by `R`, and the finite facts on `M`.
-/
import LeanUniv.U85_2

namespace URTM.Univ.FewSymGen
open URTM URTM.CTSH URTM.Univ.KToSpec URTM.Univ.NumGen
open URTM.KState (Tgt Cfg Machine HaltsIn)
open URTM.FewSym (bits enc pre glob hrun hfuel LCfg ovl ovl_block Enc)
open URTM.Univ.U85_2 (bits_tp take_flatMap_block drop_flatMap_block unf_nil)

/-! ### Blocks of `k` cells -/

/-- The first `k` cells of `l` (missing cells blank). -/
def blk (k : ℕ) (l : List ℕ) : List ℕ := (List.range k).map fun i => l.getD i 0

/-- The number of a block of bits, the first cell most significant. -/
def val (b : List ℕ) : ℕ := b.foldl (fun a x => 2 * a + x) 0

/-- The symbol number of the block at the start of `l`, read to the right. -/
def dR (tab : List ℕ) (k : ℕ) (l : List ℕ) : ℕ := tab.getD (val (blk k l)) 0

/-- The symbol number of the block at the start of `l`, read to the left (`l` is the left list of a
    code: the cell next to the head first). -/
def dL (tab : List ℕ) (k : ℕ) (l : List ℕ) : ℕ := tab.getD (val (blk k l).reverse) 0

/-- Decode a list in blocks of `k` cells by `d`. -/
def decK (k : ℕ) (d : List ℕ → ℕ) (l : List ℕ) : List ℕ :=
  ComputableDec.unf (fun l : List ℕ => l.isEmpty) d (fun l => l.drop k) l.length l

theorem blk_pad (k : ℕ) (l : List ℕ) (j : ℕ) : blk k (l ++ List.replicate j 0) = blk k l := by
  simp only [blk, Spec.CodePad.getD_append_replicate]

theorem blk_append (k : ℕ) (b t : List ℕ) (hb : b.length = k) : blk k (b ++ t) = b := by
  apply List.ext_getElem (by simp [blk, hb])
  intro i h1 h2
  simp only [blk, List.getElem_map, List.getElem_range]
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left h2, List.getElem?_eq_getElem h2]
  rfl

theorem blk_take (k : ℕ) (l : List ℕ) (hk : k ≤ l.length) : blk k l = l.take k := by
  apply List.ext_getElem (by simp [blk]; omega)
  intro i h1 h2
  simp only [blk, List.getElem_map, List.getElem_range, List.getElem_take]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [blk] at h1; omega)]
  rfl

theorem dR_pad (tab : List ℕ) (k : ℕ) (l : List ℕ) (j : ℕ) :
    dR tab k (l ++ List.replicate j 0) = dR tab k l := by
  simp only [dR, blk_pad]

theorem dL_pad (tab : List ℕ) (k : ℕ) (l : List ℕ) (j : ℕ) :
    dL tab k (l ++ List.replicate j 0) = dL tab k l := by
  simp only [dL, blk_pad]

theorem val_zeros (k : ℕ) : val (List.replicate k 0) = 0 := by
  suffices h : ∀ a, (List.replicate k 0).foldl (fun a x => 2 * a + x) a = 2 ^ k * a by
    simpa [val] using h 0
  induction k with
  | zero => intro a; simp
  | succ k ih => intro a; rw [List.replicate_succ, List.foldl_cons, ih, pow_succ]; ring

theorem blk_nil (k : ℕ) : blk k [] = List.replicate k 0 := by
  simp [blk, List.map_const']

theorem dR_zeros (tab : List ℕ) (h0 : tab.getD 0 0 = 0) (k j : ℕ) :
    dR tab k (List.replicate j 0) = 0 := by
  have := dR_pad tab k [] j
  simp only [List.nil_append] at this
  rw [this, dR, blk_nil, val_zeros, h0]

theorem dL_zeros (tab : List ℕ) (h0 : tab.getD 0 0 = 0) (k j : ℕ) :
    dL tab k (List.replicate j 0) = 0 := by
  have := dL_pad tab k [] j
  simp only [List.nil_append] at this
  rw [this, dL, blk_nil, List.reverse_replicate, val_zeros, h0]

theorem dR_append (tab : List ℕ) (k : ℕ) (b t : List ℕ) (hb : b.length = k) :
    dR tab k (b ++ t) = tab.getD (val b) 0 := by
  rw [dR, blk_append k b t hb]

theorem dL_rev_append (tab : List ℕ) (k : ℕ) (b t : List ℕ) (hb : b.length = k) :
    dL tab k (b.reverse ++ t) = tab.getD (val b) 0 := by
  rw [dL, blk_append k b.reverse t (by simp [hb]), List.reverse_reverse]

/-! ### Decoding in blocks -/

theorem decK_nil (k : ℕ) (d : List ℕ → ℕ) : decK k d [] = [] := rfl

section Dec
variable (k : ℕ) (hk : 0 < k) (d : List ℕ → ℕ)
include hk

theorem unf_fuel : ∀ (f f' : ℕ) (l : List ℕ), l.length ≤ f → l.length ≤ f' →
    ComputableDec.unf (fun l : List ℕ => l.isEmpty) d (fun l => l.drop k) f l =
      ComputableDec.unf (fun l : List ℕ => l.isEmpty) d (fun l => l.drop k) f' l
  | f, f', [], _, _ => by rw [unf_nil, unf_nil]
  | 0, _, _ :: _, h, _ => absurd h (by simp)
  | _ + 1, 0, _ :: _, _, h => absurd h (by simp)
  | f + 1, f' + 1, a :: l, h, h' => by
    simp only [ComputableDec.unf, List.isEmpty_cons, cond_false]
    congr 1
    exact unf_fuel f f' _ (by simp only [List.length_drop, List.length_cons] at h ⊢; omega)
      (by simp only [List.length_drop, List.length_cons] at h' ⊢; omega)

theorem decK_cons (l : List ℕ) (hl : l ≠ []) : decK k d l = d l :: decK k d (l.drop k) := by
  obtain ⟨a, t, rfl⟩ := List.exists_cons_of_ne_nil hl
  show ComputableDec.unf _ d _ (t.length + 1) (a :: t) = _
  simp only [ComputableDec.unf, List.isEmpty_cons, cond_false]
  congr 1
  exact unf_fuel k hk d _ _ _ (by simp only [List.length_drop, List.length_cons]; omega) le_rfl

theorem decK_append (b t : List ℕ) (hb : b.length = k) :
    decK k d (b ++ t) = d (b ++ t) :: decK k d t := by
  rw [decK_cons k hk d _ (List.ne_nil_of_length_pos (by simp; omega)), List.drop_left' hb]

/-- **Decoding the blocks of a list of symbol numbers.** -/
theorem decK_flatMap (c : ℕ → List ℕ) (hc : ∀ a, (c a).length = k) :
    ∀ (Z : List ℕ), (∀ a ∈ Z, ∀ t, d (c a ++ t) = a) → decK k d (Z.flatMap c) = Z
  | [], _ => rfl
  | a :: Z, hZ => by
    rw [List.flatMap_cons, decK_append k hk d _ _ (hc a), hZ a (by simp),
      decK_flatMap c hc Z fun b hb => hZ b (by simp [hb])]

theorem decK_zeros (hz : ∀ j, d (List.replicate j 0) = 0) :
    ∀ j, ∃ j', decK k d (List.replicate j 0) = List.replicate j' 0 := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · exact ⟨0, rfl⟩
    · rw [decK_cons k hk d _ (List.ne_nil_of_length_pos (by simpa using hj)), hz,
        List.drop_replicate]
      obtain ⟨j', h⟩ := ih (j - k) (by omega)
      exact ⟨j' + 1, by rw [h, List.replicate_succ]⟩

/-- **Trailing blanks decode to trailing blanks.** -/
theorem decK_pad (hpad : ∀ l j, d (l ++ List.replicate j 0) = d l)
    (hz : ∀ j, d (List.replicate j 0) = 0) :
    ∀ (n : ℕ) (l : List ℕ), l.length = n → ∀ j, ∃ j',
      decK k d (l ++ List.replicate j 0) = decK k d l ++ List.replicate j' 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro l hn j
    rcases l with _ | ⟨a, t⟩
    · obtain ⟨j', h⟩ := decK_zeros k hk d hz j
      exact ⟨j', by simpa [decK_nil] using h⟩
    · rw [decK_cons k hk d ((a :: t) ++ List.replicate j 0) (by simp),
        decK_cons k hk d (a :: t) (by simp), hpad,
        List.drop_append, List.drop_replicate]
      obtain ⟨j', h⟩ := ih ((a :: t).drop k).length
        (by simp only [List.length_drop, List.length_cons] at hn ⊢; omega) _ rfl
        (j - (k - (a :: t).length))
      exact ⟨j', by rw [h, List.cons_append]⟩

end Dec

/-! ### Moving the head to the start of its block, and fixing the head block -/

/-- Move the head back `δ` cells: the first `δ` cells of the left list (the cells next to the
    head, missing cells blank) go to the front of the right list. -/
def realign (δ : ℕ) (l r : List ℕ) : List ℕ × List ℕ := (l.drop δ, (blk δ l).reverse ++ r)

/-- Replace the block of `k` cells at the head by `b`. -/
def fixH (k : ℕ) (b r : List ℕ) : List ℕ := b ++ r.drop k

theorem drop_pad (n : ℕ) (l : List ℕ) (j : ℕ) :
    (l ++ List.replicate j 0).drop n = l.drop n ++ List.replicate (j - (n - l.length)) 0 := by
  rw [List.drop_append, List.drop_replicate]

/-- **Realigning a window**: moving the head of the window at `n + δ` back by `δ` cells gives the
    window at `n`. -/
theorem realign_window (δ n s : ℕ) (X : List ℕ) (h : n + δ ≤ X.length) :
    realign δ (window s X (n + δ)).2.1 (window s X (n + δ)).2.2 =
      ((window s X n).2.1, (window s X n).2.2) := by
  have hlen : ((X.drop n).take δ).reverse.length = δ := by simp; omega
  have e : (X.take (n + δ)).reverse = ((X.drop n).take δ).reverse ++ (X.take n).reverse := by
    rw [List.take_add, List.reverse_append]
  simp only [realign, window, e]
  refine Prod.ext (List.drop_left' hlen) ?_
  simp only
  have hd : X.drop (n + δ) = (X.drop n).drop δ := by simp [List.drop_drop, Nat.add_comm]
  rw [blk_take δ _ (by simp; omega), List.take_left' hlen, List.reverse_reverse, hd,
    List.take_append_drop]

/-! ### The readout -/

section Read
variable {α : Type}

/-- **Readout** of a symbol reduction, with the base readout `R`. -/
def readFS (R : Spec.Code → Option α) (k : ℕ) (tab : List ℕ) (off : ℕ → ℕ) (fx : ℕ → List ℕ)
    (stm : ℕ → ℕ) (g : Spec.Code) : Option α :=
  R (stm g.1, decK k (dL tab k) (realign (off g.1) g.2.1 g.2.2).1,
    decK k (dR tab k) (fixH k (fx g.1) (realign (off g.1) g.2.1 g.2.2).2))

theorem padL_of_toID {R : Spec.Code → Option α}
    (hR : ∀ p g g', Spec.toID p g = Spec.toID p g' → R g = R g') (s : ℕ) (l r : List ℕ) (j : ℕ) :
    R (s, l ++ List.replicate j 0, r) = R (s, l, r) :=
  hR 0 _ _ (by simpa using Spec.CodePad.toID_pad 0 s l r j 0)

theorem padR_of_toID {R : Spec.Code → Option α}
    (hR : ∀ p g g', Spec.toID p g = Spec.toID p g' → R g = R g') (s : ℕ) (l r : List ℕ) (j : ℕ) :
    R (s, l, r ++ List.replicate j 0) = R (s, l, r) :=
  hR 0 _ _ (by simpa using Spec.CodePad.toID_pad 0 s l r 0 j)

/-- **The readout depends only on the ID**, not on the code chosen for it. -/
theorem readFS_toID (R : Spec.Code → Option α)
    (hR : ∀ p g g', Spec.toID p g = Spec.toID p g' → R g = R g') (k : ℕ) (hk : 0 < k)
    (tab : List ℕ) (h0 : tab.getD 0 0 = 0) (off : ℕ → ℕ) (fx : ℕ → List ℕ) (stm : ℕ → ℕ)
    {p : ℤ} {g g' : Spec.Code} (h : Spec.toID p g = Spec.toID p g') :
    readFS R k tab off fx stm g = readFS R k tab off fx stm g' := by
  have keyL : ∀ a X J b, R (a, decK k (dL tab k) (X ++ List.replicate J 0), b) =
      R (a, decK k (dL tab k) X, b) := by
    intro a X J b
    obtain ⟨j', hj⟩ := decK_pad k hk (dL tab k) (dL_pad tab k) (dL_zeros tab h0 k) _ X rfl J
    rw [hj, padL_of_toID hR]
  have keyR : ∀ a b X J, R (a, b, decK k (dR tab k) (X ++ List.replicate J 0)) =
      R (a, b, decK k (dR tab k) X) := by
    intro a b X J
    obtain ⟨j', hj⟩ := decK_pad k hk (dR tab k) (dR_pad tab k) (dR_zeros tab h0 k) _ X rfl J
    rw [hj, padR_of_toID hR]
  refine ReadGen.read_toID2 (fun s l r => readFS R k tab off fx stm (s, l, r)) ?_ ?_ h
  · intro s j l r
    simp only [readFS, realign, blk_pad, drop_pad]
    exact keyL _ _ _ _
  · intro s j l r
    simp only [readFS, realign, fixH, ← List.append_assoc, drop_pad]
    exact keyR _ _ _ _

open Primrec in
theorem blk_primrec : Primrec₂ blk :=
  (list_map (list_range.comp fst) ((list_getD 0).comp (snd.comp fst) snd).to₂).to₂

open Primrec in
theorem val_primrec : Primrec val :=
  (list_foldl .id (const 0)
    (nat_add.comp (nat_mul.comp (const 2) (fst.comp snd)) (snd.comp snd)).to₂).of_eq
    fun _ => rfl

open Primrec in
theorem dR_primrec (tab : List ℕ) (k : ℕ) : Primrec (dR tab k) :=
  (list_getD 0).comp (const tab) (val_primrec.comp (blk_primrec.comp (const k) .id))

open Primrec in
theorem dL_primrec (tab : List ℕ) (k : ℕ) : Primrec (dL tab k) :=
  (list_getD 0).comp (const tab)
    (val_primrec.comp (list_reverse.comp (blk_primrec.comp (const k) .id)))

open Primrec in
theorem decK_primrec (k : ℕ) (d : List ℕ → ℕ) (hd : Primrec d) : Primrec (decK k d) :=
  (ComputableDec.unf_primrec (α := List ℕ) (ComputableDec.list_isEmpty.comp snd).to₂
    (hd.comp snd).to₂ (list_drop.comp (const k) snd).to₂ list_length .id).of_eq fun _ => rfl

open Primrec in
theorem readFS_primrec [Primcodable α] (R : Spec.Code → Option α) (hR : Primrec R) (k : ℕ) (tab : List ℕ)
    (off : ℕ → ℕ) (fx : ℕ → List ℕ) (stm : ℕ → ℕ) (hoff : Primrec off) (hfx : Primrec fx)
    (hstm : Primrec stm) : Primrec (readFS R k tab off fx stm) := by
  have ho : Primrec fun g : Spec.Code => off g.1 := hoff.comp fst
  have hl : Primrec fun g : Spec.Code => g.2.1 := fst.comp snd
  have hr : Primrec fun g : Spec.Code => g.2.2 := snd.comp snd
  have h1 : Primrec fun g : Spec.Code => (realign (off g.1) g.2.1 g.2.2).1 :=
    list_drop.comp ho hl
  have h2 : Primrec fun g : Spec.Code => (realign (off g.1) g.2.1 g.2.2).2 :=
    list_append.comp (list_reverse.comp (blk_primrec.comp ho hl)) hr
  have h3 : Primrec fun g : Spec.Code => fixH k (fx g.1) (realign (off g.1) g.2.1 g.2.2).2 :=
    list_append.comp (hfx.comp fst) (list_drop.comp (const k) h2)
  exact hR.comp (pair (hstm.comp fst) (pair ((decK_primrec k _ (dL_primrec tab k)).comp h1)
    ((decK_primrec k _ (dR_primrec tab k)).comp h3)))

end Read

/-! ### The encoder -/

/-- **Encoder** (list level): every cell of the base code `z` becomes its block (the left list,
    read to the left, reversed blocks), in the state `q`. -/
def encFS (c : ℕ → List ℕ) (q : ℕ) (z : Spec.Code) : Spec.Code :=
  (q, z.2.1.flatMap fun a => (c a).reverse, z.2.2.flatMap c)

open Primrec in
theorem encFS_primrec (c : ℕ → List ℕ) (hc : Primrec c) (q : ℕ) : Primrec (encFS c q) :=
  pair (const q) (pair
    (list_flatMap (fst.comp snd) ((list_reverse.comp hc).comp snd).to₂)
    (list_flatMap (snd.comp snd) (hc.comp snd).to₂))

theorem length_flatMap_k {β γ : Type} (c : β → List γ) (k : ℕ) (hc : ∀ a, (c a).length = k)
    (L : List β) : (L.flatMap c).length = k * L.length := by
  induction L with
  | nil => simp
  | cons a L ih => rw [List.flatMap_cons, List.length_append, ih, hc, List.length_cons, Nat.mul_succ]; omega

/-- The blocks of a window are the window of the blocks. -/
theorem encFS_window (c : ℕ → List ℕ) (k : ℕ) (hc : ∀ a, (c a).length = k) (q s : ℕ)
    (Y : List ℕ) (p : ℕ) : encFS c q (window s Y p) = window q (Y.flatMap c) (k * p) := by
  simp only [encFS, window, take_flatMap_block c k hc, drop_flatMap_block c k hc,
    List.reverse_flatMap]
  rfl

/-! ### The final configuration -/

theorem tp_upd_mid {S : Type} (bk : S) (A B : List S) (x y : S) :
    URTM.KState.upd (Sim.tp bk (A ++ x :: B)) (A.length : ℤ) y = Sim.tp bk (A ++ y :: B) := by
  funext i
  simp only [URTM.KState.upd]
  split_ifs with h
  · subst h
    exact (Sim.tp_at A B y).symm
  · cases i with
    | negSucc => rfl
    | ofNat j =>
      have hj : j ≠ A.length := fun e => h (by rw [e]; rfl)
      simp only [Sim.tp, List.getD_eq_getElem?_getD]
      rcases Nat.lt_or_gt_of_ne hj with hlt | hgt
      · rw [List.getElem?_append_left hlt, List.getElem?_append_left hlt]
      · rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega)]
        obtain ⟨m, hm⟩ : ∃ m, j - A.length = m + 1 := ⟨j - A.length - 1, by omega⟩
        rw [hm]
        rfl

/-- **The readout on a final configuration**: the head `δ` cells into the block of `a'`, the
    head block to be read as `a`. -/
theorem readFS_fin {α : Type} (R : Spec.Code → Option α) (k : ℕ) (hk : 0 < k) (tab : List ℕ)
    (off : ℕ → ℕ) (fx : ℕ → List ℕ) (stm : ℕ → ℕ) (c : ℕ → List ℕ)
    (hc : ∀ a, (c a).length = k) (q δ : ℕ) (hδ : δ ≤ k) (A B : List ℕ) (a a' : ℕ)
    (hoff : off q = δ) (hfx : fx q = c a)
    (hv : ∀ x ∈ A ++ a :: B, tab.getD (val (c x)) 0 = x) :
    readFS R k tab off fx stm (window q ((A ++ a' :: B).flatMap c) (k * A.length + δ)) =
      R (stm q, A.reverse, a :: B) := by
  have hX : ((A ++ a' :: B).flatMap c).length = k * A.length + k + k * B.length := by
    rw [length_flatMap_k c k hc]; simp only [List.length_append, List.length_cons]; ring
  have hAk : (A.flatMap c).length = k * A.length := length_flatMap_k c k hc A
  simp only [readFS, window_st, hoff, hfx]
  rw [realign_window δ (k * A.length) q _ (by omega)]
  simp only [window, List.flatMap_append, List.flatMap_cons, fixH]
  rw [List.take_left' hAk, List.drop_left' hAk, List.drop_left' (hc a'), List.reverse_flatMap,
    show c a ++ B.flatMap c = (a :: B).flatMap c by rw [List.flatMap_cons],
    decK_flatMap k hk (dR tab k) c hc (a :: B) fun x hx t => by
      rw [dR_append tab k _ _ (hc x)]; exact hv x (by simp at hx ⊢; tauto),
    decK_flatMap k hk (dL tab k) (List.reverse ∘ c) (fun x => by simp [hc]) A.reverse
      fun x hx t => by
        show dL tab k ((c x).reverse ++ t) = x
        rw [dL_rev_append tab k _ _ (hc x)]; exact hv x (by simp at hx ⊢; tauto)]

/-! ### The main theorem -/

section Main
variable {Q P S : Type}

/-- The state numbers of a 2-symbol machine with states `ℕ`: `go n ↦ n + 2`, the pseudo-states by
    `pn` (into `{0, 1}`). -/
def stFS (pn : P → ℕ) : Tgt ℕ P → ℕ
  | .go n => n + 2
  | .halt h => pn h

/-- The numbering of a 2-symbol machine: `stFS pn`, bits `false, true ↦ 0, 1`. -/
def numFS (pn : P → ℕ) (hpn : Function.Injective pn) (hlt : ∀ h, pn h < 2) : Numbering ℕ P Bool where
  st := stFS pn
  sym b := if b then 1 else 0
  st_inj := by
    intro a b h
    rcases a with a | a <;> rcases b with b | b <;> simp only [stFS] at h
    · rw [show a = b by omega]
    · have := hlt b; omega
    · have := hlt a; omega
    · rw [hpn h]
  sym_inj := by
    intro a b h
    cases a <;> cases b <;> simp_all

theorem flatMap_code (Nsym : S → ℕ) (code : S → List Bool) (sym : Bool → ℕ) (c : ℕ → List ℕ)
    (hcode : ∀ s, (code s).map sym = c (Nsym s)) (L : List S) :
    (L.flatMap code).map sym = (L.map Nsym).flatMap c := by
  rw [List.map_flatMap, List.flatMap_map]
  exact List.flatMap_congr fun s _ => hcode s

/-- **A base final configuration in the split form** `A · (hs h) · B`, head on `hs h`, from the
    window form (`p ≤ |L|`, as `BlockGen.readM_fin` gives it) and the head symbol. -/
theorem fin_split (N : Numbering Q P S) (bk : S) (hbk : N.sym bk = 0) {α : Type}
    (R : Spec.Code → Option α) (hR : ∀ p g g', Spec.toID p g = Spec.toID p g' → R g = R g')
    (h : P) (x : S) (st : ℕ) (L : List S) (p : ℕ) (hp : p ≤ L.length)
    (hx : Sim.tp bk L (p : ℤ) = x) (v : α) (hv : R (window st (L.map N.sym) p) = some v) :
    ∃ (A B : List S), (⟨.halt h, (p : ℤ), Sim.tp bk L⟩ : Cfg Q P S) =
      ⟨.halt h, (A.length : ℤ), Sim.tp bk (A ++ x :: B)⟩ ∧
      R (st, (A.map N.sym).reverse, N.sym x :: B.map N.sym) = some v := by
  rcases Nat.lt_or_ge p L.length with hlt | hge
  · have hx' : L[p] = x := by
      rw [Sim.tp_ofNat, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt] at hx
      exact hx
    have hL : L = L.take p ++ x :: L.drop (p + 1) := by
      rw [← hx', ← List.drop_eq_getElem_cons hlt, List.take_append_drop]
    refine ⟨L.take p, L.drop (p + 1), ?_, ?_⟩
    · rw [← hL, List.length_take, Nat.min_eq_left hp]
    · rw [← hv]
      have e2 : (L.map N.sym).drop p = N.sym x :: (L.drop (p + 1)).map N.sym := by
        rw [List.drop_eq_getElem_cons (i := p) (l := L.map N.sym) (by simpa using hlt),
          List.getElem_map, hx', List.map_drop]
      simp only [window, e2, List.map_take]
  · have hpl : p = L.length := by omega
    subst hpl
    have hx' : x = bk := by
      rw [Sim.tp_ofNat, List.getD_eq_default _ _ (Nat.le_refl _)] at hx
      exact hx.symm
    subst hx'
    refine ⟨L, [], ?_, ?_⟩
    · rw [CTSH.Sim.tp_trail]
    · rw [← hv, hbk]
      simp only [window, List.map_nil, List.take_of_length_le (by simp : (L.map N.sym).length ≤ L.length),
        List.drop_of_length_le (by simp : (L.map N.sym).length ≤ L.length)]
      simpa using padR_of_toID hR st (L.map N.sym).reverse [] 1

/-! #### Bases of Morita's one-cell-per-letter family ((13,7), (15,6), (17,5), (24,4)) -/

/-- The initial configurations of a base of Morita's family are the windows of `MoritaGen.encM`. -/
theorem morita_hinit (N : Numbering Q P S) (lo : Ch → S) (st bk x : S) (q0 : Q)
    (hbk : N.sym bk = 0) (hlo : ∀ c, N.sym (lo c) = U10_8.loN c)
    (encC : CTSH → List Ch → Cfg Q P S)
    (henc : ∀ C w, encC C w = ⟨.go q0, (((Sim.RA lo st bk C 0).length + 2 : ℕ) : ℤ),
      Sim.tp bk (bk :: Sim.RA lo st bk C 0 ++ x :: w.map lo)⟩) (C : CTSH) (w : List Ch) :
    ∃ (L0 : List S) (P0 : ℕ), P0 ≤ L0.length ∧ encC C w = ⟨.go q0, (P0 : ℤ), Sim.tp bk L0⟩ ∧
      MoritaGen.encM (N.st (.go q0)) (N.sym x) (N.sym st) C w =
        window (N.st (.go q0)) (L0.map N.sym) P0 :=
  ⟨_, _, by simp, henc C w, U85_2.encM_window N lo st bk hbk hlo q0 x C w⟩

/-- The final configurations of a base of Morita's family in the split form, read by
    `MoritaGen.readM` (from `BlockGen.readM_fin`), given the symbol under the head. -/
theorem morita_hfinB [DecidableEq S] (N : Numbering Q P S) (lo : Ch → S) (st bk : S)
    (hnull hhalt : P) (e : ℕ) (hbk : N.sym bk = 0) (hlo : ∀ c, N.sym (lo c) = U10_8.loN c)
    (hls : ∀ c, lo c ≠ st) (hst0 : N.sym st ≠ 0) (stn : P → ℕ) (hnh : stn hnull ≠ stn hhalt)
    (finC : CTSH → List Ch → ℕ → List Ch → Cfg Q P S)
    (hnullfin : ∀ C mf rm, mf ≤ C.length → ∃ (L : List S) (p : ℕ), p ≤ L.length ∧
      finC C [] mf rm = ⟨.halt hnull, p, Sim.tp bk L⟩ ∧ L.count st = C.length)
    (hhaltfin : ∀ C v rm, ∃ (A : List S) (mk : S) (p : ℕ), p ≤ (A ++ mk :: v.map lo).length ∧
      finC C (.Y :: v) 0 rm = ⟨.halt hhalt, p, Sim.tp bk (A ++ mk :: v.map lo)⟩ ∧
      (A ++ [mk]).count st - e = C.length ∧ N.sym mk ≠ 0 ∧ N.sym mk ≠ 1 ∧ N.sym mk ≠ 2)
    (hs : P → S)
    (hhead : ∀ C vf mf rm, Halting C (vf, mf) → ∃ h, (finC C vf mf rm).st = .halt h ∧
      (finC C vf mf rm).tape (finC C vf mf rm).pos = hs h)
    (C : CTSH) (vf : List Ch) (mf : ℕ) (rm : List Ch) (hf : Halting C (vf, mf)) :
    ∃ (h : P) (A B : List S),
      finC C vf mf rm = ⟨.halt h, (A.length : ℤ), Sim.tp bk (A ++ hs h :: B)⟩ ∧
      MoritaGen.readM (stn hhalt) (N.sym st) e (stn h, (A.map N.sym).reverse,
        N.sym (hs h) :: B.map N.sym) = some (C.length, vf.map U10_8.loN) := by
  obtain ⟨h, L, p, hp, hfin, hrd⟩ := BlockGen.readM_fin N lo st bk hnull hhalt e hlo hls stn hnh
    finC hnullfin hhaltfin C vf mf rm hf
  obtain ⟨h', hst, htp⟩ := hhead C vf mf rm hf
  rw [hfin] at hst htp
  obtain rfl : h = h' := by injection hst
  obtain ⟨A, B, h1, h2⟩ := fin_split N bk hbk (MoritaGen.readM (stn hhalt) (N.sym st) e)
    (fun _ _ _ hg => MoritaGen.readM_toID _ _ _ hst0 hg) h (hs h) (stn h) L p hp htp _ hrd
  exact ⟨h, A, B, hfin.trans h1, h2⟩

/-- **A symbol reduction of a base machine with a computable encoder and readout is a UTM in the
    strict sense of Morita Def. 7.1.** The base: its initial configurations are the windows of the
    encoder `encB` (`hinit`), and its final configurations are read by `R` (`hfinB`, head on the
    symbol `hs h` that the halting quintuple of `h` reads). The reduction: the simulation of
    `FewSym.fs_simulates` (`hsim`), the numbering `num` (bits `0, 1`), the numeric code `c` and
    the table `tab` that decodes it, and the runs inside the head block where `T` halts
    (`hrunH`, by `decide`) with the readout data `off`, `fx`, `stm` for their final states. -/
theorem isUTMStrict_fewsym
    (N : Numbering Q P S) (bk : S) (q0 : Q)
    (encC : CTSH → List Ch → Cfg Q P S) (finC : CTSH → List Ch → ℕ → List Ch → Cfg Q P S)
    (encB : CTSH → List Ch → Spec.Code) (hencB : Primrec₂ encB)
    (hinit : ∀ C w, ∃ (L0 : List S) (P0 : ℕ), P0 ≤ L0.length ∧
      encC C w = ⟨.go q0, (P0 : ℤ), Sim.tp bk L0⟩ ∧
      encB C w = window (N.st (.go q0)) (L0.map N.sym) P0)
    (R : Spec.Code → Option (ℕ × List ℕ)) (hR : Primrec R)
    (hRinv : ∀ p g g', Spec.toID p g = Spec.toID p g' → R g = R g')
    (hs : P → S) (stn : P → ℕ)
    (hfinB : ∀ C vf mf rm, Halting C (vf, mf) → ∃ (h : P) (A B : List S),
      finC C vf mf rm = ⟨.halt h, (A.length : ℤ), Sim.tp bk (A ++ hs h :: B)⟩ ∧
      R (stn h, (A.map N.sym).reverse, N.sym (hs h) :: B.map N.sym) =
        some (C.length, vf.map U10_8.loN))
    (M : Machine ℕ P Bool) (E : Enc Q S ℕ) (f : P → Q) (num : Numbering ℕ P Bool)
    (hn0 : num.sym false = 0)
    (hk : 0 < E.k) (hlen : ∀ s, (E.code s).length = E.k)
    (hbkc : ∀ i, (E.code bk).getD i false = false) (hce : E.ce q0 = 0)
    (hsim : ∀ C w,
      (∀ n vf mf, CHaltsIn C n (w, 0) (vf, mf) → ∃ N' rm, n ≤ N' + 1 ∧
        HaltsIn M N' (enc E (encC C w)) (pre M E (SimLemmas.unhalt f (finC C vf mf rm)))) ∧
      ((∀ n e, ¬ CHaltsIn C n (w, 0) e) ↔ ∀ N' e, ¬ HaltsIn M N' (enc E (encC C w)) e))
    (c : ℕ → List ℕ) (hcP : Primrec c) (hc : ∀ a, (c a).length = E.k)
    (hcode : ∀ s, (E.code s).map num.sym = c (N.sym s)) (hc01 : ∀ a, ∀ b ∈ c a, b = 0 ∨ b = 1)
    (tab : List ℕ) (htab0 : tab.getD 0 0 = 0)
    (htab : ∀ s, tab.getD (val (c (N.sym s))) 0 = N.sym s)
    (fs : P → ℕ) (dd : P → ℕ) (ws : P → S) (hdd : ∀ h, dd h ≤ E.k)
    (hrunH : ∀ h, hrun M (hfuel E) ⟨E.ρ (f h), E.ce (f h), E.code (hs h)⟩ =
      some ⟨fs h, dd h, E.code (ws h)⟩)
    (off : ℕ → ℕ) (fx : ℕ → List ℕ) (stm : ℕ → ℕ) (hoff : Primrec off) (hfx : Primrec fx)
    (hstm : Primrec stm) (hoffH : ∀ h, off (num.st (.go (fs h))) = dd h)
    (hfxH : ∀ h, fx (num.st (.go (fs h))) = c (N.sym (hs h)))
    (hstmH : ∀ h, stm (num.st (.go (fs h))) = stn h)
    (hq0 : num.st (.go (E.ρ q0)) ∈ Spec.states (numT num M))
    (h1 : 1 ∈ Spec.symbols (numT num M)) :
    Spec.IsUTMStrict (numT num M) := by
  have hflat := flatMap_code N.sym E.code num.sym c hcode
  refine ChainGen.isUTMStrict_of_ctsh (numT num M)
    (fun C w => encFS c (num.st (.go (E.ρ q0))) (encB C w)) (readFS R E.k tab off fx stm)
    ((encFS_primrec c hcP _).comp₂ hencB) (readFS_primrec R hR E.k tab off fx stm hoff hfx hstm)
    (fun C w => ?_) (fun C w => ?_) (fun _ _ _ h => readFS_toID R hRinv E.k hk tab htab0 off fx stm h)
  · -- the encoded initial ID is an ID of the table
    refine isIDOf_toID _ 0 _ hq0 fun a ha => ?_
    simp only [encFS, List.mem_append, List.mem_flatMap, List.mem_reverse] at ha
    rcases ha with ⟨b, -, hb⟩ | ⟨b, -, hb⟩ <;> rcases hc01 b a hb with rfl | rfl <;>
      first | exact .inl rfl | exact .inr h1
  · obtain ⟨L0, P0, hP0, hencC, hencB'⟩ := hinit C w
    -- the encoded initial configuration, on a list tape of bits
    have hE0 : enc E (encC C w) =
        ⟨.go (E.ρ q0), ((E.k * P0 : ℕ) : ℤ), Sim.tp false (L0.flatMap E.code)⟩ := by
      rw [hencC]
      simp only [enc, hce, bits_tp E.code E.k hk hlen bk hbkc, Nat.cast_zero, add_zero, Nat.cast_mul]
    have e : Spec.toID 0 (encFS c (num.st (.go (E.ρ q0))) (encB C w)) =
        numCfg num ((E.k * P0 : ℕ) : ℤ) (enc E (encC C w)) := by
      rw [hE0, numCfg_tp (N := num) false hn0 ((E.k * P0 : ℕ) : ℤ) (.go (E.ρ q0))
        (L0.flatMap E.code) (E.k * P0)
        (by rw [length_flatMap_k E.code E.k hlen]; exact Nat.mul_le_mul_left _ hP0),
        sub_self, hflat, hencB', encFS_window c E.k hc]
    rw [e]
    obtain ⟨hF, hN⟩ := hsim C w
    refine runSim_of_sim num M _ C w (enc E (encC C w))
      (fun y cfg => ∃ rm, cfg = pre M E (SimLemmas.unhalt f (finC C y.1 y.2 rm))) _
      (fun n y hy => ?_) (fun hn => hN.mp hn) (fun y cfg hy hc' => ?_)
    · obtain ⟨N', rm, -, h⟩ := hF n y.1 y.2 hy
      exact ⟨N', _, h, rm, rfl⟩
    · obtain ⟨rm, rfl⟩ := hc'
      obtain ⟨vf, mf⟩ := y
      obtain ⟨h, A, B, hfin, hrd⟩ := hfinB C vf mf rm hy
      -- the run inside the head block
      have hb : Sim.tp bk (A ++ hs h :: B) (A.length : ℤ) = hs h := Sim.tp_at A B (hs h)
      have efin : pre M E (SimLemmas.unhalt f (finC C vf mf rm)) =
          ⟨.go (fs h), ((E.k * A.length + dd h : ℕ) : ℤ),
            Sim.tp false ((A ++ ws h :: B).flatMap E.code)⟩ := by
        rw [hfin]
        have hu : SimLemmas.unhalt f (⟨.halt h, (A.length : ℤ), Sim.tp bk (A ++ hs h :: B)⟩ :
            Cfg Q P S) = ⟨.go (f h), (A.length : ℤ), Sim.tp bk (A ++ hs h :: B)⟩ := rfl
        rw [hu]
        simp only [pre, hb, hrunH h, glob]
        rw [ovl_block hk hlen, tp_upd_mid, bits_tp E.code E.k hk hlen bk hbkc]
        simp only [Nat.cast_add, Nat.cast_mul]
      rw [efin]
      refine read_of_tp num false hn0 _ _ _ _ ?_ _ _ ?_
      · rw [length_flatMap_k E.code E.k hlen]
        simp only [List.length_append, List.length_cons]
        have h2 : E.k * (A.length + 1) ≤ E.k * (A.length + (B.length + 1)) :=
          Nat.mul_le_mul_left _ (by omega)
        rw [Nat.mul_add, Nat.mul_one] at h2
        have := hdd h
        omega
      · have hlenA : A.length = (A.map N.sym).length := by simp
        rw [hflat, List.map_append, List.map_cons, hlenA,
          readFS_fin R E.k hk tab off fx stm c hc _ (dd h) (hdd h) (A.map N.sym) (B.map N.sym)
            (N.sym (hs h)) (N.sym (ws h)) (hoffH h) (hfxH h) (fun x hx => ?_), hstmH h]
        · exact hrd
        · simp only [List.mem_append, List.mem_map, List.mem_cons] at hx
          rcases hx with ⟨s, -, rfl⟩ | rfl | ⟨s, -, rfl⟩ <;> exact htab _

end Main

end URTM.Univ.FewSymGen
