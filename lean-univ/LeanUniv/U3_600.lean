/-
  **URTM(3,600): encoder, readout, and universality in the sense of Def. 7.1** (docs/24 P7d).

  The machine (`Num3_600.lean`) is the improved 3-state conversion of docs/09, mirrored, applied
  to Morita's (32,3) without its halting quintuples. A (32,3) configuration is packed into a
  window of plain cells `pl (pl s)`; the window grows by two cells and shifts by one per
  simulated step, so the final configuration depends on the number `N` of steps
  (`CTSH3_600Main.fin600 … N`).

  * `encList C w`: the Spec code of the encoded initial configuration `E600 C w`, computed from
    the (32,3) initial code: state `L`, head on the blank right of the window; left of the head
    the (32,3) tape with the mark `mk begin s` on the (32,3) head cell (`encList_eq`).
  * Final configurations (`Ffin`, `fin600_Ffin`): state `R0`; the head cell
    is a counter symbol `ct x k`, where `x` shows the (32,3) head cell and `k` (the index of a
    state of the intermediate machine) carries the cell right of it; left of the head are the
    (32,3) cells as they are, right of the head the (32,3) cells shifted by one; padding cells
    `pl (pl b)` and blanks `pl bl` surround them, their number depending on `N`
    (`Ffin_left`, `Ffin_right`, `Ffin_supp`).
  * `readU g`: recover the (32,3) window around the head (`rec3`; padding and blanks both become
    the blank of (32,3)) and apply the (32,3) readout `U32_3.readL`; the kind of the head cell
    tells `halt` from `null`. It reads only the ID: no `N`, `C`, `w` (`readU_toID`,
    `readU_primrec`, `readU_of_shape`).
  * `isUTMStrict_U`: `IsUTMStrict U` by `ChainGen.isUTMStrict_of_ctsh`.
-/
import LeanUniv.Num3_600
import LeanUniv.ReadGen

namespace URTM.Univ.U3_600
open URTM URTM.CTSH URTM.Gen.K32_3 URTM.Gen.T3_600 URTM.Univ.KToSpec URTM.Univ.NumGen
open URTM.Univ.ReadGen
open URTM.KState (Tgt Cfg Machine HaltsIn upd)
open URTM.SimLemmas (unhalt)
open URTM.Conv3Base (flipC)
open URTM.Conv1W (VSt VSym isPlus)
open URTM.Conv3P (CSym)
open URTM.Conv510 (TSt)
open URTM.CTSH.U3_600 (E600 fin600 f32 a0 n0 len32 inv0 q0_minus len32_eq
  urtm3_600_simulates_ctsh)
open URTM.CTSH.U32_3 (nm32 encC32 finCfg32)
open URTM.Univ.U10_8 (loN)
open URTM.Conv59 (mix mix_lt mix_ge)
open URTM.Conv55 (upd_eq upd_ne)

/-! ### The list-level encoder -/

/-- The (3,600) initial code from the (32,3) initial code `z = (_, l, r)`: state `L = 0`, the
    head on the blank right of the window; left of the head, nearest first, the cells of the
    (32,3) tape from two cells beyond its right end down to one cell beyond its left end, each
    as `pl (pl s) ↦ 1 + s`, except the (32,3) head cell, which carries the mark
    `pl (mk begin s) ↦ 4 + s`. -/
def enc3 (z : Spec.Code) : Spec.Code :=
  (0, (List.range (z.2.1.length + z.2.2.length + 3)).map (fun t =>
        if t = z.2.2.length + 1 then 4 + z.2.2.getD 0 0
        else 1 + (if t ≤ z.2.2.length then z.2.2.getD (z.2.2.length + 1 - t) 0
                  else z.2.1.getD (t - z.2.2.length - 2) 0)), [])

/-- **Encoder** (list level). -/
def encList (C : CTSH) (w : List Ch) : Spec.Code := enc3 (U32_3.encList C w)

theorem qN_q0 : qN St.q0 = 0 := by decide

/-- The encoded initial configuration, unfolded. -/
theorem E600_eq (C : CTSH) (w : List Ch) :
    E600 C w = ⟨.go .L, 0, fun i => .pl (Conv1W.packV TR (a0 C w) (n0 C w) St.q0
      (-(encC32 C w).pos) (fun j => (encC32 C w).tape (-j)) (-i))⟩ := by
  have hst : (encC32 C w).st = .go St.q0 := rfl
  simp only [E600, Conv3S.encM, Conv3S.enc, Conv1W.Wc, flipC, hst, Conv1W.encV, Conv3P.enc]
  simp
  rfl

theorem encList_left_length (C : CTSH) (w : List Ch) :
    (U32_3.encList C w).2.1.length = (URTM.CTSH.U32_3.RA nm32 C 0).length + 2 := by
  have h := congrArg List.length (U32_3.Hi_zero_rev C)
  simp only [List.length_reverse, List.length_map] at h
  simp [U32_3.encList, U32_3.RA_zero, ← h]

theorem encList_right_length (C : CTSH) (w : List Ch) :
    (U32_3.encList C w).2.2.length = w.length := by
  simp [U32_3.encList]

/-- The (32,3) initial code describes the (32,3) initial tape relative to its head. -/
theorem enc32_tape (C : CTSH) (w : List Ch) (y : ℤ) :
    sN ((encC32 C w).tape (y + (encC32 C w).pos)) = (Spec.toID 0 (U32_3.encList C w)).tape y := by
  have h := congrFun (congrArg Spec.ID.tape (U32_3.encList_eq C w)) y
  have hp : (encC32 C w).pos = U32_3.δ C := by
    have := congrArg Spec.ID.pos (U32_3.encList_eq C w)
    simp only [Spec.toID, numCfg] at this
    omega
  rw [h, hp]
  rfl

theorem enc32_pos (C : CTSH) (w : List Ch) :
    (encC32 C w).pos = (((U32_3.encList C w).2.1.length : ℕ) : ℤ) := by
  have := congrArg Spec.ID.pos (U32_3.encList_eq C w)
  simp only [Spec.toID, numCfg, U32_3.δ] at this
  rw [encList_left_length]
  omega

/-- The tape of the encoder, cell by cell. -/
theorem enc_tape (C : CTSH) (w : List Ch) (j : ℤ) :
    (Spec.toID 0 (encList C w)).tape j =
      vN (Conv1W.packV TR (a0 C w) (n0 C w) St.q0 (-(encC32 C w).pos)
        (fun i => (encC32 C w).tape (-i)) (-j)) := by
  have hp := enc32_pos C w
  have hT := enc32_tape C w
  have hn : n0 C w = (U32_3.encList C w).2.1.length + (U32_3.encList C w).2.2.length + 3 := by
    rw [n0, len32_eq, encList_left_length, encList_right_length]
  have ha : a0 C w = -((((U32_3.encList C w).2.1.length +
      (U32_3.encList C w).2.2.length : ℕ) : ℤ)) - 1 := by
    rw [a0, len32_eq, encList_left_length, encList_right_length]
  simp only [Spec.toID] at hT
  simp only [Spec.toID, encList, enc3]
  generalize (U32_3.encList C w).2.1 = l at *
  generalize (U32_3.encList C w).2.2 = r at *
  by_cases hj : 0 ≤ j
  · rw [if_pos hj, Conv1W.packV_out (.inl (by omega))]
    simp [vN]
  · rw [if_neg hj]
    obtain ⟨t, ht⟩ : ∃ t : ℕ, -j = (t : ℤ) + 1 := ⟨(-j - 1).toNat, by omega⟩
    have ht' : (0 - 1 - j).toNat = t := by omega
    rw [ht', getD_map_range]
    by_cases htn : t < l.length + r.length + 3
    · rw [if_pos htn, Conv1W.packV_in (by omega) (by rw [hn]; omega)]
      have hy : a0 C w + -j - 1 = (t : ℤ) - ((l.length : ℤ) + r.length) - 1 := by
        rw [ha]; push_cast; omega
      by_cases hm : t = r.length + 1
      · have hc : Conv1W.cell TR St.q0 (-(encC32 C w).pos) (fun i => (encC32 C w).tape (-i))
            (a0 C w + -j - 1) = .mk St.q0 ((encC32 C w).tape (0 + (encC32 C w).pos)) := by
          simp only [Conv1W.cell, Conv1W.mpos_minus q0_minus]
          rw [if_pos (by rw [hy, hp]; omega), Conv1W.mark_minus q0_minus]
          congr 2
          rw [hy, hp]; omega
        rw [hc, if_pos hm]
        simp only [vN, qN_q0]
        rw [hT 0, if_pos (le_refl _)]
        simp
      · have hc : Conv1W.cell TR St.q0 (-(encC32 C w).pos) (fun i => (encC32 C w).tape (-i))
            (a0 C w + -j - 1) =
            .pl ((encC32 C w).tape (((r.length : ℤ) + 1 - t) + (encC32 C w).pos)) := by
          simp only [Conv1W.cell, Conv1W.mpos_minus q0_minus]
          rw [if_neg (by rw [hy, hp]; omega)]
          congr 2
          rw [hy, hp]; omega
        rw [hc, if_neg hm]
        simp only [vN]
        rw [hT]
        by_cases hle : t ≤ r.length
        · rw [if_pos hle, if_pos (by omega)]
          congr 2
          omega
        · rw [if_neg hle, if_neg (by omega)]
          congr 2
          omega
    · rw [if_neg htn, Conv1W.packV_out (.inr (by rw [hn]; omega))]
      simp [vN]

/-- The encoder is the numbered encoded initial configuration (head at Spec position 0). -/
theorem encList_eq (C : CTSH) (w : List Ch) :
    Spec.toID 0 (encList C w) = numCfg num 0 (E600 C w) := by
  rw [E600_eq]
  refine ID_ext rfl (by simp [Spec.toID, numCfg]) fun x => ?_
  rw [enc_tape]
  simp [numCfg, num, cN]

/-- The entries of the (32,3) initial code are `0, 1, 2`. -/
theorem enc32_entries (C : CTSH) (w : List Ch) :
    (∀ a ∈ (U32_3.encList C w).2.1, a ≤ 2) ∧ (∀ a ∈ (U32_3.encList C w).2.2, a ≤ 2) := by
  have hlo : ∀ c : Ch, loN c ≤ 2 := by intro c; cases c <;> decide
  have hp : ∀ c : Ch, ∀ a ∈ U32_3.p2r c, a ≤ 2 := by intro c; cases c <;> decide
  refine ⟨fun a ha => ?_, fun a ha => ?_⟩
  · simp only [U32_3.encList, List.mem_append, List.mem_cons, List.mem_flatMap,
      List.not_mem_nil, or_false] at ha
    rcases ha with (rfl | rfl | rfl | ⟨u, -, rfl | rfl | ⟨c, -, hc⟩⟩) | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · exact hp c a hc
    · decide
  · simp only [U32_3.encList, List.mem_map] at ha
    obtain ⟨c, -, rfl⟩ := ha
    exact hlo c

theorem getD_le2 (l : List ℕ) (h : ∀ a ∈ l, a ≤ 2) (i : ℕ) : l.getD i 0 ≤ 2 := by
  rw [List.getD_eq_getElem?_getD]
  cases hi : l[i]? with
  | none => simp
  | some a => exact h a (List.mem_of_getElem? hi)

set_option maxRecDepth 100000 in
theorem U_syms : ∀ a ∈ [1, 2, 3, 4, 5, 6], a ∈ Spec.symbols U := by decide +kernel

set_option maxRecDepth 100000 in
theorem U_st0 : (0 : ℕ) ∈ Spec.states U := by decide +kernel

/-- The encoded initial ID is an ID of U (`c(n, α) ∈ ID(U)` of Morita Def. 7.1). -/
theorem isIDOf_encList (C : CTSH) (w : List Ch) : Spec.IsIDOf U (Spec.toID 0 (encList C w)) := by
  obtain ⟨hl, hr⟩ := enc32_entries C w
  refine isIDOf_toID U 0 _ U_st0 fun a ha => .inr ?_
  simp only [encList, enc3, List.append_nil, List.mem_map, List.mem_range] at ha
  obtain ⟨t, -, rfl⟩ := ha
  have h0 := getD_le2 _ hr 0
  have h1 := getD_le2 _ hr ((U32_3.encList C w).2.2.length + 1 - t)
  have h2 := getD_le2 _ hl (t - (U32_3.encList C w).2.2.length - 2)
  refine U_syms _ ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  split_ifs <;> omega

open Primrec in
theorem enc3_primrec : Primrec enc3 := by
  have l : Primrec fun p : Spec.Code × ℕ => p.1.2.1 := fst.comp (snd.comp fst)
  have r : Primrec fun p : Spec.Code × ℕ => p.1.2.2 := snd.comp (snd.comp fst)
  have t : Primrec fun p : Spec.Code × ℕ => p.2 := snd
  have rl : Primrec fun p : Spec.Code × ℕ => p.1.2.2.length := list_length.comp r
  have G := list_getD (0 : ℕ)
  have hf : Primrec₂ fun (z : Spec.Code) (t : ℕ) =>
      if t = z.2.2.length + 1 then 4 + z.2.2.getD 0 0
      else 1 + (if t ≤ z.2.2.length then z.2.2.getD (z.2.2.length + 1 - t) 0
                else z.2.1.getD (t - z.2.2.length - 2) 0) :=
    (Primrec.ite (Primrec.eq.comp t (succ.comp rl))
      (nat_add.comp (const 4) (G.comp r (const 0)))
      (nat_add.comp (const 1) (Primrec.ite (nat_le.comp t rl)
        (G.comp r (nat_sub.comp (succ.comp rl) t))
        (G.comp l (nat_sub.comp (nat_sub.comp t rl) (const 2)))))).to₂
  exact pair (const 0) (pair (list_map (list_range.comp (nat_add.comp (nat_add.comp
    (list_length.comp (fst.comp snd)) (list_length.comp (snd.comp snd))) (const 3))) hf)
    (const []))

theorem encList_primrec : Primrec₂ encList := enc3_primrec.comp₂ U32_3.encList_primrec

/-! ### The readout -/

/-- `pl (pl s) ↦ s`; everything else (the blank, marks, counters) `↦` the blank of (32,3). -/
def baseN (c : ℕ) : ℕ := if 1 ≤ c ∧ c ≤ 3 then c - 1 else 0

/-- The (32,3) symbol carried by the state of the one-way-updating machine with index `k`
    (`c s` and `g p v` carry the cell right of the (32,3) head). -/
def carry (k : ℕ) : ℕ :=
  match numf k with
  | .c s => sN s
  | .g _ v => sN v
  | _ => 0

/-- The (32,3) window (left end first) recovered from the two lists `(l, r)` of a (3,600) code:
    left of the head the cells as they are; the head cell `ct x k` gives the (32,3) head cell
    (from `x`) and the cell right of it (carried by `k`); the cells right of the head are the
    (32,3) cells from two right of its head. -/
def rec3 (l r : List ℕ) : List ℕ :=
  (l.map baseN).reverse ++
    (if 4 ≤ r.getD 0 0 % 196 then (r.getD 0 0 % 196 - 4) % 3 else r.getD 0 0 % 196 - 1) ::
    carry (r.getD 0 0 / 196 - 1) :: (r.drop 1).map baseN

/-- The (32,3) pseudo-state: the head cell `ct (pl u) _` (`x ≤ 3`) means `halt = 33`, the head
    cell `ct (mk begin u) _` means `null = 32`. -/
def qOf (r : List ℕ) : ℕ := if r.getD 0 0 % 196 ≤ 3 then 33 else 32

/-- **Readout** (list level) from a code `g` of the halting ID: `(|C|, ϕ₁(vf))`, by the (32,3)
    readout on the recovered (32,3) window. It does not look at the number of steps. -/
def readU (g : Spec.Code) : Option (ℕ × List ℕ) :=
  some (U32_3.readL 33 (qOf g.2.2) (rec3 g.2.1 g.2.2))

theorem map_baseN_replicate (k : ℕ) : (List.replicate k 0).map baseN = List.replicate k 0 := by
  simp [baseN]

theorem rec3_padL (k : ℕ) (l r : List ℕ) :
    rec3 (l ++ List.replicate k 0) r = List.replicate k 0 ++ rec3 l r := by
  simp only [rec3, List.map_append, List.reverse_append, map_baseN_replicate,
    List.reverse_replicate, List.append_assoc]

theorem rec3_padR (k : ℕ) (l r : List ℕ) :
    ∃ j, rec3 l (r ++ List.replicate k 0) = rec3 l r ++ List.replicate j 0 := by
  obtain ⟨j, hj⟩ := U32_3.drop1_pad r k
  refine ⟨j, ?_⟩
  simp only [rec3, Spec.CodePad.getD_append_replicate, hj, List.map_append, map_baseN_replicate]
  simp

theorem qOf_padR (k : ℕ) (r : List ℕ) : qOf (r ++ List.replicate k 0) = qOf r := by
  simp only [qOf, Spec.CodePad.getD_append_replicate]

/-- **The readout depends only on the ID**, not on the code chosen for it. -/
theorem readU_toID {p : ℤ} {g g' : Spec.Code} (h : Spec.toID p g = Spec.toID p g') :
    readU g = readU g' := by
  refine congrArg some (read_toID2 (fun _ l r => U32_3.readL 33 (qOf r) (rec3 l r)) ?_ ?_ h)
  · intro s k l r
    simp only [rec3_padL, U32_3.readL_padL]
  · intro s k l r
    obtain ⟨j, hj⟩ := rec3_padR k l r
    simp only [qOf_padR, hj, U32_3.readL_padR]

/-! #### Computability of the readout -/

theorem carry_eq_tab (k : ℕ) :
    carry k = ((List.range (allVSt.length + 1)).map carry).getD k 0 := by
  rw [getD_map_range]
  split
  · rfl
  · rename_i h
    have : numf k = VSt.L := by
      simp only [numf]
      exact List.getD_eq_default _ _ (by omega)
    simp [carry, this]

open Primrec in
theorem carry_primrec : Primrec carry :=
  ((list_getD 0).comp (const ((List.range (allVSt.length + 1)).map carry)) .id).of_eq fun k =>
    (carry_eq_tab k).symm

open Primrec in
theorem baseN_primrec : Primrec baseN :=
  (Primrec.ite (PrimrecPred.and (nat_le.comp (const 1) .id) (nat_le.comp .id (const 3)))
    (nat_sub.comp .id (const 1)) (const 0)).of_eq fun _ => rfl

open Primrec in
theorem readL_primrec : Primrec fun p : ℕ × List ℕ => U32_3.readL 33 p.1 p.2 := by
  have p0 : Primrec fun a : ℕ => a == 0 := Primrec.beq.comp .id (const 0)
  have hR : Primrec fun p : ℕ × List ℕ => p.2.dropWhile (· == 0) := (list_dropWhile p0).comp snd
  have hs : Primrec fun p : ℕ × List ℕ => (p.2.dropWhile (· == 0)).foldl U32_3.scan (0, 0, 0) :=
    list_foldl hR (const (0, 0, 0)) (U32_3.scan_primrec.comp (fst.comp snd) (snd.comp snd)).to₂
  have hc := fst.comp (snd.comp hs)
  have ht := U32_3.tail32_primrec.comp (list_drop.comp (snd.comp (snd.comp hs)) hR)
  exact (Primrec.ite (Primrec.eq.comp fst (const 33))
    (pair hc (list_cons.comp (const 1) ht)) (pair hc (const []))).of_eq fun p => by
      simp only [U32_3.readL, U32_3.readR]

open Primrec in
theorem readU_primrec : Primrec readU := by
  have l : Primrec fun g : Spec.Code => g.2.1 := fst.comp snd
  have r : Primrec fun g : Spec.Code => g.2.2 := snd.comp snd
  have c : Primrec fun g : Spec.Code => g.2.2.getD 0 0 := (list_getD 0).comp r (const 0)
  have vx : Primrec fun g : Spec.Code => g.2.2.getD 0 0 % 196 := nat_mod.comp c (const 196)
  have u : Primrec fun g : Spec.Code =>
      if 4 ≤ g.2.2.getD 0 0 % 196 then (g.2.2.getD 0 0 % 196 - 4) % 3
      else g.2.2.getD 0 0 % 196 - 1 :=
    Primrec.ite (nat_le.comp (const 4) vx) (nat_mod.comp (nat_sub.comp vx (const 4)) (const 3))
      (nat_sub.comp vx (const 1))
  have cr : Primrec fun g : Spec.Code => carry (g.2.2.getD 0 0 / 196 - 1) :=
    carry_primrec.comp (nat_sub.comp (nat_div.comp c (const 196)) (const 1))
  have hrec : Primrec fun g : Spec.Code => rec3 g.2.1 g.2.2 :=
    list_append.comp (list_reverse.comp (list_map l (baseN_primrec.comp snd).to₂))
      (list_cons.comp u (list_cons.comp cr
        (list_map (list_drop.comp (const 1) r) (baseN_primrec.comp snd).to₂)))
  have hq : Primrec fun g : Spec.Code => qOf g.2.2 :=
    Primrec.ite (nat_le.comp vx (const 3)) (const 33) (const 32)
  exact option_some.comp (readL_primrec.comp (pair hq hrec))

/-! ### The final configurations (typed) -/

/-- The final configuration of (3,600) for a halting configuration `(p, x, t)` of `T'`
    (the (32,3) configuration just before its halting quintuple), with the window `[a, a + n)`
    of the mirrored one-way-updating machine (`fin600_Ffin`). -/
def Ffin (a : ℤ) (n : ℕ) (p : St) (x : ℤ) (t : ℤ → Sy) : Cfg TSt Ps (CSym (VSym St Sy)) :=
  flipC { st := .go .R0, pos := -x - a + 1,
          tape := upd (fun i => .pl (mix (-x - a + 1)
              (Conv1W.packV TR (a - 1) n p (-x) (fun i => t (-i)))
              (Conv1W.packV TR a n p (-x) (fun i => t (-i))) i)) (-x - a + 1)
            (.ct (mix (-x - a + 1) (Conv1W.packV TR (a - 1) n p (-x) (fun i => t (-i)))
                (Conv1W.packV TR a n p (-x) (fun i => t (-i))) (-x - a + 1))
              (idx (if isPlus TR p then .g p (t (-(-x - 1))) else .c (t (-(-x - 1)))))) }

/-- The final configuration of the zoo's theorem, unfolded (the proof of
    `URTM.CTSH.Readout.fin600_eq` in `lean/URTM/CTSHReadout3_600.lean`; that module is not
    imported, since it also holds `noncomputable` tape-level readouts). -/
theorem fin600_Ffin (C : CTSH) (w : List Ch) (vf : List Ch) (mf : ℕ) (rm : List Ch) (N : ℕ)
    {p : St} (hp : (unhalt f32 (finCfg32 C vf mf rm)).st = .go p) :
    fin600 C w vf mf rm N = Ffin (a0 C w - N) (n0 C w + 2 * N) p
      (unhalt f32 (finCfg32 C vf mf rm)).pos (unhalt f32 (finCfg32 C vf mf rm)).tape := by
  simp only [fin600, Conv3S.finM, Conv3S.fin, Conv1W.Ev, flipC, hp, Conv1W.haltV, Conv3P.enc]
  rw [if_neg (by split <;> nofun)]
  rfl

theorem numf_idx (q : VSt St Sy) : numf (idx q) = q := dec_idx q (allVSt_all q)

theorem q2_plus : isPlus TR St.q2 = true := by decide +kernel

section Fin
variable (a : ℤ) (n : ℕ) (p : St) (x : ℤ) (t : ℤ → Sy)

/-- The tape of the final configuration relative to its head. -/
theorem Ffin_tape (d : ℤ) :
    (Ffin a n p x t).tape ((Ffin a n p x t).pos + d) =
      upd (fun i => CSym.pl (mix (-x - a + 1)
          (Conv1W.packV TR (a - 1) n p (-x) (fun i => t (-i)))
          (Conv1W.packV TR a n p (-x) (fun i => t (-i))) i)) (-x - a + 1)
        (.ct (mix (-x - a + 1) (Conv1W.packV TR (a - 1) n p (-x) (fun i => t (-i)))
            (Conv1W.packV TR a n p (-x) (fun i => t (-i))) (-x - a + 1))
          (idx (if isPlus TR p then .g p (t (-(-x - 1))) else .c (t (-(-x - 1))))))
        (-x - a + 1 - d) := by
  simp only [Ffin, flipC]
  congr 1
  omega

variable {a n p x t}

theorem baseN_plpl (s : Sy) : baseN (cN (.pl (.pl s))) = sN s := by cases s <;> rfl

/-- The head cell, when `p` is entered from the left in the mirrored machine (`Q₋`): the mark
    `mk p u` with the counter of `c s`. -/
theorem Ffin_head_minus (hI : Conv1W.Inv TR Sy.s0 GlR a n p (-x) (fun i => t (-i)))
    (hp : isPlus TR p = false) :
    (Ffin a n p x t).tape (Ffin a n p x t).pos = .ct (.mk p (t x)) (idx (.c (t (x + 1)))) := by
  have h := Ffin_tape a n p x t 0
  rw [Int.add_zero, Int.sub_zero, upd_eq, mix_ge (Int.le_refl _),
    Conv1W.packV_mk (by have := hI.lo; omega) (by have := hI.hi; omega)
      (by rw [Conv1W.mpos_minus hp]; omega), Conv1W.mark_minus hp] at h
  have e1 : -(a + (-x - a + 1) - 1) = x := by omega
  have e2 : -(-x - 1) = x + 1 := by omega
  rw [h]
  simp only [hp, Bool.false_eq_true, if_false, e1, e2]

/-- The head cell, when `p` is in `Q₊`: the plain symbol with the counter of `g p v`. -/
theorem Ffin_head_plus (hI : Conv1W.Inv TR Sy.s0 GlR a n p (-x) (fun i => t (-i)))
    (hp : isPlus TR p = true) :
    (Ffin a n p x t).tape (Ffin a n p x t).pos = .ct (.pl (t x)) (idx (.g p (t (x + 1)))) := by
  have h := Ffin_tape a n p x t 0
  rw [Int.add_zero, Int.sub_zero, upd_eq, mix_ge (Int.le_refl _),
    Conv1W.packV_pl (by have := hI.lo; omega) (by have := hI.hi; omega)
      (by rw [Conv1W.mpos_plus hp]; omega)] at h
  have e1 : -(a + (-x - a + 1) - 1) = x := by omega
  have e2 : -(-x - 1) = x + 1 := by omega
  rw [h]
  simp only [hp, if_true, e1, e2]

/-- Left of the head: the (32,3) cells as they are. -/
theorem Ffin_left (hI : Conv1W.Inv TR Sy.s0 GlR a n p (-x) (fun i => t (-i))) (d : ℤ)
    (hd : d < 0) :
    baseN (cN ((Ffin a n p x t).tape ((Ffin a n p x t).pos + d))) = sN (t (x + d)) := by
  rw [Ffin_tape, upd_ne _ _ (by omega), mix_ge (by omega)]
  by_cases hin : -x - a + 1 - d ≤ n
  · rw [Conv1W.packV_pl (by have := hI.lo; omega) hin
      (by simp only [Conv1W.mpos]; split <;> omega), baseN_plpl]
    congr 2
    omega
  · rw [Conv1W.packV_out (.inr (by omega))]
    have h := hI.out (-x - d) (.inr (by omega))
    rw [show x + d = -(-x - d) by omega, h]
    rfl

/-- Right of the head: the (32,3) cells from two right of its head (the cell right of the head is
    carried by the state index). -/
theorem Ffin_right (hI : Conv1W.Inv TR Sy.s0 GlR a n p (-x) (fun i => t (-i))) (d : ℤ)
    (hd : 1 ≤ d) :
    baseN (cN ((Ffin a n p x t).tape ((Ffin a n p x t).pos + d))) = sN (t (x + d + 1)) := by
  rw [Ffin_tape, upd_ne _ _ (by omega), mix_lt (by omega)]
  by_cases hin : 1 ≤ -x - a + 1 - d
  · rw [Conv1W.packV_pl hin (by have := hI.hi; omega)
      (by simp only [Conv1W.mpos]; split <;> omega), baseN_plpl]
    congr 2
    omega
  · rw [Conv1W.packV_out (.inl (by omega))]
    have h := hI.out (-x - d - 1) (.inl (by omega))
    rw [show x + d + 1 = -(-x - d - 1) by omega, h]
    rfl

/-- The tape is blank outside a finite window around the head. -/
theorem Ffin_supp (hI : Conv1W.Inv TR Sy.s0 GlR a n p (-x) (fun i => t (-i))) (d : ℤ)
    (hd : d < -x - a + 1 - n ∨ -x - a < d) :
    (Ffin a n p x t).tape ((Ffin a n p x t).pos + d) = .pl .bl := by
  have hlo := hI.lo
  have hhi := hI.hi
  rw [Ffin_tape, upd_ne _ _ (by omega)]
  rcases hd with hd | hd
  · rw [mix_ge (by omega), Conv1W.packV_out (.inr (by omega))]
  · rw [mix_lt (by omega), Conv1W.packV_out (.inl (by omega))]

end Fin

/-! ### Reading the final ID -/

theorem getD_rec (fa fb : ℕ → ℕ) (m k u s i : ℕ) :
    (((List.range m).map fa).reverse ++ u :: s :: (List.range k).map fb).getD i 0 =
      if i < m then fa (m - 1 - i) else if i = m then u else if i = m + 1 then s
      else if i < m + 2 + k then fb (i - m - 2) else 0 := by
  have hlen : (((List.range m).map fa).reverse).length = m := by simp
  by_cases h1 : i < m
  · rw [if_pos h1, List.getD_append _ _ _ _ (by rw [hlen]; exact h1),
      congrFun (List.getD_reverse i (by simpa using h1)) 0, getD_map_range]
    simp only [List.length_map, List.length_range]
    rw [if_pos (by omega)]
  · rw [if_neg h1, List.getD_append_right _ _ _ _ (by rw [hlen]; omega), hlen]
    obtain ⟨j, rfl⟩ : ∃ j, i = m + j := ⟨i - m, by omega⟩
    rw [Nat.add_sub_cancel_left]
    match j with
    | 0 => simp
    | 1 => simp
    | j + 2 =>
      have e1 : ¬ (m + (j + 2) = m) := by omega
      have e2 : ¬ (m + (j + 2) = m + 1) := by omega
      rw [List.getD_cons_succ, List.getD_cons_succ, getD_map_range, if_neg e1, if_neg e2]
      by_cases hj : j < k
      · have e3 : m + (j + 2) < m + 2 + k := by omega
        rw [if_pos hj, if_pos e3, Nat.add_sub_cancel]
      · have e3 : ¬ m + (j + 2) < m + 2 + k := by omega
        rw [if_neg hj, if_neg e3]

theorem drop_one_map_range (f : ℕ → ℕ) (k : ℕ) :
    ((List.range (k + 1)).map f).drop 1 = (List.range k).map (fun i => f (i + 1)) := by
  rw [List.range_succ_eq_map, List.map_cons, List.drop_succ_cons, List.drop_zero, List.map_map]
  rfl

theorem getD_zeros_append (m : ℕ) (L : List ℕ) (i : ℕ) :
    (List.replicate m 0 ++ L).getD i 0 = if i < m then 0 else L.getD (i - m) 0 := by
  by_cases h : i < m
  · rw [if_pos h, List.getD_append _ _ _ _ (by simpa using h)]
    simp [List.getD_eq_getElem?_getD, h]
  · rw [if_neg h, List.getD_append_right _ _ _ _ (by simpa using Nat.le_of_not_lt h)]
    simp

/-- **Reading a final ID from its description relative to the head.** `τ` is the numbered (32,3)
    tape (the list `L`), `P` the (32,3) head position; the head cell of `γ` is a counter symbol
    whose content gives `τ P` and whose index carries `τ (P + 1)`; left of the head `γ` shows
    the (32,3) cells as they are, right of the head the (32,3) cells shifted by one; `γ` is blank
    outside a window. Then some code of `γ` is read as the (32,3) readout of `L`. -/
theorem readU_of_shape (γ : Spec.ID) (τ : ℤ → ℕ) (P : ℕ) (L : List ℕ) (halt : Bool)
    (k mL mR : ℕ)
    (hτ : ∀ y : ℤ, τ y = if 0 ≤ y then L.getD y.toNat 0 else 0) (hτ3 : ∀ y, τ y < 3)
    (hhead : γ.tape γ.pos = 196 * (k + 1) + ((if halt then 1 else 4) + τ P))
    (hcarry : carry k = τ (P + 1))
    (hleft : ∀ d : ℤ, d < 0 → baseN (γ.tape (γ.pos + d)) = τ (P + d))
    (hright : ∀ d : ℤ, 1 ≤ d → baseN (γ.tape (γ.pos + d)) = τ (P + d + 1))
    (hsupp : ∀ d : ℤ, (d < -(mL : ℤ) ∨ (mR : ℤ) < d) → γ.tape (γ.pos + d) = 0) :
    ∃ g, Spec.toID γ.pos g = γ ∧
      readU g = some (U32_3.readL 33 (if halt then 33 else 32) L) := by
  refine ⟨codeOf γ (mL + P) (mR + L.length + 1), toID_codeOf γ _ _ (fun x hx => ?_), ?_⟩
  · have := hsupp (x - γ.pos) (by push_cast at hx; omega)
    rwa [show γ.pos + (x - γ.pos) = x by omega] at this
  · have h3 := hτ3 P
    have hv : (if halt then 1 else 4) + τ P < 196 := by split <;> omega
    have hc : (codeOf γ (mL + P) (mR + L.length + 1)).2.2.getD 0 0 =
        196 * (k + 1) + ((if halt then 1 else 4) + τ P) := by
      simp only [codeOf]
      rw [getD_map_range, if_pos (by omega)]
      simpa using hhead
    have hmod : (codeOf γ (mL + P) (mR + L.length + 1)).2.2.getD 0 0 % 196 =
        (if halt then 1 else 4) + τ P := by
      rw [hc, Nat.mul_add_mod, Nat.mod_eq_of_lt hv]
    have hdiv : (codeOf γ (mL + P) (mR + L.length + 1)).2.2.getD 0 0 / 196 - 1 = k := by
      rw [hc, Nat.mul_add_div (by decide), Nat.div_eq_of_lt hv]
      omega
    have hq : qOf (codeOf γ (mL + P) (mR + L.length + 1)).2.2 = if halt then 33 else 32 := by
      simp only [qOf, hmod]
      cases halt <;> simp <;> omega
    have hu : (if 4 ≤ (if halt then 1 else 4) + τ P then ((if halt then 1 else 4) + τ P - 4) % 3
        else (if halt then 1 else 4) + τ P - 1) = τ P := by
      cases halt
      · simp only [Bool.false_eq_true, if_false]
        rw [if_pos (by omega), Nat.add_sub_cancel_left, Nat.mod_eq_of_lt h3]
      · simp only [if_true]
        rw [if_neg (by omega), Nat.add_sub_cancel_left]
    have hrec : ∀ i, (rec3 (codeOf γ (mL + P) (mR + L.length + 1)).2.1
        (codeOf γ (mL + P) (mR + L.length + 1)).2.2).getD i 0 =
        (List.replicate mL 0 ++ L).getD i 0 := by
      intro i
      have hfa : ∀ j : ℕ, j < mL + P →
          baseN (γ.tape (γ.pos - 1 - ((mL + P - 1 - j : ℕ) : ℤ))) = τ ((j : ℤ) - mL) := by
        intro j hj
        have e : γ.pos - 1 - ((mL + P - 1 - j : ℕ) : ℤ) = γ.pos + ((j : ℤ) - (mL + P)) := by
          omega
        rw [e, hleft _ (by omega)]
        congr 1
        omega
      have hfb : ∀ j : ℕ, baseN (γ.tape (γ.pos + ((j + 1 : ℕ) : ℤ))) = τ ((P : ℤ) + j + 2) := by
        intro j
        rw [hright _ (by omega)]
        congr 1
      simp only [rec3, hmod, hdiv, hu, hcarry]
      simp only [codeOf, List.map_map, drop_one_map_range]
      rw [getD_rec, getD_zeros_append]
      simp only [Function.comp_apply]
      by_cases h1 : i < mL + P
      · rw [if_pos h1, hfa i h1, hτ]
        by_cases h2 : i < mL
        · have e : ¬ (0 : ℤ) ≤ (i : ℤ) - mL := by omega
          rw [if_pos h2, if_neg e]
        · have e : (0 : ℤ) ≤ (i : ℤ) - mL := by omega
          rw [if_neg h2, if_pos e]
          congr 1
          omega
      · have h2' : ¬ i < mL := by omega
        rw [if_neg h1, if_neg h2']
        by_cases h2 : i = mL + P
        · rw [if_pos h2, hτ, if_pos (Int.natCast_nonneg P)]
          congr 1
          omega
        · rw [if_neg h2]
          by_cases h3' : i = mL + P + 1
          · have e : (0 : ℤ) ≤ (P : ℤ) + 1 := by omega
            rw [if_pos h3', hτ, if_pos e]
            congr 1
            omega
          · rw [if_neg h3']
            by_cases h4 : i < mL + P + 2 + (mR + L.length)
            · have e : (0 : ℤ) ≤ (P : ℤ) + ((i - (mL + P) - 2 : ℕ) : ℤ) + 2 := by omega
              rw [if_pos h4, hfb, hτ, if_pos e]
              congr 1
              omega
            · rw [if_neg h4, List.getD_eq_default _ _ (by omega)]
    obtain ⟨M, j1, j2, e1, e2⟩ := Spec.CodePad.pad_of_getD _ _ hrec
    simp only [readU, hq]
    rw [e1, U32_3.readL_padR, ← U32_3.readL_padL 33 _ mL L, e2, U32_3.readL_padR]

/-! ### The final configurations, numbered -/

theorem carry_c (s : Sy) : carry (idx (.c s)) = sN s := by
  simp only [carry, numf_idx]

theorem carry_g (p : St) (v : Sy) : carry (idx (.g p v)) = sN v := by
  simp only [carry, numf_idx]

/-- The numbered (32,3) list tape, as a function. -/
theorem tau_tp (L : List Sy) (y : ℤ) :
    sN (Sim.tp Sy.s0 L y) = if 0 ≤ y then (L.map sN).getD y.toNat 0 else 0 := by
  cases y with
  | ofNat n =>
    have h0 : (0 : ℤ) ≤ Int.ofNat n := Int.natCast_nonneg n
    rw [if_pos h0]
    show sN (L.getD n Sy.s0) = (L.map sN).getD n 0
    exact (getD_map_zero sN Sy.s0 rfl L n).symm
  | negSucc n =>
    have h0 : ¬ (0 : ℤ) ≤ Int.negSucc n := by omega
    rw [if_neg h0]
    rfl

theorem numCfg_rel (δ : ℤ) (c : Cfg TSt Ps (CSym (VSym St Sy))) (d : ℤ) :
    (numCfg num δ c).tape ((numCfg num δ c).pos + d) = cN (c.tape (c.pos + d)) := by
  simp only [numCfg, num]
  congr 2
  omega

/-- **Reading the final configuration of (3,600)** for a halting configuration `(p, P, L)` of
    `T'` on a list tape, in the two cases of the head cell. -/
theorem read_Ffin (a : ℤ) (n : ℕ) (p : St) (P : ℕ) (L : List Sy)
    (hI : Conv1W.Inv TR Sy.s0 GlR a n p (-(P : ℤ)) (fun i => Sim.tp Sy.s0 L (-i)))
    (halt : Bool) (k : ℕ)
    (hhead : cN ((Ffin a n p P (Sim.tp Sy.s0 L)).tape (Ffin a n p P (Sim.tp Sy.s0 L)).pos) =
      196 * (k + 1) + ((if halt then 1 else 4) + sN (Sim.tp Sy.s0 L P)))
    (hcarry : carry k = sN (Sim.tp Sy.s0 L ((P : ℤ) + 1))) :
    ∃ g, Spec.toID (numCfg num 0 (Ffin a n p P (Sim.tp Sy.s0 L))).pos g =
        numCfg num 0 (Ffin a n p P (Sim.tp Sy.s0 L)) ∧
      readU g = some (U32_3.readL 33 (if halt then 33 else 32) (L.map sN)) := by
  have hlo := hI.lo
  have hhi := hI.hi
  refine readU_of_shape _ (fun y => sN (Sim.tp Sy.s0 L y)) P (L.map sN) halt k
    (n + P + a - 1).toNat (-(P : ℤ) - a).toNat (tau_tp L) (fun y => sN_lt _) ?_ hcarry
    (fun d hd => ?_) (fun d hd => ?_) (fun d hd => ?_)
  · have := numCfg_rel 0 (Ffin a n p P (Sim.tp Sy.s0 L)) 0
    rw [Int.add_zero, Int.add_zero] at this
    rw [this, hhead]
  · rw [numCfg_rel, Ffin_left hI d hd]
  · rw [numCfg_rel, Ffin_right hI d hd]
  · rw [numCfg_rel, Ffin_supp hI d (by omega)]
    rfl

/-- The final configurations of (32,3) on list tapes, read by the (32,3) readout
    (as in `U32_3.runSim_U`). -/
theorem fin32_read (C : CTSH) (vf : List Ch) (mf : ℕ) (rm : List Ch) (hf : Halting C (vf, mf)) :
    ∃ (h : Ps) (L : List Sy) (P : ℕ),
      finCfg32 C vf mf rm = ⟨.halt h, (P : ℤ), Sim.tp .s0 L⟩ ∧
      U32_3.readL 33 (if h = Ps.h1 then 33 else 32) (L.map sN) = (C.length, vf.map loN) := by
  obtain ⟨hk, hv | hv⟩ := hf
  · obtain ⟨v, hv1, hv2⟩ := hv
    simp only at hv1 hv2
    subst hv1 hv2
    refine ⟨.h1, URTM.CTSH.U32_3.finList nm32 C (Ch.Y :: v) 0 rm,
      (URTM.CTSH.U32_3.RA nm32 C 0).length, ?_, ?_⟩
    · simp [finCfg32, URTM.CTSH.U32_3.finCfg, nm32]
    · have hL : (URTM.CTSH.U32_3.finList nm32 C (Ch.Y :: v) 0 rm).map sN =
          0 :: (URTM.CTSH.U32_3.RA nm32 C 0).map sN ++ 0 :: (rm.map loN ++ 0 :: v.map loN) := by
        simp only [URTM.CTSH.U32_3.finList, List.map_append, List.map_cons, U32_3.map_lo]
        simp [nm32]
        rfl
      rw [hL, if_pos rfl]
      exact U32_3.readL_halt C rm v
  · simp only at hv
    subst hv
    have hm : mf ≤ C.length := by simp [CTSH.k] at hk; omega
    refine ⟨.h0, URTM.CTSH.U32_3.finList nm32 C [] mf rm,
      (URTM.CTSH.U32_3.RA nm32 C mf).length + 2 + rm.length, ?_, ?_⟩
    · simp [finCfg32, URTM.CTSH.U32_3.finCfg, nm32]
    · have hL : (URTM.CTSH.U32_3.finList nm32 C [] mf rm).map sN =
          0 :: (URTM.CTSH.U32_3.RA nm32 C mf).map sN ++ 0 :: rm.map loN := by
        simp only [URTM.CTSH.U32_3.finList, URTM.CTSH.U32_3.tapeList, List.map_append,
          List.map_cons, U32_3.map_lo, List.map_nil, List.append_nil]
        simp [nm32]
        rfl
      rw [hL, if_neg (by decide)]
      exact U32_3.readL_null C hm _ _ (by decide)

/-! ### The run-level simulation and the main theorem -/

/-- **URTM(3,600) simulates every CTSH at the level of Spec** (run level, exact readback). -/
theorem runSim_U (C : CTSH) (w : List Ch) :
    RunSim (CStep C) (Halting C) (Spec.Step U) (Spec.Halted U)
      (fun y γ => ∃ g, Spec.toID γ.pos g = γ ∧ readU g = some (C.length, y.1.map loN))
      (w, 0) (Spec.toID 0 (encList C w)) := by
  rw [encList_eq]
  obtain ⟨-, -, -, -, -, -, -, -, hF, -, hN⟩ := urtm3_600_simulates_ctsh C w
  refine runSim_of_sim num T3py 0 C w (E600 C w)
    (fun f c => ∃ rm N, HaltsIn T' N (encC32 C w) (unhalt f32 (finCfg32 C f.1 f.2 rm)) ∧
      c = fin600 C w f.1 f.2 rm N) _
    (fun m f hf => ?_) (fun hn => hN.mp hn) (fun f c hf hc => ?_)
  · obtain ⟨N, M, rm, -, hT, hM⟩ := hF m f.1 f.2 hf
    exact ⟨M, _, hM, rm, N, hT, rfl⟩
  · obtain ⟨rm, N, hT, rfl⟩ := hc
    obtain ⟨vf, mf⟩ := f
    obtain ⟨h, L, P, hfin, hrd⟩ := fin32_read C vf mf rm hf
    have he : unhalt f32 (finCfg32 C vf mf rm) = ⟨.go (f32 h), (P : ℤ), Sim.tp .s0 L⟩ := by
      rw [hfin]; rfl
    -- the invariant of the mirrored run
    obtain ⟨⟨p, hp, hI⟩, -⟩ := Conv1W.run_sim (Conv3S.hyp1W hyp) (c0 := flipC (encC32 C w))
      (p0 := .q0) rfl (inv0 C w) N (Conv3Base.stepN_mirror hT.1)
    rw [he] at hp hI
    have hpp : f32 h = p := Tgt.go.inj hp
    subst hpp
    simp only [flipC] at hI
    have hF600 : fin600 C w vf mf rm N =
        Ffin (a0 C w - N) (n0 C w + 2 * N) (f32 h) (P : ℤ) (Sim.tp .s0 L) := by
      have := fin600_Ffin C w vf mf rm N (p := f32 h) (by rw [he])
      rw [he] at this
      exact this
    simp only [hF600]
    cases h with
    | h0 =>
      -- null: `begin` is in Q₋ of the mirrored machine; the head cell is the mark `mk begin u`
      have hh := Ffin_head_minus hI q0_minus
      obtain ⟨g, hg, hr⟩ := read_Ffin _ _ _ P L hI false (idx (.c (Sim.tp .s0 L ((P : ℤ) + 1))))
        (by rw [hh]; simp only [cN, vN, f32, qN_q0]; simp) (carry_c _)
      exact ⟨g, hg, by rw [hr]; exact congrArg some hrd⟩
    | h1 =>
      -- halt: `case_y_2` is in Q₊; the head cell is plain
      have hh := Ffin_head_plus hI q2_plus
      obtain ⟨g, hg, hr⟩ := read_Ffin _ _ _ P L hI true
        (idx (.g St.q2 (Sim.tp .s0 L ((P : ℤ) + 1))))
        (by rw [hh]; simp only [cN, vN, f32]; simp) (carry_g _ _)
      exact ⟨g, hg, by rw [hr]; exact congrArg some hrd⟩

/-- **URTM(3,600) is a UTM in the strict sense of Morita Def. 7.1.** -/
theorem isUTMStrict_U : Spec.IsUTMStrict U :=
  ChainGen.isUTMStrict_of_ctsh U encList readU encList_primrec readU_primrec isIDOf_encList
    runSim_U (fun _ _ _ h => readU_toID h)

end URTM.Univ.U3_600
