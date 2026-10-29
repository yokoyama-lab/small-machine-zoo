/-
  **URTM(3,659): encoder, readout, and universality in the sense of Def. 7.1.**

  The machine (`Num3_659.lean`) is the improved 3-state conversion of docs/09, **not mirrored**, applied
  to Morita's (32,3) without its halting quintuples (`Sim3_659.lean`). The construction follows the
  mirrored URTM(3,600) (`U3_600.lean`) with left and right exchanged: a (32,3) configuration is packed into
  a window of plain cells `pl (pl s)` that starts at `0` and grows to the right (by two cells and a shift
  of one per simulated step), so the final configuration depends on the number `N` of steps
  (`Sim3_659.fin659 … N`). What does not depend on the direction (the numbering `num`, the (32,3)
  readout `U32_3.readL`, `baseN`, the list lemmas `getD_rec` …, `tau_tp`, `numCfg_rel`, `fin32_read`) is
  taken from `U3_600` / `Num3_600`.

  * `encList C w`: the Spec code of the encoded initial configuration `E659 C w`, computed from
    the (32,3) initial code: state `L`, head on the blank left of the window; right of the head the
    (32,3) tape and three blank cells of (32,3), each `pl (pl s) ↦ 1 + s`, except the cell left of the
    (32,3) head, which carries the mark `pl (mkp begin s) ↦ 100 + s` (`begin` is entered by right moves)
    (`encList_eq`).
  * Final configurations (`Ffin`, `fin659_Ffin`): state `R0`; the head cell is a counter symbol
    `ct x k`, where `x` shows the (32,3) head cell and `k` (the index of a state of the intermediate
    machine) carries the cell left of it; right of the head are the (32,3) cells as they are, left of
    the head the (32,3) cells shifted by one; padding cells `pl (pl b)` and blanks `pl bl` surround
    them, their number depending on `N` (`Ffin_left`, `Ffin_right`, `Ffin_supp`).
    For `null` the (32,3) state is `begin ∈ Q₊` and the head cell is plain; for `halt` it is
    `case_y_2 ∈ Q₋` and the head cell is the mark `mk case_y_2 u` (the reverse of (3,600)).
  * `readU g`: recover the (32,3) window around the head (`rec3`; padding and blanks both become
    the blank of (32,3)) and apply the (32,3) readout `U32_3.readL`; the kind of the head cell
    tells `halt` from `null`. It reads only the ID: no `N`, `C`, `w` (`readU_toID`,
    `readU_primrec`, `readU_of_shape`).
  * `isUTMStrict_U`: `IsUTMStrict U` by `ChainGen.isUTMStrict_of_ctsh`.
-/
import LeanUniv.Num3_659
import LeanUniv.U3_600

namespace URTM.Univ.U3_659
open URTM URTM.CTSH URTM.Gen.K32_3 URTM.Gen.T3_659 URTM.Univ.KToSpec URTM.Univ.NumGen
open URTM.Univ.ReadGen
open URTM.KState (Tgt Cfg Machine HaltsIn upd)
open URTM.SimLemmas (unhalt)
open URTM.Conv1W (VSt VSym isPlus)
open URTM.Conv3P (CSym)
open URTM.Conv510 (TSt)
open URTM.Univ.Sim3_659 (E659 fin659 n0 inv0 urtm3_659_simulates_ctsh)
open URTM.CTSH.U3_600 (f32 len32 len32_eq)
open URTM.CTSH.U32_3 (nm32 encC32 finCfg32)
open URTM.Univ.U10_8 (loN)
open URTM.Conv59 (mix mix_lt mix_ge)
open URTM.Conv55 (upd_eq upd_ne)
open URTM.Univ.U3_600 (sN qN vN cN num sN_lt qN_lt qN_q0 baseN baseN_plpl baseN_primrec
  map_baseN_replicate getD_rec drop_one_map_range getD_zeros_append tau_tp numCfg_rel fin32_read
  readL_primrec getD_le2 enc32_entries enc32_pos enc32_tape encList_left_length encList_right_length)

theorem q0_plus : isPlus T' St.q0 = true := by decide +kernel

theorem q2_minus : isPlus T' St.q2 = false := by decide +kernel

/-! ### The list-level encoder -/

/-- The (3,659) initial code from the (32,3) initial code `z = (_, l, r)`: state `L = 0`, the
    head on the blank left of the window; right of the head, the cells `y = 0, 1, …` of the (32,3)
    tape (the (32,3) head is at `y = |l|`) up to three cells beyond its right end, each
    as `pl (pl s) ↦ 1 + s`, except the cell `y = |l| - 1` left of the (32,3) head, which carries
    the mark `pl (mkp begin s) ↦ 100 + s`. -/
def enc3 (z : Spec.Code) : Spec.Code :=
  (0, [], 0 :: (List.range (z.2.1.length + z.2.2.length + 3)).map (fun y =>
        if y + 1 = z.2.1.length then 100 + z.2.1.getD 0 0
        else 1 + (if y < z.2.1.length then z.2.1.getD (z.2.1.length - 1 - y) 0
                  else z.2.2.getD (y - z.2.1.length) 0)))

/-- **Encoder** (list level). -/
def encList (C : CTSH) (w : List Ch) : Spec.Code := enc3 (U32_3.encList C w)

/-- The encoded initial configuration, unfolded. -/
theorem E659_eq (C : CTSH) (w : List Ch) :
    E659 C w = ⟨.go .L, 0, fun i => .pl (Conv1W.packV T' 0 (n0 C w) St.q0
      (encC32 C w).pos (encC32 C w).tape i)⟩ := by
  have hst : (encC32 C w).st = .go St.q0 := rfl
  simp only [E659, Conv3S.enc, Conv1W.Wc, hst, Conv1W.encV, Conv3P.enc]
  simp

/-- The tape of the encoder, cell by cell. -/
theorem enc_tape (C : CTSH) (w : List Ch) (j : ℤ) :
    (Spec.toID 0 (encList C w)).tape j =
      vN (Conv1W.packV T' 0 (n0 C w) St.q0 (encC32 C w).pos (encC32 C w).tape j) := by
  have hp := enc32_pos C w
  have hT := enc32_tape C w
  have hn : n0 C w = (U32_3.encList C w).2.1.length + (U32_3.encList C w).2.2.length + 3 := by
    rw [n0, len32_eq, encList_left_length, encList_right_length]
  simp only [Spec.toID] at hT
  simp only [Spec.toID, encList, enc3]
  generalize (U32_3.encList C w).2.1 = l at *
  generalize (U32_3.encList C w).2.2 = r at *
  by_cases hj : 1 ≤ j
  · obtain ⟨t, ht⟩ : ∃ t : ℕ, j = (t : ℤ) + 1 := ⟨(j - 1).toNat, by omega⟩
    rw [if_pos (by omega), show (j - 0).toNat = t + 1 by omega, List.getD_cons_succ,
      getD_map_range]
    by_cases htn : t < l.length + r.length + 3
    · rw [if_pos htn, Conv1W.packV_in (by omega) (by rw [hn]; omega)]
      by_cases hm : t + 1 = l.length
      · have hc : Conv1W.cell T' St.q0 (encC32 C w).pos (encC32 C w).tape (0 + j - 1) =
            .mkp St.q0 ((encC32 C w).tape (-1 + (encC32 C w).pos)) := by
          simp only [Conv1W.cell, Conv1W.mpos_plus q0_plus]
          rw [if_pos (by rw [hp]; omega), Conv1W.mark_plus q0_plus]
          congr 2
          rw [hp]; omega
        rw [hc, if_pos hm]
        simp only [vN, qN_q0]
        rw [hT (-1), if_neg (by omega), show ((0 : ℤ) - 1 - -1).toNat = 0 by omega]
      · have hc : Conv1W.cell T' St.q0 (encC32 C w).pos (encC32 C w).tape (0 + j - 1) =
            .pl ((encC32 C w).tape (((t : ℤ) - l.length) + (encC32 C w).pos)) := by
          simp only [Conv1W.cell, Conv1W.mpos_plus q0_plus]
          rw [if_neg (by rw [hp]; omega)]
          congr 2
          rw [hp]; omega
        rw [hc, if_neg hm]
        simp only [vN]
        rw [hT]
        by_cases hle : t < l.length
        · rw [if_pos hle, if_neg (by omega)]
          congr 2
          omega
        · rw [if_neg hle, if_pos (by omega)]
          congr 2
          omega
    · rw [if_neg htn, Conv1W.packV_out (.inr (by rw [hn]; omega))]
      simp [vN]
  · rw [Conv1W.packV_out (.inl (by omega))]
    by_cases h0 : 0 ≤ j
    · rw [if_pos h0, show (j - 0).toNat = 0 by omega]
      simp [vN]
    · rw [if_neg h0]
      simp [vN]

/-- The encoder is the numbered encoded initial configuration (head at Spec position 0). -/
theorem encList_eq (C : CTSH) (w : List Ch) :
    Spec.toID 0 (encList C w) = numCfg num 0 (E659 C w) := by
  rw [E659_eq]
  refine ID_ext rfl (by simp [Spec.toID, numCfg]) fun x => ?_
  rw [enc_tape]
  simp [numCfg, num, cN]

set_option maxRecDepth 100000 in
theorem U_syms : ∀ a ∈ [1, 2, 3, 100, 101, 102], a ∈ Spec.symbols U := by decide +kernel

set_option maxRecDepth 100000 in
theorem U_st0 : (0 : ℕ) ∈ Spec.states U := by decide +kernel

/-- The encoded initial ID is an ID of U (`c(n, α) ∈ ID(U)` of Morita Def. 7.1). -/
theorem isIDOf_encList (C : CTSH) (w : List Ch) : Spec.IsIDOf U (Spec.toID 0 (encList C w)) := by
  obtain ⟨hl, hr⟩ := enc32_entries C w
  refine isIDOf_toID U 0 _ U_st0 fun a ha => ?_
  simp only [encList, enc3, List.nil_append, List.mem_cons, List.mem_map, List.mem_range] at ha
  rcases ha with rfl | ⟨t, -, rfl⟩
  · exact .inl rfl
  · refine .inr (U_syms _ ?_)
    have h0 := getD_le2 _ hl 0
    have h1 := getD_le2 _ hl ((U32_3.encList C w).2.1.length - 1 - t)
    have h2 := getD_le2 _ hr (t - (U32_3.encList C w).2.1.length)
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    split_ifs <;> omega

open Primrec in
theorem enc3_primrec : Primrec enc3 := by
  have l : Primrec fun p : Spec.Code × ℕ => p.1.2.1 := fst.comp (snd.comp fst)
  have r : Primrec fun p : Spec.Code × ℕ => p.1.2.2 := snd.comp (snd.comp fst)
  have t : Primrec fun p : Spec.Code × ℕ => p.2 := snd
  have ll : Primrec fun p : Spec.Code × ℕ => p.1.2.1.length := list_length.comp l
  have G := list_getD (0 : ℕ)
  have hf : Primrec₂ fun (z : Spec.Code) (y : ℕ) =>
      if y + 1 = z.2.1.length then 100 + z.2.1.getD 0 0
      else 1 + (if y < z.2.1.length then z.2.1.getD (z.2.1.length - 1 - y) 0
                else z.2.2.getD (y - z.2.1.length) 0) :=
    (Primrec.ite (Primrec.eq.comp (succ.comp t) ll)
      (nat_add.comp (const 100) (G.comp l (const 0)))
      (nat_add.comp (const 1) (Primrec.ite (nat_lt.comp t ll)
        (G.comp l (nat_sub.comp (nat_sub.comp ll (const 1)) t))
        (G.comp r (nat_sub.comp t ll))))).to₂
  exact pair (const 0) (pair (const []) (list_cons.comp (const 0)
    (list_map (list_range.comp (nat_add.comp (nat_add.comp
      (list_length.comp (fst.comp snd)) (list_length.comp (snd.comp snd))) (const 3))) hf)))

theorem encList_primrec : Primrec₂ encList := enc3_primrec.comp₂ U32_3.encList_primrec

/-! ### The readout -/

/-- The (32,3) symbol shown by the content `x` of a counter symbol `ct x k` (number `c`):
    `pl s ↦ 1 + s` and the marks `mk p s ↦ 4 + 3p + s`, `mkp p s ↦ 100 + 3p + s` give `s`. -/
def headSym (c : ℕ) : ℕ := if 4 ≤ c % 196 then (c % 196 - 4) % 3 else c % 196 - 1

/-- The (32,3) symbol carried by the state of the one-way-updating machine with index `k`
    (`c s` and `g p v` carry the cell left of the (32,3) head). -/
def carry (k : ℕ) : ℕ :=
  match numf k with
  | .c s => sN s
  | .g _ v => sN v
  | _ => 0

/-- The (32,3) window (left end first) recovered from the two lists `(l, r)` of a (3,659) code:
    left of the head the (32,3) cells up to two left of its head; the head cell `ct x k` gives the
    cell left of the (32,3) head (carried by `k`) and the (32,3) head cell (from `x`); right of the
    head the (32,3) cells as they are. -/
def rec3 (l r : List ℕ) : List ℕ :=
  (l.map baseN).reverse ++
    carry (r.getD 0 0 / 196 - 1) :: headSym (r.getD 0 0) :: (r.drop 1).map baseN

/-- The (32,3) pseudo-state: the head cell `ct (pl u) _` (`x ≤ 3`) means `null = 32`, a head
    cell `ct (mk case_y_2 u) _` means `halt = 33`. -/
def qOf (r : List ℕ) : ℕ := if r.getD 0 0 % 196 ≤ 3 then 32 else 33

/-- **Readout** (list level) from a code `g` of the halting ID: `(|C|, ϕ₁(vf))`, by the (32,3)
    readout on the recovered (32,3) window. It does not look at the number of steps. -/
def readU (g : Spec.Code) : Option (ℕ × List ℕ) :=
  some (U32_3.readL 33 (qOf g.2.2) (rec3 g.2.1 g.2.2))

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
theorem readU_primrec : Primrec readU := by
  have l : Primrec fun g : Spec.Code => g.2.1 := fst.comp snd
  have r : Primrec fun g : Spec.Code => g.2.2 := snd.comp snd
  have c : Primrec fun g : Spec.Code => g.2.2.getD 0 0 := (list_getD 0).comp r (const 0)
  have vx : Primrec fun g : Spec.Code => g.2.2.getD 0 0 % 196 := nat_mod.comp c (const 196)
  have u : Primrec fun g : Spec.Code => headSym (g.2.2.getD 0 0) :=
    (Primrec.ite (nat_le.comp (const 4) vx) (nat_mod.comp (nat_sub.comp vx (const 4)) (const 3))
      (nat_sub.comp vx (const 1))).of_eq fun _ => rfl
  have cr : Primrec fun g : Spec.Code => carry (g.2.2.getD 0 0 / 196 - 1) :=
    carry_primrec.comp (nat_sub.comp (nat_div.comp c (const 196)) (const 1))
  have hrec : Primrec fun g : Spec.Code => rec3 g.2.1 g.2.2 :=
    list_append.comp (list_reverse.comp (list_map l (baseN_primrec.comp snd).to₂))
      (list_cons.comp cr (list_cons.comp u
        (list_map (list_drop.comp (const 1) r) (baseN_primrec.comp snd).to₂)))
  have hq : Primrec fun g : Spec.Code => qOf g.2.2 :=
    Primrec.ite (nat_le.comp vx (const 3)) (const 32) (const 33)
  exact option_some.comp (readL_primrec.comp (pair hq hrec))

/-! ### The final configurations (typed) -/

/-- The final configuration of (3,659) for a halting configuration `(p, x, t)` of `T'`
    (the (32,3) configuration just before its halting quintuple), with the window `[a, a + n)`
    of the one-way-updating machine (`fin659_Ffin`). -/
def Ffin (a : ℤ) (n : ℕ) (p : St) (x : ℤ) (t : ℤ → Sy) : Cfg TSt Ps (CSym (VSym St Sy)) :=
  { st := .go .R0, pos := x - a + 1,
    tape := upd (fun i => .pl (mix (x - a + 1) (Conv1W.packV T' (a - 1) n p x t)
        (Conv1W.packV T' a n p x t) i)) (x - a + 1)
      (.ct (mix (x - a + 1) (Conv1W.packV T' (a - 1) n p x t) (Conv1W.packV T' a n p x t)
          (x - a + 1))
        (idx (if isPlus T' p then .g p (t (x - 1)) else .c (t (x - 1))))) }

/-- The final configuration of `Sim3_659`, unfolded. -/
theorem fin659_Ffin (C : CTSH) (w : List Ch) (vf : List Ch) (mf : ℕ) (rm : List Ch) (N : ℕ)
    {p : St} (hp : (unhalt f32 (finCfg32 C vf mf rm)).st = .go p) :
    fin659 C w vf mf rm N = Ffin (0 - N) (n0 C w + 2 * N) p
      (unhalt f32 (finCfg32 C vf mf rm)).pos (unhalt f32 (finCfg32 C vf mf rm)).tape := by
  simp only [fin659, Conv3S.fin, Conv1W.Ev, hp, Conv1W.haltV, Conv3P.enc]
  rw [if_neg (by split <;> nofun)]
  rfl

theorem numf_idx (q : VSt St Sy) : numf (idx q) = q := dec_idx q (allVSt_all q)

section Fin
variable {a : ℤ} {n : ℕ} {p : St} {x : ℤ} {t : ℤ → Sy}

/-- The head cell of the final configuration. -/
theorem Ffin_head :
    (Ffin a n p x t).tape (Ffin a n p x t).pos =
      .ct (Conv1W.packV T' a n p x t (x - a + 1))
        (idx (if isPlus T' p then .g p (t (x - 1)) else .c (t (x - 1)))) := by
  simp only [Ffin]
  rw [upd_eq, mix_ge (Int.le_refl _)]

/-- The head cell, when `p` is in `Q₋` (entered by left moves): the mark `mk p u` with the counter
    of `c s`. -/
theorem Ffin_head_minus (hI : Conv1W.Inv T' Sy.s0 Gl a n p x t) (hp : isPlus T' p = false) :
    (Ffin a n p x t).tape (Ffin a n p x t).pos = .ct (.mk p (t x)) (idx (.c (t (x - 1)))) := by
  have hlo := hI.lo
  have hhi := hI.hi
  rw [Ffin_head, Conv1W.packV_mk (by omega) (by omega) (by rw [Conv1W.mpos_minus hp]; omega),
    Conv1W.mark_minus hp, show a + (x - a + 1) - 1 = x by omega]
  simp only [hp, Bool.false_eq_true, if_false]

/-- The head cell, when `p` is in `Q₊` (entered by right moves): the plain symbol with the counter
    of `g p v`. -/
theorem Ffin_head_plus (hI : Conv1W.Inv T' Sy.s0 Gl a n p x t) (hp : isPlus T' p = true) :
    (Ffin a n p x t).tape (Ffin a n p x t).pos = .ct (.pl (t x)) (idx (.g p (t (x - 1)))) := by
  have hlo := hI.lo
  have hhi := hI.hi
  rw [Ffin_head, Conv1W.packV_pl (by omega) (by omega) (by rw [Conv1W.mpos_plus hp]; omega),
    show a + (x - a + 1) - 1 = x by omega]
  simp only [hp, if_true]

/-- Left of the head: the (32,3) cells shifted by one (the cell left of the head is carried by the
    state index). -/
theorem Ffin_left (hI : Conv1W.Inv T' Sy.s0 Gl a n p x t) (d : ℤ) (hd : d < 0) :
    baseN (cN ((Ffin a n p x t).tape ((Ffin a n p x t).pos + d))) = sN (t (x + d - 1)) := by
  have hlo := hI.lo
  have hhi := hI.hi
  simp only [Ffin]
  rw [upd_ne _ _ (by omega), mix_lt (by omega)]
  by_cases hin : 1 ≤ x - a + 1 + d
  · rw [Conv1W.packV_pl hin (by omega) (by simp only [Conv1W.mpos]; split <;> omega), baseN_plpl]
    congr 2
    omega
  · rw [Conv1W.packV_out (.inl (by omega)), hI.out (x + d - 1) (.inl (by omega))]
    rfl

/-- Right of the head: the (32,3) cells as they are. -/
theorem Ffin_right (hI : Conv1W.Inv T' Sy.s0 Gl a n p x t) (d : ℤ) (hd : 1 ≤ d) :
    baseN (cN ((Ffin a n p x t).tape ((Ffin a n p x t).pos + d))) = sN (t (x + d)) := by
  have hlo := hI.lo
  have hhi := hI.hi
  simp only [Ffin]
  rw [upd_ne _ _ (by omega), mix_ge (by omega)]
  by_cases hin : x - a + 1 + d ≤ n
  · rw [Conv1W.packV_pl (by omega) hin (by simp only [Conv1W.mpos]; split <;> omega), baseN_plpl]
    congr 2
    omega
  · rw [Conv1W.packV_out (.inr (by omega)), hI.out (x + d) (.inr (by omega))]
    rfl

/-- The tape is blank outside a finite window around the head. -/
theorem Ffin_supp (hI : Conv1W.Inv T' Sy.s0 Gl a n p x t) (d : ℤ)
    (hd : d < a - x ∨ n + a - x - 1 < d) :
    (Ffin a n p x t).tape ((Ffin a n p x t).pos + d) = .pl .bl := by
  have hlo := hI.lo
  have hhi := hI.hi
  simp only [Ffin]
  rw [upd_ne _ _ (by omega)]
  rcases hd with hd | hd
  · rw [mix_lt (by omega), Conv1W.packV_out (.inl (by omega))]
  · rw [mix_ge (by omega), Conv1W.packV_out (.inr (by omega))]

end Fin

/-! ### Reading the final ID -/

/-- **Reading a final ID from its description relative to the head.** `τ` is the numbered (32,3)
    tape (the list `L`), `P` the (32,3) head position; the head cell of `γ` is a counter symbol
    whose content gives `τ P` and whose index carries `τ (P - 1)`; right of the head `γ` shows
    the (32,3) cells as they are, left of the head the (32,3) cells shifted by one; `γ` is blank
    outside a window. Then some code of `γ` is read as the (32,3) readout of `L`. -/
theorem readU_of_shape (γ : Spec.ID) (τ : ℤ → ℕ) (P : ℕ) (L : List ℕ) (halt : Bool)
    (k mL mR : ℕ)
    (hτ : ∀ y : ℤ, τ y = if 0 ≤ y then L.getD y.toNat 0 else 0) (hτ3 : ∀ y, τ y < 3)
    (hhead : γ.tape γ.pos = 196 * (k + 1) + ((if halt then 4 + 3 * qN St.q2 else 1) + τ P))
    (hcarry : carry k = τ ((P : ℤ) - 1))
    (hleft : ∀ d : ℤ, d < 0 → baseN (γ.tape (γ.pos + d)) = τ (P + d - 1))
    (hright : ∀ d : ℤ, 1 ≤ d → baseN (γ.tape (γ.pos + d)) = τ (P + d))
    (hsupp : ∀ d : ℤ, (d < -(mL : ℤ) ∨ (mR : ℤ) < d) → γ.tape (γ.pos + d) = 0) :
    ∃ g, Spec.toID γ.pos g = γ ∧
      readU g = some (U32_3.readL 33 (if halt then 33 else 32) L) := by
  refine ⟨codeOf γ (mL + P) (mR + L.length + 1), toID_codeOf γ _ _ (fun x hx => ?_), ?_⟩
  · have := hsupp (x - γ.pos) (by push_cast at hx; omega)
    rwa [show γ.pos + (x - γ.pos) = x by omega] at this
  · have h3 := hτ3 P
    have hq2 := qN_lt St.q2
    have hv : (if halt then 4 + 3 * qN St.q2 else 1) + τ P < 196 := by split <;> omega
    have hc : (codeOf γ (mL + P) (mR + L.length + 1)).2.2.getD 0 0 =
        196 * (k + 1) + ((if halt then 4 + 3 * qN St.q2 else 1) + τ P) := by
      simp only [codeOf]
      rw [getD_map_range, if_pos (by omega)]
      simpa using hhead
    have hmod : (codeOf γ (mL + P) (mR + L.length + 1)).2.2.getD 0 0 % 196 =
        (if halt then 4 + 3 * qN St.q2 else 1) + τ P := by
      rw [hc, Nat.mul_add_mod, Nat.mod_eq_of_lt hv]
    have hdiv : (codeOf γ (mL + P) (mR + L.length + 1)).2.2.getD 0 0 / 196 - 1 = k := by
      rw [hc, Nat.mul_add_div (by decide), Nat.div_eq_of_lt hv]
      omega
    have hq : qOf (codeOf γ (mL + P) (mR + L.length + 1)).2.2 = if halt then 33 else 32 := by
      simp only [qOf, hmod]
      cases halt <;> simp <;> omega
    have hu : headSym ((codeOf γ (mL + P) (mR + L.length + 1)).2.2.getD 0 0) = τ P := by
      simp only [headSym, hmod]
      cases halt
      · simp only [Bool.false_eq_true, if_false]
        rw [if_neg (by omega)]
        omega
      · simp only [if_true]
        rw [if_pos (by omega)]
        omega
    have hT : ∀ i : ℕ, (List.replicate (mL + 1) 0 ++ L).getD i 0 = τ ((i : ℤ) - mL - 1) := by
      intro i
      rw [getD_zeros_append, hτ]
      by_cases h : i < mL + 1
      · rw [if_pos h, if_neg (by omega)]
      · rw [if_neg h, if_pos (by omega)]
        congr 1
        omega
    have hrec : ∀ i, (rec3 (codeOf γ (mL + P) (mR + L.length + 1)).2.1
        (codeOf γ (mL + P) (mR + L.length + 1)).2.2).getD i 0 =
        (List.replicate (mL + 1) 0 ++ L).getD i 0 := by
      intro i
      have hfa : ∀ j : ℕ, j < mL + P →
          baseN (γ.tape (γ.pos - 1 - ((mL + P - 1 - j : ℕ) : ℤ))) = τ ((j : ℤ) - mL - 1) := by
        intro j hj
        have e : γ.pos - 1 - ((mL + P - 1 - j : ℕ) : ℤ) = γ.pos + ((j : ℤ) - (mL + P)) := by
          omega
        rw [e, hleft _ (by omega)]
        congr 1
        omega
      have hfb : ∀ j : ℕ, baseN (γ.tape (γ.pos + ((j + 1 : ℕ) : ℤ))) = τ ((P : ℤ) + j + 1) := by
        intro j
        rw [hright _ (by omega)]
        congr 1
      rw [hT]
      simp only [rec3, hdiv, hu, hcarry]
      simp only [codeOf, List.map_map, drop_one_map_range]
      rw [getD_rec]
      simp only [Function.comp_apply]
      by_cases h1 : i < mL + P
      · rw [if_pos h1, hfa i h1]
      · rw [if_neg h1]
        by_cases h2 : i = mL + P
        · rw [if_pos h2]
          congr 1
          omega
        · rw [if_neg h2]
          by_cases h3' : i = mL + P + 1
          · rw [if_pos h3']
            congr 1
            omega
          · rw [if_neg h3']
            by_cases h4 : i < mL + P + 2 + (mR + L.length)
            · rw [if_pos h4, hfb]
              congr 1
              omega
            · rw [if_neg h4, hτ, if_pos (by omega), List.getD_eq_default _ _ (by omega)]
    obtain ⟨M, j1, j2, e1, e2⟩ := Spec.CodePad.pad_of_getD _ _ hrec
    simp only [readU, hq]
    rw [e1, U32_3.readL_padR, ← U32_3.readL_padL 33 _ (mL + 1) L, e2, U32_3.readL_padR]

/-! ### The final configurations, numbered -/

theorem carry_c (s : Sy) : carry (idx (.c s)) = sN s := by
  simp only [carry, numf_idx]

theorem carry_g (p : St) (v : Sy) : carry (idx (.g p v)) = sN v := by
  simp only [carry, numf_idx]

/-- **Reading the final configuration of (3,659)** for a halting configuration `(p, P, L)` of
    `T'` on a list tape, in the two cases of the head cell. -/
theorem read_Ffin (a : ℤ) (n : ℕ) (p : St) (P : ℕ) (L : List Sy)
    (hI : Conv1W.Inv T' Sy.s0 Gl a n p (P : ℤ) (Sim.tp Sy.s0 L))
    (halt : Bool) (k : ℕ)
    (hhead : cN ((Ffin a n p P (Sim.tp Sy.s0 L)).tape (Ffin a n p P (Sim.tp Sy.s0 L)).pos) =
      196 * (k + 1) + ((if halt then 4 + 3 * qN St.q2 else 1) + sN (Sim.tp Sy.s0 L P)))
    (hcarry : carry k = sN (Sim.tp Sy.s0 L ((P : ℤ) - 1))) :
    ∃ g, Spec.toID (numCfg num 0 (Ffin a n p P (Sim.tp Sy.s0 L))).pos g =
        numCfg num 0 (Ffin a n p P (Sim.tp Sy.s0 L)) ∧
      readU g = some (U32_3.readL 33 (if halt then 33 else 32) (L.map sN)) := by
  have hlo := hI.lo
  have hhi := hI.hi
  refine readU_of_shape _ (fun y => sN (Sim.tp Sy.s0 L y)) P (L.map sN) halt k
    ((P : ℤ) - a).toNat ((n : ℤ) + a - P - 1).toNat (tau_tp L) (fun y => sN_lt _) ?_ hcarry
    (fun d hd => ?_) (fun d hd => ?_) (fun d hd => ?_)
  · have := numCfg_rel 0 (Ffin a n p P (Sim.tp Sy.s0 L)) 0
    rw [Int.add_zero, Int.add_zero] at this
    rw [this, hhead]
  · rw [numCfg_rel, Ffin_left hI d hd]
  · rw [numCfg_rel, Ffin_right hI d hd]
  · rw [numCfg_rel, Ffin_supp hI d (by omega)]
    rfl

/-! ### The run-level simulation and the main theorem -/

/-- **URTM(3,659) simulates every CTSH at the level of Spec** (run level, exact readback). -/
theorem runSim_U (C : CTSH) (w : List Ch) :
    RunSim (CStep C) (Halting C) (Spec.Step U) (Spec.Halted U)
      (fun y γ => ∃ g, Spec.toID γ.pos g = γ ∧ readU g = some (C.length, y.1.map loN))
      (w, 0) (Spec.toID 0 (encList C w)) := by
  rw [encList_eq]
  obtain ⟨-, -, -, -, -, -, -, hF, -, hN⟩ := urtm3_659_simulates_ctsh C w
  refine runSim_of_sim num T3py 0 C w (E659 C w)
    (fun f c => ∃ rm N, HaltsIn T' N (encC32 C w) (unhalt f32 (finCfg32 C f.1 f.2 rm)) ∧
      c = fin659 C w f.1 f.2 rm N) _
    (fun m f hf => ?_) (fun hn => hN.mp hn) (fun f c hf hc => ?_)
  · obtain ⟨N, M, rm, -, hT, hM⟩ := hF m f.1 f.2 hf
    exact ⟨M, _, hM, rm, N, hT, rfl⟩
  · obtain ⟨rm, N, hT, rfl⟩ := hc
    obtain ⟨vf, mf⟩ := f
    obtain ⟨h, L, P, hfin, hrd⟩ := fin32_read C vf mf rm hf
    have he : unhalt f32 (finCfg32 C vf mf rm) = ⟨.go (f32 h), (P : ℤ), Sim.tp .s0 L⟩ := by
      rw [hfin]; rfl
    -- the invariant of the one-way-updating run
    obtain ⟨⟨p, hp, hI⟩, -⟩ := Conv1W.run_sim (Conv3S.hyp1W hyp) (c0 := encC32 C w)
      (p0 := .q0) rfl (inv0 C w) N hT.1
    rw [he] at hp hI
    have hpp : f32 h = p := Tgt.go.inj hp
    subst hpp
    have hF659 : fin659 C w vf mf rm N =
        Ffin (0 - N) (n0 C w + 2 * N) (f32 h) (P : ℤ) (Sim.tp .s0 L) := by
      have := fin659_Ffin C w vf mf rm N (p := f32 h) (by rw [he])
      rw [he] at this
      exact this
    simp only [hF659]
    cases h with
    | h0 =>
      -- null: `begin` is in Q₊; the head cell is plain
      have hh := Ffin_head_plus hI q0_plus
      obtain ⟨g, hg, hr⟩ := read_Ffin _ _ _ P L hI false
        (idx (.g St.q0 (Sim.tp .s0 L ((P : ℤ) - 1))))
        (by rw [hh]; simp only [cN, vN, f32]; simp) (carry_g _ _)
      exact ⟨g, hg, by rw [hr]; exact congrArg some hrd⟩
    | h1 =>
      -- halt: `case_y_2` is in Q₋; the head cell is the mark `mk case_y_2 u`
      have hh := Ffin_head_minus hI q2_minus
      obtain ⟨g, hg, hr⟩ := read_Ffin _ _ _ P L hI true (idx (.c (Sim.tp .s0 L ((P : ℤ) - 1))))
        (by rw [hh]; simp only [cN, vN, f32]; simp) (carry_c _)
      exact ⟨g, hg, by rw [hr]; exact congrArg some hrd⟩

/-- **URTM(3,659) is a UTM in the strict sense of Morita Def. 7.1.** -/
theorem isUTMStrict_U : Spec.IsUTMStrict U :=
  ChainGen.isUTMStrict_of_ctsh U encList readU encList_primrec readU_primrec isIDOf_encList
    runSim_U (fun _ _ _ h => readU_toID h)

end URTM.Univ.U3_659
