/-
  **The 18476-symbol three-state machine: encoder, readout, and universality in the sense of
  Def. 7.1.**

  The machine `K = Conv3P.conv That .L .bl idx3 (fun _ => 61) allW` (`Num3_18476.lean`) is the
  three-state conversion, with every counter kept, of Morita's one-way-updating machine `That`
  (Lemma 5.9) of (32,3) without its halting quintuples. A cell of `That` packs two cells of (32,3):
  `pr s t`, or `hp p s t` for the pair that holds the (32,3) head (state `p`), or the blank `bl`.
  The CTSH simulation is `CTSH.U3_18476.urtm3_18476_simulates_ctsh`.

  * `encList C w`: the Spec code of the initial configuration `E18476 C w (n0 C w)`, computed from
    the (32,3) initial code `z = (_, l, r)` (`enc18`): state `L`, the head on the blank at `0`;
    right of it the pairs of (32,3) cells `(2j, 2j + 1)`, `j < |l| + |r| + 3`, each
    `pr s t ↦ 1 + 3s + t`, except the pair of the (32,3) head (`2j = |l|`, state `begin = q0`),
    `hp q0 s t ↦ 10 + 3s + t` (`encList_eq`).
  * The halting configurations have one of two shapes (`Conv59.E`): if (32,3) halts after `N ≥ 1`
    steps, `h(s0)` reads the blank right of the pairs, so the head cell is the counter `ct bl k` and
    all pairs lie left of the head (`read_haltW`); if `N = 0`, the sweep stops at the pair of the
    head, which is the head cell `ct (hp p s t) k`; the pairs left of it are shifted by one cell of
    (32,3) and the cell in between is carried by the state index `k` (`read_immW`).
  * `readU g`: unpack every cell of the window into its two (32,3) cells (`pa`, `pb`), insert
    the cell carried by the counter of the head cell (`carry`; it is `0` in the first shape, where
    it falls on blank cells), read the (32,3) state from the `hp` cell (`qOf`), and apply the
    (32,3) readout `U32_3.readL`. It reads only the ID: no `N`, `C`, `w` (`readU_toID`,
    `readU_primrec`, `readU_of_shape`).
  * `isUTMStrict_U`: `IsUTMStrict U` by `ChainGen.isUTMStrict_of_ctsh`.
  No `sorry`, no new axiom, no `native_decide`.
-/
import LeanUniv.Num3_18476
import LeanUniv.U3_600

namespace URTM.Univ.U3_18476
open URTM URTM.CTSH URTM.Gen.K32_3 URTM.Univ.KToSpec URTM.Univ.NumGen URTM.Univ.NumCount
open URTM.Univ.ReadGen
open URTM.KState (Tgt Cfg Machine HaltsIn StepN Step upd fire)
open URTM.SimLemmas (unhalt)
open URTM.Conv59 (WSt WSym pack mix mix_lt mix_ge pack_out pack_pr pack_hp)
open URTM.Conv3P (CSym)
open URTM.Conv510 (TSt)
open URTM.Conv55 (upd_eq upd_ne)
open URTM.CTSH.U3_36654 (T32' That allW allW_all idx3 cS cQ cW hyp59 inv0 f32)
open URTM.CTSH.U32_3 (nm32 encC32 finCfg32)
open URTM.CTSH.U3_600 (len32 len32_eq)
open URTM.Univ.U10_8 (loN)
open URTM.Univ.U3_600 (sN qN getD_zeros_append tau_tp fin32_read readL_primrec
  enc32_pos enc32_tape encList_left_length encList_right_length drop_one_map_range)

/-! ### The window of the initial configuration -/

/-- The number of pairs of the initial configuration. -/
def n0 (C : CTSH) (w : List Ch) : ℕ := len32 C w + 3

theorem hn0 (C : CTSH) (w : List Ch) :
    (URTM.CTSH.U32_3.RA nm32 C 0).length + 6 ≤ 2 * n0 C w ∧
      (URTM.CTSH.U32_3.tapeList nm32 C 0 [] w).length + 1 ≤ 2 * n0 C w := by
  have h1 := len32_eq C w
  have h2 : (URTM.CTSH.U32_3.tapeList nm32 C 0 [] w).length = len32 C w := rfl
  simp only [n0]
  omega

/-! ### The list-level encoder -/

/-- The (32,3) cell `y ≥ 0` of the (32,3) code `z = (_, l, r)` (the head at `y = |l|`). -/
def cell (z : Spec.Code) (y : ℕ) : ℕ :=
  if y < z.2.1.length then z.2.1.getD (z.2.1.length - 1 - y) 0 else z.2.2.getD (y - z.2.1.length) 0

/-- The initial code from the (32,3) initial code `z`: state `L = 0`, the head on the blank at `0`;
    right of it the pairs `(2j, 2j + 1)` of (32,3) cells for `j < |l| + |r| + 3`, as
    `pr s t ↦ 1 + 3s + t`, except the pair of the (32,3) head (`2j = |l|`), `hp begin s t ↦ 10 + 3s + t`. -/
def enc18 (z : Spec.Code) : Spec.Code :=
  (0, [], 0 :: (List.range (z.2.1.length + z.2.2.length + 3)).map (fun j =>
    (if 2 * j = z.2.1.length then 10 else 1) + 3 * cell z (2 * j) + cell z (2 * j + 1)))

/-- **Encoder** (list level). -/
def encList (C : CTSH) (w : List Ch) : Spec.Code := enc18 (U32_3.encList C w)

theorem cell_eq (C : CTSH) (w : List Ch) (y : ℕ) :
    cell (U32_3.encList C w) y = sN ((encC32 C w).tape (y : ℤ)) := by
  have hp := enc32_pos C w
  have hT := enc32_tape C w ((y : ℤ) - (U32_3.encList C w).2.1.length)
  rw [hp, show (y : ℤ) - ((U32_3.encList C w).2.1.length : ℤ) +
      ((U32_3.encList C w).2.1.length : ℤ) = y by omega] at hT
  rw [hT]
  simp only [Spec.toID, cell]
  by_cases h : y < (U32_3.encList C w).2.1.length
  · rw [if_pos h, if_neg (by omega)]
    congr 1
    omega
  · rw [if_neg h, if_pos (by omega)]
    congr 1
    omega

/-- The encoded initial configuration, unfolded. -/
theorem E_eq (C : CTSH) (w : List Ch) :
    URTM.CTSH.U3_18476.E18476 C w (n0 C w) =
      ⟨.go .L, 0, fun i => .pl (pack 0 (n0 C w) St.q0 (encC32 C w).pos (encC32 C w).tape i)⟩ := by
  have hst : (encC32 C w).st = .go St.q0 := rfl
  simp only [URTM.CTSH.U3_18476.E18476, Conv59.W, hst, Conv59.encW, Conv3P.enc]
  simp

theorem cQ_q0 : cQ St.q0 = 0 := by decide

/-- The tape of the encoder, cell by cell. -/
theorem enc_tape (C : CTSH) (w : List Ch) (j : ℤ) :
    (Spec.toID 0 (encList C w)).tape j =
      cW (pack 0 (n0 C w) St.q0 (encC32 C w).pos (encC32 C w).tape j) := by
  have hp := enc32_pos C w
  have hn : n0 C w = (U32_3.encList C w).2.1.length + (U32_3.encList C w).2.2.length + 3 := by
    rw [n0, len32_eq, encList_left_length, encList_right_length]
  simp only [Spec.toID, encList, enc18]
  by_cases hj : 1 ≤ j
  · obtain ⟨t, rfl⟩ : ∃ t : ℕ, j = (t : ℤ) + 1 := ⟨(j - 1).toNat, by omega⟩
    rw [if_pos (by omega), show ((t : ℤ) + 1 - 0).toNat = t + 1 by omega, List.getD_cons_succ,
      getD_map_range]
    by_cases ht : t < (U32_3.encList C w).2.1.length + (U32_3.encList C w).2.2.length + 3
    · rw [if_pos ht]
      have e0 : (0 : ℤ) + 2 * ((t : ℤ) + 1 - 1) = ((2 * t : ℕ) : ℤ) := by push_cast; omega
      by_cases hm : 2 * t = (U32_3.encList C w).2.1.length
      · rw [if_pos hm, pack_hp (by omega) (by rw [hn]; omega) (by rw [hp]; omega)]
        have e1 : (encC32 C w).pos = ((2 * t : ℕ) : ℤ) := by rw [hp]; omega
        have e2 : (encC32 C w).pos + 1 = ((2 * t + 1 : ℕ) : ℤ) := by rw [hp]; push_cast; omega
        rw [cell_eq, cell_eq, e2, e1]
        simp only [cW, cQ_q0, cS_sN]
      · rw [if_neg hm, pack_pr (by omega) (by rw [hn]; omega) (by rw [hp]; omega), e0]
        rw [cell_eq, cell_eq]
        simp only [cW, cS_sN]
        push_cast
        omega
    · rw [if_neg ht, pack_out (.inr (by rw [hn]; omega))]
      rfl
  · rw [pack_out (.inl (by omega))]
    by_cases h0 : 0 ≤ j
    · rw [if_pos h0, show (j - 0).toNat = 0 by omega]
      rfl
    · rw [if_neg h0]
      rfl

/-- The encoder is the numbered encoded initial configuration (head at Spec position 0). -/
theorem encList_eq (C : CTSH) (w : List Ch) :
    Spec.toID 0 (encList C w) = numCfg num 0 (URTM.CTSH.U3_18476.E18476 C w (n0 C w)) := by
  rw [E_eq]
  refine ID_ext rfl (by simp [Spec.toID, numCfg]) fun x => ?_
  rw [enc_tape]
  simp [numCfg, num, cN]

theorem U_st0 : (0 : ℕ) ∈ Spec.states U := by
  have := mem_states_numT num (mem_d8 (x := .pr .s0 .s0) (by decide))
  rw [U]
  exact this

/-- Every cell of `That` is blank or, as a plain symbol, a symbol of `U` (read by δ8). -/
theorem cW_sym (x : WSym St Sy) : cW x = 0 ∨ cW x ∈ Spec.symbols U := by
  by_cases hx : x = .bl
  · left
    rw [hx]
    rfl
  · right
    have := mem_symbols_numT num (mem_d8 hx)
    rw [U]
    exact this

/-- The encoded initial ID is an ID of U (`c(n, α) ∈ ID(U)` of Morita Def. 7.1). -/
theorem isIDOf_encList (C : CTSH) (w : List Ch) : Spec.IsIDOf U (Spec.toID 0 (encList C w)) :=
  ⟨toID_finite 0 _, U_st0, fun x => by rw [enc_tape]; exact cW_sym _⟩

open Primrec in
theorem cell_primrec : Primrec₂ cell := by
  have l : Primrec fun p : Spec.Code × ℕ => p.1.2.1 := fst.comp (snd.comp fst)
  have r : Primrec fun p : Spec.Code × ℕ => p.1.2.2 := snd.comp (snd.comp fst)
  have t : Primrec fun p : Spec.Code × ℕ => p.2 := snd
  have ll : Primrec fun p : Spec.Code × ℕ => p.1.2.1.length := list_length.comp l
  have G := list_getD (0 : ℕ)
  exact (Primrec.ite (nat_lt.comp t ll) (G.comp l (nat_sub.comp (nat_sub.comp ll (const 1)) t))
    (G.comp r (nat_sub.comp t ll))).to₂

open Primrec in
theorem enc18_primrec : Primrec enc18 := by
  have t : Primrec fun p : Spec.Code × ℕ => p.2 := snd
  have z : Primrec fun p : Spec.Code × ℕ => p.1 := fst
  have ll : Primrec fun p : Spec.Code × ℕ => p.1.2.1.length := list_length.comp (fst.comp (snd.comp fst))
  have t2 : Primrec fun p : Spec.Code × ℕ => 2 * p.2 := nat_mul.comp (const 2) t
  have hf : Primrec₂ fun (z : Spec.Code) (j : ℕ) =>
      (if 2 * j = z.2.1.length then 10 else 1) + 3 * cell z (2 * j) + cell z (2 * j + 1) :=
    (nat_add.comp (nat_add.comp (Primrec.ite (Primrec.eq.comp t2 ll) (const 10) (const 1))
      (nat_mul.comp (const 3) (cell_primrec.comp z t2)))
      (cell_primrec.comp z (nat_add.comp t2 (const 1)))).to₂
  exact pair (const 0) (pair (const []) (list_cons.comp (const 0)
    (list_map (list_range.comp (nat_add.comp (nat_add.comp
      (list_length.comp (fst.comp snd)) (list_length.comp (snd.comp snd))) (const 3))) hf)))

theorem encList_primrec : Primrec₂ encList := enc18_primrec.comp₂ U32_3.encList_primrec

/-! ### The readout -/

/-- The first (32,3) cell of a cell of `K` (its counter dropped): `pr s t ↦ s`, `hp p s t ↦ s`,
    blank `↦ 0`. -/
def pa (c : ℕ) : ℕ :=
  if c % 298 = 0 then 0 else if c % 298 < 10 then (c % 298 - 1) / 3 else (c % 298 - 10) % 9 / 3

/-- The second (32,3) cell of a cell of `K`: `pr s t ↦ t`, `hp p s t ↦ t`, blank `↦ 0`. -/
def pb (c : ℕ) : ℕ :=
  if c % 298 = 0 then 0 else if c % 298 < 10 then (c % 298 - 1) % 3 else (c % 298 - 10) % 3

/-- The (32,3) cell carried by the state `q(s)` of `That` with index `k` (`0` for any other index). -/
def carry (k : ℕ) : ℕ := if k = idx3 (.q .s1) then 1 else if k = idx3 (.q .s2) then 2 else 0

/-- Every cell unpacked into its two (32,3) cells. -/
def unpk (l : List ℕ) : List ℕ := l.flatMap fun c => [pa c, pb c]

/-- The (32,3) window (left end first) recovered from the two lists `(l, r)` of a code: the cells
    left of the head unpacked; the cell carried by the counter of the head cell; the head cell
    unpacked; the cells right of the head unpacked. -/
def rec18 (l r : List ℕ) : List ℕ :=
  unpk l.reverse ++
    carry (r.getD 0 0 / 298 - 1) :: pa (r.getD 0 0) :: pb (r.getD 0 0) :: unpk (r.drop 1)

/-- The (32,3) state of the last `hp` cell seen. -/
def hpF (acc c : ℕ) : ℕ := if 10 ≤ c % 298 then (c % 298 - 10) / 9 else acc

/-- The (32,3) pseudo-state: the `hp` cell has the state `case_y_2 = q2` for `halt = 33`, and
    `begin = q0` for `null = 32`. -/
def qOf (l r : List ℕ) : ℕ := if (l.reverse ++ r).foldl hpF 0 = cQ St.q2 then 33 else 32

/-- **Readout** (list level) from a code `g` of the halting ID: `(|C|, ϕ₁(vf))`, by the (32,3)
    readout on the recovered (32,3) window. It does not look at the number of steps. -/
def readU (g : Spec.Code) : Option (ℕ × List ℕ) :=
  some (U32_3.readL 33 (qOf g.2.1 g.2.2) (rec18 g.2.1 g.2.2))

theorem unpk_cons (c : ℕ) (l : List ℕ) : unpk (c :: l) = pa c :: pb c :: unpk l := by
  simp [unpk]

theorem unpk_append (a b : List ℕ) : unpk (a ++ b) = unpk a ++ unpk b := by
  simp [unpk, List.flatMap_append]

theorem unpk_replicate (k : ℕ) : unpk (List.replicate k 0) = List.replicate (2 * k) 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ, unpk_cons, ih, show 2 * (k + 1) = 2 * k + 1 + 1 by ring,
      List.replicate_succ, List.replicate_succ]
    rfl

theorem unpk_length (l : List ℕ) : (unpk l).length = 2 * l.length := by
  induction l with
  | nil => rfl
  | cons c l ih => rw [unpk_cons, List.length_cons, List.length_cons, ih, List.length_cons]; ring

theorem unpk_getD (l : List ℕ) (i : ℕ) :
    (unpk l).getD i 0 = if i % 2 = 0 then pa (l.getD (i / 2) 0) else pb (l.getD (i / 2) 0) := by
  induction l generalizing i with
  | nil => simp [unpk, pa, pb]
  | cons c l ih =>
    rw [unpk_cons]
    obtain _ | _ | i := i
    · simp
    · simp
    · rw [List.getD_cons_succ, List.getD_cons_succ, ih,
        show (i + 1 + 1) / 2 = i / 2 + 1 by omega, show (i + 1 + 1) % 2 = i % 2 by omega,
        List.getD_cons_succ]

theorem rec18_padL (k : ℕ) (l r : List ℕ) :
    rec18 (l ++ List.replicate k 0) r = List.replicate (2 * k) 0 ++ rec18 l r := by
  simp only [rec18, List.reverse_append, List.reverse_replicate, unpk_append, unpk_replicate,
    List.append_assoc]

theorem rec18_padR (k : ℕ) (l r : List ℕ) :
    ∃ j, rec18 l (r ++ List.replicate k 0) = rec18 l r ++ List.replicate j 0 := by
  obtain ⟨j, hj⟩ := U32_3.drop1_pad r k
  refine ⟨2 * j, ?_⟩
  simp only [rec18, Spec.CodePad.getD_append_replicate, hj, unpk_append, unpk_replicate]
  simp

theorem foldl_hpF_none : ∀ (W : List ℕ) (acc : ℕ), (∀ c ∈ W, ¬ 10 ≤ c % 298) →
    W.foldl hpF acc = acc := by
  intro W
  induction W with
  | nil => intro _ _; rfl
  | cons c W ih =>
    intro acc h
    rw [List.foldl_cons, show hpF acc c = acc by
      simp only [hpF]; rw [if_neg (h c List.mem_cons_self)]]
    exact ih acc fun c' hc' => h c' (List.mem_cons_of_mem _ hc')

theorem foldl_hpF_zeros (k acc : ℕ) : (List.replicate k 0).foldl hpF acc = acc :=
  foldl_hpF_none _ acc fun c hc => by rw [List.eq_of_mem_replicate hc]; decide

theorem foldl_hpF (v : ℕ) : ∀ (W : List ℕ) (acc : ℕ),
    (∀ c ∈ W, 10 ≤ c % 298 → (c % 298 - 10) / 9 = v) → (∃ c ∈ W, 10 ≤ c % 298) →
    W.foldl hpF acc = v := by
  intro W
  induction W with
  | nil => intro _ _ ⟨c, hc, _⟩; exact absurd hc List.not_mem_nil
  | cons c W ih =>
    intro acc h hex
    rw [List.foldl_cons]
    by_cases hW : ∃ c' ∈ W, 10 ≤ c' % 298
    · exact ih _ (fun c' hc' => h c' (List.mem_cons_of_mem _ hc')) hW
    · have hc : 10 ≤ c % 298 := by
        obtain ⟨c', hc', h'⟩ := hex
        rcases List.mem_cons.mp hc' with rfl | hc'
        · exact h'
        · exact absurd ⟨c', hc', h'⟩ hW
      rw [foldl_hpF_none W _ (fun c' hc' h' => hW ⟨c', hc', h'⟩)]
      simp only [hpF, if_pos hc]
      exact h c List.mem_cons_self hc

theorem qOf_padL (k : ℕ) (l r : List ℕ) : qOf (l ++ List.replicate k 0) r = qOf l r := by
  simp only [qOf, List.reverse_append, List.reverse_replicate, List.append_assoc, List.foldl_append,
    foldl_hpF_zeros]

theorem qOf_padR (k : ℕ) (l r : List ℕ) : qOf l (r ++ List.replicate k 0) = qOf l r := by
  simp only [qOf, ← List.append_assoc, List.foldl_append, foldl_hpF_zeros]

/-- **The readout depends only on the ID**, not on the code chosen for it. -/
theorem readU_toID {p : ℤ} {g g' : Spec.Code} (h : Spec.toID p g = Spec.toID p g') :
    readU g = readU g' := by
  refine congrArg some (read_toID2 (fun _ l r => U32_3.readL 33 (qOf l r) (rec18 l r)) ?_ ?_ h)
  · intro s k l r
    simp only [rec18_padL, qOf_padL, U32_3.readL_padL]
  · intro s k l r
    obtain ⟨j, hj⟩ := rec18_padR k l r
    simp only [qOf_padR, hj, U32_3.readL_padR]

/-! #### Computability of the readout -/

open Primrec in
theorem pa_primrec : Primrec pa := by
  have v : Primrec fun c : ℕ => c % 298 := nat_mod.comp .id (const 298)
  exact (Primrec.ite (Primrec.eq.comp v (const 0)) (const 0)
    (Primrec.ite (nat_lt.comp v (const 10)) (nat_div.comp (nat_sub.comp v (const 1)) (const 3))
      (nat_div.comp (nat_mod.comp (nat_sub.comp v (const 10)) (const 9)) (const 3)))).of_eq
    fun _ => rfl

open Primrec in
theorem pb_primrec : Primrec pb := by
  have v : Primrec fun c : ℕ => c % 298 := nat_mod.comp .id (const 298)
  exact (Primrec.ite (Primrec.eq.comp v (const 0)) (const 0)
    (Primrec.ite (nat_lt.comp v (const 10)) (nat_mod.comp (nat_sub.comp v (const 1)) (const 3))
      (nat_mod.comp (nat_sub.comp v (const 10)) (const 3)))).of_eq fun _ => rfl

open Primrec in
theorem carry_primrec : Primrec carry :=
  (Primrec.ite (Primrec.eq.comp .id (const (idx3 (.q .s1)))) (const 1)
    (Primrec.ite (Primrec.eq.comp .id (const (idx3 (.q .s2)))) (const 2) (const 0))).of_eq
    fun _ => rfl

open Primrec in
theorem unpk_primrec : Primrec unpk :=
  (list_flatMap .id (list_cons.comp (pa_primrec.comp snd)
    (list_cons.comp (pb_primrec.comp snd) (const []))).to₂).of_eq fun _ => rfl

open Primrec in
theorem hpF_primrec : Primrec₂ hpF := by
  have v : Primrec fun p : ℕ × ℕ => p.2 % 298 := nat_mod.comp snd (const 298)
  exact (Primrec.ite (nat_le.comp (const 10) v) (nat_div.comp (nat_sub.comp v (const 10)) (const 9))
    fst).to₂

open Primrec in
theorem readU_primrec : Primrec readU := by
  have l : Primrec fun g : Spec.Code => g.2.1 := fst.comp snd
  have r : Primrec fun g : Spec.Code => g.2.2 := snd.comp snd
  have c : Primrec fun g : Spec.Code => g.2.2.getD 0 0 := (list_getD 0).comp r (const 0)
  have hrec : Primrec fun g : Spec.Code => rec18 g.2.1 g.2.2 :=
    list_append.comp (unpk_primrec.comp (list_reverse.comp l))
      (list_cons.comp (carry_primrec.comp (nat_sub.comp (nat_div.comp c (const 298)) (const 1)))
        (list_cons.comp (pa_primrec.comp c) (list_cons.comp (pb_primrec.comp c)
          (unpk_primrec.comp (list_drop.comp (const 1) r)))))
  have hfold : Primrec fun g : Spec.Code => (g.2.1.reverse ++ g.2.2).foldl hpF 0 :=
    list_foldl (list_append.comp (list_reverse.comp l) r) (const 0)
      (hpF_primrec.comp (fst.comp snd) (snd.comp snd)).to₂
  have hq : Primrec fun g : Spec.Code => qOf g.2.1 g.2.2 :=
    (Primrec.ite (Primrec.eq.comp hfold (const (cQ St.q2))) (const 33) (const 32)).of_eq fun _ => rfl
  exact option_some.comp (readL_primrec.comp (pair hq hrec))

/-! ### Reading an ID of the right shape -/

/-- The numbered (32,3) tape `L`, as a function of the (32,3) position. -/
def tau (L : List ℕ) (y : ℤ) : ℕ := if 0 ≤ y then L.getD y.toNat 0 else 0

theorem tau_sN (L : List Sy) (y : ℤ) : sN (Sim.tp Sy.s0 L y) = tau (L.map sN) y := tau_tp L y

theorem tau_sN' (L : List Sy) {y y' : ℤ} (h : y = y') : sN (Sim.tp Sy.s0 L y) = tau (L.map sN) y' := by
  rw [h]; exact tau_sN L y'

theorem tau_neg (L : List ℕ) {y : ℤ} (h : y < 0) : tau L y = 0 := by
  simp only [tau]
  rw [if_neg (by omega)]

theorem tau_big (L : List ℕ) {y : ℤ} (h : (L.length : ℤ) ≤ y) : tau L y = 0 := by
  simp only [tau]
  rw [if_pos (by omega), List.getD_eq_default _ _ (by omega)]

theorem reverse_map_range (f : ℕ → ℕ) (M : ℕ) :
    ((List.range M).map f).reverse = (List.range M).map (fun j => f (M - 1 - j)) := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_reverse, List.getElem_map, List.getElem_range, List.length_map,
    List.length_range]

/-- **Reading an ID from its description relative to the head.** `L` is the numbered (32,3) tape;
    the cell `d < 0` left of the head unpacks to the (32,3) cells `B + 2d`, `B + 2d + 1`; the counter
    of the head cell carries the cell `B` and the head cell unpacks to `B + 1`, `B + 2`; the cell
    `d ≥ 1` unpacks to `B + 2d + 1`, `B + 2d + 2`; `γ` is blank outside a window; every `hp` cell has
    the (32,3) state `p`, and there is one. Then some code of `γ` is read as the (32,3) readout of
    `L` in the state `halt` (`p = case_y_2`) or `null`. -/
theorem readU_of_shape (γ : Spec.ID) (L : List ℕ) (B : ℤ) (p : St) (mL mR : ℕ) (hB : -1 ≤ B)
    (hleft : ∀ d : ℤ, d < 0 → pa (γ.tape (γ.pos + d)) = tau L (B + 2 * d) ∧
      pb (γ.tape (γ.pos + d)) = tau L (B + 2 * d + 1))
    (hhead : carry (γ.tape γ.pos / 298 - 1) = tau L B ∧ pa (γ.tape γ.pos) = tau L (B + 1) ∧
      pb (γ.tape γ.pos) = tau L (B + 2))
    (hright : ∀ d : ℤ, 1 ≤ d → pa (γ.tape (γ.pos + d)) = tau L (B + 2 * d + 1) ∧
      pb (γ.tape (γ.pos + d)) = tau L (B + 2 * d + 2))
    (hsupp : ∀ d : ℤ, (d < -(mL : ℤ) ∨ (mR : ℤ) < d) → γ.tape (γ.pos + d) = 0)
    (hhp : ∀ d : ℤ, 10 ≤ γ.tape (γ.pos + d) % 298 → (γ.tape (γ.pos + d) % 298 - 10) / 9 = cQ p)
    (hex : ∃ d : ℤ, -(mL : ℤ) ≤ d ∧ d ≤ mR ∧ 10 ≤ γ.tape (γ.pos + d) % 298) :
    ∃ g, Spec.toID γ.pos g = γ ∧
      readU g = some (U32_3.readL 33 (if p = St.q2 then 33 else 32) L) := by
  obtain ⟨M, hM⟩ : ∃ M, M = mL + B.toNat + 1 := ⟨_, rfl⟩
  obtain ⟨k, hk⟩ : ∃ k, k = mR + L.length := ⟨_, rfl⟩
  refine ⟨codeOf γ M (k + 1), toID_codeOf γ _ _ (fun x hx => ?_), ?_⟩
  · have := hsupp (x - γ.pos) (by push_cast at hx; omega)
    rwa [show γ.pos + (x - γ.pos) = x by omega] at this
  · -- the two lists of the code
    have hl : (codeOf γ M (k + 1)).2.1.reverse =
        (List.range M).map (fun (j : ℕ) => γ.tape (γ.pos + ((j : ℤ) - M))) := by
      simp only [codeOf, reverse_map_range]
      refine List.map_congr_left fun j hj => ?_
      have := List.mem_range.mp hj
      congr 1
      omega
    have hr0 : (codeOf γ M (k + 1)).2.2.getD 0 0 = γ.tape γ.pos := by
      simp only [codeOf]
      rw [getD_map_range, if_pos (by omega)]
      simp
    have hr1 : (codeOf γ M (k + 1)).2.2.drop 1 =
        (List.range k).map (fun (j : ℕ) => γ.tape (γ.pos + ((j : ℤ) + 1))) := by
      simp only [codeOf, drop_one_map_range]
      refine List.map_congr_left fun j _ => ?_
      congr 1
    -- the recovered window, cell by cell
    have hrec : ∀ i : ℕ, (rec18 (codeOf γ M (k + 1)).2.1 (codeOf γ M (k + 1)).2.2).getD i 0 =
        tau L (B - 2 * M + i) := by
      intro i
      simp only [rec18, hl, hr0, hr1]
      have hlen : (unpk ((List.range M).map (fun (j : ℕ) => γ.tape (γ.pos + ((j : ℤ) - M))))).length =
          2 * M := by rw [unpk_length]; simp
      by_cases h1 : i < 2 * M
      · rw [List.getD_append _ _ _ _ (by rw [hlen]; exact h1), unpk_getD, getD_map_range,
          if_pos (show i / 2 < M by omega)]
        obtain ⟨hp, hq⟩ := hleft ((((i / 2 : ℕ) : ℤ) - M)) (by omega)
        split_ifs with h2
        · rw [hp]; congr 1; omega
        · rw [hq]; congr 1; omega
      · rw [List.getD_append_right _ _ _ _ (by rw [hlen]; omega), hlen]
        obtain ⟨j, hj⟩ : ∃ j, i = 2 * M + j := ⟨i - 2 * M, by omega⟩
        subst hj
        rw [Nat.add_sub_cancel_left]
        obtain _ | _ | _ | j := j
        · rw [List.getD_cons_zero, hhead.1]; congr 1; omega
        · rw [List.getD_cons_succ, List.getD_cons_zero, hhead.2.1]; congr 1; omega
        · rw [List.getD_cons_succ, List.getD_cons_succ, List.getD_cons_zero, hhead.2.2]
          congr 1; omega
        · rw [List.getD_cons_succ, List.getD_cons_succ, List.getD_cons_succ, unpk_getD,
            getD_map_range]
          by_cases h3 : j / 2 < k
          · rw [if_pos h3]
            obtain ⟨hp, hq⟩ := hright (((j / 2 : ℕ) : ℤ) + 1) (by omega)
            split_ifs with h4
            · rw [hp]; congr 1; omega
            · rw [hq]; congr 1; omega
          · rw [if_neg h3, tau_big L (by omega)]
            split_ifs <;> rfl
    have htau : ∀ i : ℕ, tau L (B - 2 * M + i) =
        (List.replicate (2 * M - B).toNat 0 ++ L).getD i 0 := by
      intro i
      rw [getD_zeros_append]
      simp only [tau]
      by_cases h : 0 ≤ B - 2 * M + i
      · rw [if_pos h, if_neg (by omega)]
        congr 1
        omega
      · rw [if_neg h, if_pos (by omega)]
    -- the (32,3) state
    have hmem : ∀ c ∈ (codeOf γ M (k + 1)).2.1.reverse ++ (codeOf γ M (k + 1)).2.2,
        ∃ d : ℤ, c = γ.tape (γ.pos + d) := by
      intro c hc
      rcases List.mem_append.mp hc with hc | hc
      · rw [hl] at hc
        obtain ⟨j, -, rfl⟩ := List.mem_map.mp hc
        exact ⟨_, rfl⟩
      · simp only [codeOf] at hc
        obtain ⟨j, -, rfl⟩ := List.mem_map.mp hc
        exact ⟨_, rfl⟩
    have hq : qOf (codeOf γ M (k + 1)).2.1 (codeOf γ M (k + 1)).2.2 = if p = St.q2 then 33 else 32 := by
      have hf : ((codeOf γ M (k + 1)).2.1.reverse ++ (codeOf γ M (k + 1)).2.2).foldl hpF 0 = cQ p := by
        refine foldl_hpF _ _ _ (fun c hc h10 => ?_) ?_
        · obtain ⟨d, rfl⟩ := hmem c hc
          exact hhp d h10
        · obtain ⟨d, hd1, hd2, hd⟩ := hex
          refine ⟨γ.tape (γ.pos + d), ?_, hd⟩
          by_cases hd0 : d < 0
          · refine List.mem_append_left _ ?_
            rw [hl]
            refine List.mem_map.mpr ⟨(d + M).toNat, List.mem_range.mpr (by omega), ?_⟩
            congr 2
            omega
          · refine List.mem_append_right _ ?_
            simp only [codeOf]
            exact List.mem_map.mpr ⟨d.toNat, List.mem_range.mpr (by omega), by congr 2; omega⟩
      simp only [qOf, hf]
      by_cases hp : p = St.q2
      · subst hp; simp
      · rw [if_neg (fun h => hp (cQ_inj h)), if_neg hp]
    obtain ⟨Mx, j1, j2, e1, e2⟩ := Spec.CodePad.pad_of_getD _ _ fun i => (hrec i).trans (htau i)
    simp only [readU, hq]
    rw [e1, U32_3.readL_padR, ← U32_3.readL_padL 33 _ (2 * M - B).toNat L, e2, U32_3.readL_padR]

/-! ### The cells of `K` -/

theorem cW_mod (x : WSym St Sy) : cW x % 298 = cW x := Nat.mod_eq_of_lt (cW_lt x)

theorem pa_ct (k v : ℕ) : pa (298 * (k + 1) + v) = pa v := by
  have h : (298 * (k + 1) + v) % 298 = v % 298 := by omega
  simp only [pa, h]

theorem pb_ct (k v : ℕ) : pb (298 * (k + 1) + v) = pb v := by
  have h : (298 * (k + 1) + v) % 298 = v % 298 := by omega
  simp only [pb, h]

theorem pa_pr (s t : Sy) : pa (cW (.pr s t)) = sN s := by
  have := cS_lt s; have := cS_lt t
  simp only [pa, cW_mod]
  simp only [cW, ← cS_sN]
  rw [if_neg (by omega), if_pos (by omega)]
  omega

theorem pb_pr (s t : Sy) : pb (cW (.pr s t)) = sN t := by
  have := cS_lt s; have := cS_lt t
  simp only [pb, cW_mod]
  simp only [cW, ← cS_sN]
  rw [if_neg (by omega), if_pos (by omega)]
  omega

theorem pa_hp (p : St) (s t : Sy) : pa (cW (.hp p s t)) = sN s := by
  have := cS_lt s; have := cS_lt t
  simp only [pa, cW_mod]
  simp only [cW, ← cS_sN]
  rw [if_neg (by omega), if_neg (by omega)]
  omega

theorem pb_hp (p : St) (s t : Sy) : pb (cW (.hp p s t)) = sN t := by
  have := cS_lt s; have := cS_lt t
  simp only [pb, cW_mod]
  simp only [cW, ← cS_sN]
  rw [if_neg (by omega), if_neg (by omega)]
  omega

section Pack
variable {a : ℤ} {n : ℕ} {p : St} {x : ℤ} {g : ℤ → Sy} {i : ℤ}

theorem pa_pack : pa (cW (pack a n p x g i)) =
    if 1 ≤ i ∧ i ≤ n then sN (g (a + 2 * (i - 1))) else 0 := by
  simp only [Conv59.pack]
  split_ifs with h1 h2
  · rw [pa_hp, h2]
  · rw [pa_pr]
  · rfl

theorem pb_pack : pb (cW (pack a n p x g i)) =
    if 1 ≤ i ∧ i ≤ n then sN (g (a + 2 * (i - 1) + 1)) else 0 := by
  simp only [Conv59.pack]
  split_ifs with h1 h2
  · rw [pb_hp, h2]
  · rw [pb_pr]
  · rfl

/-- Every `hp` cell of a packed tape has the state `p`. -/
theorem hp_pack (h : 10 ≤ cW (pack a n p x g i) % 298) :
    (cW (pack a n p x g i) % 298 - 10) / 9 = cQ p := by
  rw [cW_mod] at h ⊢
  simp only [Conv59.pack] at h ⊢
  split_ifs at h ⊢ with h1 h2
  · have := cS_lt (g x); have := cS_lt (g (x + 1))
    simp only [cW]
    omega
  · have := cS_lt (g (a + 2 * (i - 1))); have := cS_lt (g (a + 2 * (i - 1) + 1))
    simp only [cW] at h
    omega
  · simp [cW] at h

theorem hp_pack_at (h1 : 1 ≤ i) (h2 : i ≤ n) (hx : a + 2 * (i - 1) = x) :
    10 ≤ cW (pack a n p x g i) % 298 := by
  rw [pack_hp h1 h2 hx, cW_mod]
  simp only [cW]
  omega

end Pack

theorem carry_q (s : Sy) : carry (idx3 (.q s)) = sN s := by cases s <;> decide

theorem carry_h : carry (idx3 (.h .s0)) = 0 := by decide

/-! ### The halting configurations, numbered -/

/-- The 3-state encoding of a configuration of `That` in a state `q ≠ q_L`. -/
theorem enc_go (cw : Cfg (WSt St Sy) Ps (WSym St Sy)) (q : WSt St Sy) (hq : cw.st = .go q)
    (hqL : q ≠ .L) :
    Conv3P.enc .L idx3 cw =
      ⟨.go .R0, cw.pos, upd (fun i => .pl (cw.tape i)) cw.pos (.ct (cw.tape cw.pos) (idx3 q))⟩ := by
  obtain ⟨st, pos, tape⟩ := cw
  simp only at hq
  subst hq
  simp [Conv3P.enc, hqL]

/-- **Reading the 3-state encoding** of a configuration `cw` of `That` in a state `q ≠ q_L`, from
    the description of the cells of `cw` relative to its head. -/
theorem read_enc (cw : Cfg (WSt St Sy) Ps (WSym St Sy)) (q : WSt St Sy) (hq : cw.st = .go q)
    (hqL : q ≠ .L) (L : List ℕ) (B : ℤ) (p : St) (mL mR : ℕ) (hB : -1 ≤ B)
    (hleft : ∀ d : ℤ, d < 0 → pa (cW (cw.tape (cw.pos + d))) = tau L (B + 2 * d) ∧
      pb (cW (cw.tape (cw.pos + d))) = tau L (B + 2 * d + 1))
    (hhead : carry (idx3 q) = tau L B ∧ pa (cW (cw.tape cw.pos)) = tau L (B + 1) ∧
      pb (cW (cw.tape cw.pos)) = tau L (B + 2))
    (hright : ∀ d : ℤ, 1 ≤ d → pa (cW (cw.tape (cw.pos + d))) = tau L (B + 2 * d + 1) ∧
      pb (cW (cw.tape (cw.pos + d))) = tau L (B + 2 * d + 2))
    (hsupp : ∀ d : ℤ, (d < -(mL : ℤ) ∨ (mR : ℤ) < d) → cw.tape (cw.pos + d) = .bl)
    (hhp : ∀ d : ℤ, 10 ≤ cW (cw.tape (cw.pos + d)) % 298 →
      (cW (cw.tape (cw.pos + d)) % 298 - 10) / 9 = cQ p)
    (hex : ∃ d : ℤ, -(mL : ℤ) ≤ d ∧ d ≤ mR ∧ 10 ≤ cW (cw.tape (cw.pos + d)) % 298) :
    ∃ g, Spec.toID (numCfg num 0 (Conv3P.enc .L idx3 cw)).pos g = numCfg num 0 (Conv3P.enc .L idx3 cw) ∧
      readU g = some (U32_3.readL 33 (if p = St.q2 then 33 else 32) L) := by
  rw [enc_go cw q hq hqL]
  have hcell : ∀ d : ℤ,
      (numCfg num 0 (⟨.go .R0, cw.pos, upd (fun i => .pl (cw.tape i)) cw.pos
          (.ct (cw.tape cw.pos) (idx3 q))⟩ : Cfg TSt Ps (CSym (WSym St Sy)))).tape
        ((numCfg num 0 (⟨.go .R0, cw.pos, upd (fun i => .pl (cw.tape i)) cw.pos
          (.ct (cw.tape cw.pos) (idx3 q))⟩ : Cfg TSt Ps (CSym (WSym St Sy)))).pos + d) =
        if d = 0 then 298 * (idx3 q + 1) + cW (cw.tape cw.pos) else cW (cw.tape (cw.pos + d)) := by
    intro d
    simp only [numCfg, num, sub_zero, add_zero]
    by_cases hd : d = 0
    · subst hd
      rw [if_pos rfl, add_zero, upd_eq]
      rfl
    · rw [if_neg hd, upd_ne _ _ (by omega)]
      rfl
  have h0 : ∀ γ : Spec.ID, γ.pos + 0 = γ.pos := fun γ => add_zero _
  have hlt := cW_lt (cw.tape cw.pos)
  refine readU_of_shape _ L B p mL mR hB (fun d hd => ?_) ?_ (fun d hd => ?_) (fun d hd => ?_)
    (fun d h10 => ?_) ?_
  · rw [hcell, if_neg (by omega)]
    exact hleft d hd
  · have e := hcell 0
    rw [h0, if_pos rfl] at e
    rw [e, pa_ct, pb_ct,
      show (298 * (idx3 q + 1) + cW (cw.tape cw.pos)) / 298 - 1 = idx3 q by omega]
    exact hhead
  · rw [hcell, if_neg (by omega)]
    exact hright d hd
  · rw [hcell, if_neg (by omega), hsupp d hd]
    rfl
  · rw [hcell] at h10 ⊢
    by_cases hd : d = 0
    · subst hd
      rw [if_pos rfl] at h10 ⊢
      have e : (298 * (idx3 q + 1) + cW (cw.tape cw.pos)) % 298 = cW (cw.tape (cw.pos + 0)) % 298 := by
        rw [add_zero]; omega
      rw [e] at h10 ⊢
      exact hhp 0 h10
    · rw [if_neg hd] at h10 ⊢
      exact hhp d h10
  · obtain ⟨d, hd1, hd2, hd⟩ := hex
    refine ⟨d, hd1, hd2, ?_⟩
    rw [hcell]
    by_cases hd0 : d = 0
    · subst hd0
      rw [if_pos rfl]
      rw [add_zero] at hd
      omega
    · rw [if_neg hd0]
      exact hd

/-- **Reading the halting configuration of `K`**, for a halting configuration `(p, P, L)` of
    `T32'` reached in `N` steps from a configuration `c₀` that satisfies the invariant of Lemma 5.9
    (pairs starting at `0`, `n₀` of them). -/
theorem read_fin (n0 : ℕ) (c0 : Cfg St Ps Sy) (hc0 : c0.st = .go St.q0)
    (hI : Conv59.Inv Sy.s0 0 n0 c0.pos c0.tape) (p : St) (P : ℕ) (L : List Sy) (N : ℕ)
    (hT : HaltsIn T32' N c0 ⟨.go p, (P : ℤ), Sim.tp .s0 L⟩) :
    ∃ g, Spec.toID (numCfg num 0 (Conv3P.enc .L idx3
          (Conv59.E Sy.s0 0 n0 N ⟨.go p, (P : ℤ), Sim.tp .s0 L⟩))).pos g =
        numCfg num 0 (Conv3P.enc .L idx3 (Conv59.E Sy.s0 0 n0 N ⟨.go p, (P : ℤ), Sim.tp .s0 L⟩)) ∧
      readU g = some (U32_3.readL 33 (if p = St.q2 then 33 else 32) (L.map sN)) := by
  obtain ⟨⟨p', hp', hIe⟩, -⟩ := Conv59.run_sim hyp59 hc0 hI N hT.1
  -- the invariant of the halting configuration, with its fields unfolded
  have hlo : (0 : ℤ) - (N : ℤ) ≤ (P : ℤ) := hIe.lo
  have hhi : (P : ℤ) + 4 ≤ (0 : ℤ) - (N : ℤ) + 2 * ((n0 + N : ℕ) : ℤ) := hIe.hi
  have hev : ((P : ℤ) - ((0 : ℤ) - (N : ℤ))) % 2 = 0 := hIe.even
  have hout : ∀ j : ℤ, (0 : ℤ) - (N : ℤ) + 2 * ((n0 + N : ℕ) : ℤ) ≤ j → Sim.tp Sy.s0 L j = Sy.s0 :=
    fun j hj => hIe.out j (.inr hj)
  cases N with
  | zero =>
    -- the sweep stops at the pair of the head: `immW`
    have hE : Conv59.E Sy.s0 0 n0 0 (⟨.go p, (P : ℤ), Sim.tp .s0 L⟩ : Cfg St Ps Sy) =
        Conv59.immW 0 n0 p (P : ℤ) (Sim.tp .s0 L) := by
      simp [Conv59.E]
    rw [hE]
    refine read_enc _ (.q (Sim.tp .s0 L ((P : ℤ) - 1))) rfl (by nofun) (L.map sN) ((P : ℤ) - 1) p
      ((P : ℤ) / 2 + 1).toNat n0 (by omega) (fun d hd => ?_) ?_ (fun d hd => ?_) (fun d hd => ?_)
      (fun d h10 => ?_) ⟨0, by omega, by omega, ?_⟩
    · simp only [Conv59.immW]
      rw [mix_lt (by omega), pa_pack, pb_pack]
      split_ifs with hc
      · constructor
        · exact tau_sN' L (by omega)
        · exact tau_sN' L (by omega)
      · exact ⟨(tau_neg _ (by omega)).symm, (tau_neg _ (by omega)).symm⟩
    · simp only [Conv59.immW]
      rw [mix_ge (le_refl _), pa_pack, pb_pack, carry_q]
      split_ifs with hc
      · refine ⟨?_, ?_, ?_⟩
        · exact tau_sN' L (by omega)
        · exact tau_sN' L (by omega)
        · exact tau_sN' L (by omega)
      · exfalso; omega
    · simp only [Conv59.immW]
      rw [mix_ge (by omega), pa_pack, pb_pack]
      split_ifs with hc
      · constructor
        · exact tau_sN' L (by omega)
        · exact tau_sN' L (by omega)
      · rw [← tau_sN, ← tau_sN, hout _ (by omega), hout _ (by omega)]
        exact ⟨rfl, rfl⟩
    · simp only [Conv59.immW]
      rcases hd with hd | hd
      · rw [mix_lt (by omega), pack_out (.inl (by omega))]
      · rw [mix_ge (by omega), pack_out (.inr (by omega))]
    · simp only [Conv59.immW] at h10 ⊢
      by_cases hd : d < 0
      · rw [mix_lt (by omega)] at h10 ⊢
        exact hp_pack h10
      · rw [mix_ge (by omega)] at h10 ⊢
        exact hp_pack h10
    · simp only [Conv59.immW]
      rw [add_zero, mix_ge (le_refl _)]
      exact hp_pack_at (by omega) (by omega) (by omega)
  | succ N =>
    -- `h(s0)` reads the blank right of the pairs: `haltW`
    obtain ⟨c1, h1, r, hr, hst, hs, he⟩ := URTM.SimLemmas.StepN.last hT.1
    obtain ⟨⟨p1, hp1, hI1⟩, -⟩ := Conv59.run_sim hyp59 hc0 hI N h1
    have hhi1 := hI1.hi
    have htape : Sim.tp Sy.s0 L = upd c1.tape c1.pos r.t := congrArg Cfg.tape he
    -- the tape is blank from the end of the pairs of `haltW` on
    have hbeyond : ∀ j : ℤ, (0 - ((N + 1 : ℕ) : ℤ)) + 2 * ((n0 + N : ℕ) : ℤ) ≤ j →
        Sim.tp Sy.s0 L j = Sy.s0 := by
      intro j hj
      rw [htape, upd_ne _ _ (by omega)]
      by_cases hj' : j = 0 - (N : ℤ) + 2 * ((n0 + N : ℕ) : ℤ) - 1
      · rw [hj']; exact hI1.last
      · exact hI1.out j (.inr (by omega))
    have hE : Conv59.E Sy.s0 0 n0 (N + 1) (⟨.go p, (P : ℤ), Sim.tp .s0 L⟩ : Cfg St Ps Sy) =
        Conv59.haltW Sy.s0 (0 - ((N + 1 : ℕ) : ℤ)) (n0 + N) p (P : ℤ) (Sim.tp .s0 L) := by
      simp only [Conv59.E, Nat.add_one_ne_zero, if_false]
      rw [show n0 + (N + 1) - 1 = n0 + N by omega]
    rw [hE]
    have hb : ∀ j : ℤ, (0 - ((N + 1 : ℕ) : ℤ)) + 2 * ((n0 + N : ℕ) : ℤ) ≤ j →
        tau (L.map sN) j = 0 := by
      intro j hj
      rw [← tau_sN, hbeyond j hj]
      rfl
    refine read_enc _ (.h .s0) rfl (by nofun) (L.map sN)
      ((0 - ((N + 1 : ℕ) : ℤ)) + 2 * ((n0 + N : ℕ) : ℤ)) p (n0 + N + 1) 0
      (by omega) (fun d hd => ?_) ?_ (fun d hd => ?_) (fun d hd => ?_)
      (fun d h10 => ?_) ⟨((P : ℤ) - (0 - ((N + 1 : ℕ) : ℤ))) / 2 + 1 - (((n0 + N : ℕ) : ℤ) + 1),
        by omega, by omega, ?_⟩
    · simp only [Conv59.haltW]
      rw [pa_pack, pb_pack]
      split_ifs with hc
      · constructor
        · exact tau_sN' L (by omega)
        · exact tau_sN' L (by omega)
      · exact ⟨(tau_neg _ (by omega)).symm, (tau_neg _ (by omega)).symm⟩
    · simp only [Conv59.haltW]
      rw [carry_h, pa_pack, pb_pack]
      split_ifs with hc
      · exfalso; omega
      · exact ⟨(hb _ (le_refl _)).symm, (hb _ (by omega)).symm, (hb _ (by omega)).symm⟩
    · simp only [Conv59.haltW]
      rw [pa_pack, pb_pack]
      split_ifs with hc
      · exfalso; omega
      · exact ⟨(hb _ (by omega)).symm, (hb _ (by omega)).symm⟩
    · simp only [Conv59.haltW]
      exact pack_out (by omega)
    · simp only [Conv59.haltW] at h10 ⊢
      exact hp_pack h10
    · simp only [Conv59.haltW]
      exact hp_pack_at (by omega) (by omega) (by omega)

/-! ### The run-level simulation and the main theorem -/

/-- **The 18476-symbol machine simulates every CTSH at the level of Spec** (run level, exact
    readback). -/
theorem runSim_U (C : CTSH) (w : List Ch) :
    RunSim (CStep C) (Halting C) (Spec.Step U) (Spec.Halted U)
      (fun y γ => ∃ g, Spec.toID γ.pos g = γ ∧ readU g = some (C.length, y.1.map loN))
      (w, 0) (Spec.toID 0 (encList C w)) := by
  rw [encList_eq]
  obtain ⟨-, hF, -, hN⟩ := URTM.CTSH.U3_18476.urtm3_18476_simulates_ctsh C w (n0 C w) (hn0 C w)
  refine runSim_of_sim num K 0 C w (URTM.CTSH.U3_18476.E18476 C w (n0 C w))
    (fun f c => ∃ rm N, HaltsIn T32' N (encC32 C w) (unhalt f32 (finCfg32 C f.1 f.2 rm)) ∧
      c = URTM.CTSH.U3_18476.fin18476 (n0 C w) C f.1 f.2 rm N) _
    (fun m f hf => ?_) (fun hn => hN.mp hn) (fun f c hf hc => ?_)
  · obtain ⟨N, M, rm, -, hT, hM⟩ := hF m f.1 f.2 hf
    exact ⟨M, _, hM, rm, N, hT, rfl⟩
  · obtain ⟨rm, N, hT, rfl⟩ := hc
    obtain ⟨vf, mf⟩ := f
    obtain ⟨h, L, P, hfin, hrd⟩ := fin32_read C vf mf rm hf
    have he : unhalt f32 (finCfg32 C vf mf rm) = ⟨.go (f32 h), (P : ℤ), Sim.tp .s0 L⟩ := by
      rw [hfin]; rfl
    rw [he] at hT
    simp only [URTM.CTSH.U3_18476.fin18476, he]
    obtain ⟨g, hg, hr⟩ := read_fin (n0 C w) (encC32 C w) rfl (inv0 C w (n0 C w) (hn0 C w))
      (f32 h) P L N hT
    refine ⟨g, hg, ?_⟩
    rw [hr, ← hrd]
    cases h <;> rfl

/-- **The 18476-symbol three-state machine is a UTM in the strict sense of Morita Def. 7.1.** -/
theorem isUTMStrict_U : Spec.IsUTMStrict U :=
  ChainGen.isUTMStrict_of_ctsh U encList readU encList_primrec readU_primrec isIDOf_encList
    runSim_U (fun _ _ _ h => readU_toID h)

end URTM.Univ.U3_18476
