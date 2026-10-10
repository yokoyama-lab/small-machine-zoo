/-
  **L1: an arbitrary quintuple TM (code level) → TRM** (docs/24 §2 L1, piece P5).

  Source: the code-level system `L0.CStep T` / `L0.CHalt T` of `LeanUniv/L0Zipper.lean`
  (zipper step with normalisation of trailing blanks) for an arbitrary table `T`.
  Target: the TRM of `LeanUniv/TRM.lean` with program `prog T`.

  * **Width.** `w := width T = log2 (max symbol of T) + 1` (= `max 1 (bitlen (max symbol))`),
    `B := 2^w`. The invariant `Inv T` says every symbol of the code is `< B`; `IsIDOf (tm n)`
    gives it (`hin`), and steps preserve it.
  * **Encoding.** `(q, L, R) ↦ (rd q 0 0, Σ L_k B^k, Σ R_k B^k)` for a normalised code
    (no trailing blanks); an unnormalised code gets the label `nrm q` (two no-op steps, matching
    L0's normalisation step).
  * **Labels** are `Nat.pair` codes: `lRd m q j acc` (read phase; `m = 0` reads Y with
    `half2`, `m = 1` reads X with `half1`; `j` bits read so far, accumulated LSB-first in
    `acc`), `lPush r v k c` (push the low `k` bits of `v`, MSB first, into register `r`, then
    go to `c`), `lNrm q`, `lNrm' q`.
  * **One TM step** from `lRd 0 q 0 0`: `w × half2` to `lRd 0 q w s`; there, no rule ⇒ halt
    (the halting label carries `(q, w, s)`); rule `(t, R, q')` ⇒ `w × dbl1` pushes `t` into X;
    `(t, Z, q')` ⇒ `w × dbl2` pushes `t` back into Y; `(t, L, q')` ⇒ `w × dbl2` (push `t`),
    `w × half1` (pop `s'` from X, label `lRd 1 q' j acc`), `w × dbl2` (push `s'`). Then `lRd q' 0 0`.
  * **Readback** `dec` uses the label only (no `n`): at `lRd 0 q w s` with registers `(X, Y')`,
    the code is `(q, digits_B X, s :: digits_B Y')` with trailing blanks removed.

  Main statements: `sim` (`ExactSim` for every table), `hin` (the bridge hypothesis `hin` of
  `isUTMStrict_of_chain` for `tm n`, with `InvX n := Inv (tbl n)`), `tm_runSim_trm`
  (composite run-level simulation Spec `tm n` → TRM).
-/
import LeanUniv.L0Zipper
import LeanUniv.TRM
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

namespace URTM.Univ.L1
open URTM URTM.Spec URTM.Univ.L0 URTM.Univ.TRM Relation

/-! ### Numbers and digit lists -/

/-- `Σ l_k B^k`. -/
def num (B : ℕ) : List ℕ → ℕ
  | [] => 0
  | a :: l => a + B * num B l

/-- Base-`B` digits of `X`, least significant first, no trailing zeros (fuel `f`). -/
def digs (B : ℕ) : ℕ → ℕ → List ℕ
  | 0, _ => []
  | f + 1, X => if X = 0 then [] else X % B :: digs B f (X / B)

theorem num_trim (B : ℕ) (l : List ℕ) : num B (trim l) = num B l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [trim, consT]
    split_ifs with h
    · obtain ⟨rfl, h⟩ := h
      simp [num, ← ih, h]
    · simp [num, ih]

theorem trim_eq_nil_of_num {B : ℕ} (hB : 0 < B) {l : List ℕ} (h : num B l = 0) : trim l = [] := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [num] at h
    have ha : a = 0 := by omega
    have hn : num B l = 0 := by
      rcases Nat.eq_zero_or_pos (num B l) with h' | h'
      · exact h'
      · have : 0 < B * num B l := Nat.mul_pos hB h'
        omega
    simp [trim, ih hn, ha, consT]

theorem digs_zero (B f : ℕ) : digs B f 0 = [] := by cases f <;> simp [digs]

theorem digs_num {B : ℕ} (hB : 2 ≤ B) :
    ∀ (l : List ℕ), (∀ x ∈ l, x < B) → ∀ f, num B l ≤ f → digs B f (num B l) = trim l := by
  intro l
  induction l with
  | nil => intro _ f _; simp [num, digs_zero, trim]
  | cons a l ih =>
    intro hl f hf
    have ha : a < B := hl a (List.mem_cons_self ..)
    have hl' : ∀ x ∈ l, x < B := fun x hx => hl x (List.mem_cons_of_mem _ hx)
    by_cases hv : num B (a :: l) = 0
    · rw [hv, digs_zero, trim_eq_nil_of_num (by omega) hv]
    · simp only [num] at hv hf ⊢
      obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
      have hB0 : 0 < B := by omega
      have hmod : (a + B * num B l) % B = a := by
        rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]
      have hdiv : (a + B * num B l) / B = num B l := by
        rw [Nat.add_mul_div_left _ _ hB0, Nat.div_eq_of_lt ha, zero_add]
      have hle : num B l ≤ f' := by
        have : 2 * num B l ≤ B * num B l := Nat.mul_le_mul_right _ hB
        omega
      rw [digs, if_neg hv, hmod, hdiv, ih hl' f' hle]
      simp only [trim, consT]
      rw [if_neg]
      rintro ⟨rfl, h⟩
      apply hv
      rw [← num_trim, h]; simp [num]

theorem num_head {B : ℕ} (hB : 0 < B) {l : List ℕ} (hl : ∀ x ∈ l, x < B) :
    num B l % B = l.headD 0 ∧ num B l / B = num B l.tail := by
  cases l with
  | nil => simp [num]
  | cons a l =>
    have ha : a < B := hl a (List.mem_cons_self ..)
    simp only [num, List.headD_cons, List.tail_cons]
    exact ⟨by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha],
      by rw [Nat.add_mul_div_left _ _ hB, Nat.div_eq_of_lt ha, zero_add]⟩

theorem headD_lt {B : ℕ} (hB : 0 < B) {l : List ℕ} (hl : ∀ x ∈ l, x < B) : l.headD 0 < B := by
  cases l with
  | nil => simpa using hB
  | cons a l => exact hl a (List.mem_cons_self ..)

/-! ### Width -/

/-- Maximum of a list (0 if empty). -/
def lmax (l : List ℕ) : ℕ := l.foldr max 0

theorem le_lmax {x : ℕ} {l : List ℕ} (h : x ∈ l) : x ≤ lmax l := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
    simp only [lmax, List.foldr_cons] at ih ⊢
    rcases List.mem_cons.mp h with rfl | h
    · exact le_max_left _ _
    · exact le_trans (ih h) (le_max_right _ _)

/-- Bit width: `log2 (max symbol of T) + 1`, i.e. `max 1 (bitlen (max symbol))`. -/
def width (T : List Quint) : ℕ := Nat.log2 (lmax (symbols T)) + 1

theorem lt_width {T : List Quint} {x : ℕ} (hx : x ∈ symbols T) : x < 2 ^ width T :=
  lt_of_le_of_lt (le_lmax hx) Nat.lt_log2_self

theorem two_le_B (T : List Quint) : 2 ≤ 2 ^ width T := by
  unfold width
  rw [pow_succ]
  have := Nat.one_le_two_pow (n := Nat.log2 (lmax (symbols T)))
  omega

/-! ### Labels and program -/

/-- Read-phase label: mode `m` (0 = read Y, then act; 1 = read X, then push into Y),
    state `q`, `j` bits read, accumulator `acc`. -/
def lRd (m q j acc : ℕ) : ℕ := Nat.pair 0 (Nat.pair m (Nat.pair q (Nat.pair j acc)))

/-- Push-phase label: push the low `k` bits of `v`, MSB first, into register `r`, then `c`. -/
def lPush (r v k c : ℕ) : ℕ := Nat.pair 1 (Nat.pair r (Nat.pair v (Nat.pair k c)))

/-- Normalisation labels (two no-op steps, then `lRd 0 q 0 0`). -/
def lNrm (q : ℕ) : ℕ := Nat.pair 2 q
def lNrm' (q : ℕ) : ℕ := Nat.pair 3 q

/-- Bit `k` of `v`. -/
def bit (v k : ℕ) : Bool := decide (v / 2 ^ k % 2 = 1)

theorem bit_toNat (v k : ℕ) : (bit v k).toNat = v / 2 ^ k % 2 := by
  unfold bit
  rcases Nat.mod_two_eq_zero_or_one (v / 2 ^ k) with h | h <;> simp [h]

/-- First instruction of "push the low `k` bits of `v` into register `r` (1 = X, else Y),
    then go to `c`". -/
def pushOp (r v k c : ℕ) : Op :=
  if r = 1 then .dbl1 (bit v (k - 1)) (if k ≤ 1 then c else lPush r v (k - 1) c)
  else .dbl2 (bit v (k - 1)) (if k ≤ 1 then c else lPush r v (k - 1) c)

/-- The first instruction executing the rule right-hand side `o = (t, d, q')`. -/
def act (w : ℕ) (o : ℕ × ℕ × ℕ) : Op :=
  if o.2.1 = 0 then pushOp 2 o.1 w (lRd 1 o.2.2 0 0)
  else if o.2.1 = 1 then pushOp 2 o.1 w (lRd 0 o.2.2 0 0)
  else pushOp 1 o.1 w (lRd 0 o.2.2 0 0)

/-- The TRM program for table `T` at width `w`, as a function of the label. -/
def progW (T : List Quint) (w : ℕ) (i : ℕ) : Option Op :=
  if i.unpair.1 = 0 then
    if i.unpair.2.unpair.2.unpair.2.unpair.1 < w then
      some (if i.unpair.2.unpair.1 = 0 then
          .half2 (lRd 0 i.unpair.2.unpair.2.unpair.1 (i.unpair.2.unpair.2.unpair.2.unpair.1 + 1)
              i.unpair.2.unpair.2.unpair.2.unpair.2)
            (lRd 0 i.unpair.2.unpair.2.unpair.1 (i.unpair.2.unpair.2.unpair.2.unpair.1 + 1)
              (i.unpair.2.unpair.2.unpair.2.unpair.2 + 2 ^ i.unpair.2.unpair.2.unpair.2.unpair.1))
        else
          .half1 (lRd 1 i.unpair.2.unpair.2.unpair.1 (i.unpair.2.unpair.2.unpair.2.unpair.1 + 1)
              i.unpair.2.unpair.2.unpair.2.unpair.2)
            (lRd 1 i.unpair.2.unpair.2.unpair.1 (i.unpair.2.unpair.2.unpair.2.unpair.1 + 1)
              (i.unpair.2.unpair.2.unpair.2.unpair.2 + 2 ^ i.unpair.2.unpair.2.unpair.2.unpair.1)))
    else if i.unpair.2.unpair.1 = 0 then
      (look T i.unpair.2.unpair.2.unpair.1 i.unpair.2.unpair.2.unpair.2.unpair.2).map (act w)
    else some (pushOp 2 i.unpair.2.unpair.2.unpair.2.unpair.2 w (lRd 0 i.unpair.2.unpair.2.unpair.1 0 0))
  else if i.unpair.1 = 1 then
    some (pushOp i.unpair.2.unpair.1 i.unpair.2.unpair.2.unpair.1
      i.unpair.2.unpair.2.unpair.2.unpair.1 i.unpair.2.unpair.2.unpair.2.unpair.2)
  else if i.unpair.1 = 2 then some (.dbl1 false (lNrm' i.unpair.2))
  else if i.unpair.1 = 3 then some (.half1 (lRd 0 i.unpair.2 0 0) (lRd 0 i.unpair.2 0 0))
  else none

/-- **The TRM program of `T`.** -/
def prog (T : List Quint) : ℕ → Option Op := progW T (width T)

theorem progW_rd0_lt {T : List Quint} {w q j acc : ℕ} (hj : j < w) :
    progW T w (lRd 0 q j acc) = some (.half2 (lRd 0 q (j + 1) acc) (lRd 0 q (j + 1) (acc + 2 ^ j))) := by
  simp [progW, lRd, hj]

theorem progW_rd1_lt {T : List Quint} {w q j acc : ℕ} (hj : j < w) :
    progW T w (lRd 1 q j acc) = some (.half1 (lRd 1 q (j + 1) acc) (lRd 1 q (j + 1) (acc + 2 ^ j))) := by
  simp [progW, lRd, hj]

theorem progW_rd0_w {T : List Quint} {w q acc : ℕ} :
    progW T w (lRd 0 q w acc) = (look T q acc).map (act w) := by
  simp [progW, lRd]

theorem progW_rd1_w {T : List Quint} {w q acc : ℕ} :
    progW T w (lRd 1 q w acc) = some (pushOp 2 acc w (lRd 0 q 0 0)) := by
  simp [progW, lRd]

theorem progW_push {T : List Quint} {w r v k c : ℕ} :
    progW T w (lPush r v k c) = some (pushOp r v k c) := by
  simp [progW, lPush]

theorem progW_nrm {T : List Quint} {w q : ℕ} : progW T w (lNrm q) = some (.dbl1 false (lNrm' q)) := by
  simp [progW, lNrm]

theorem progW_nrm' {T : List Quint} {w q : ℕ} :
    progW T w (lNrm' q) = some (.half1 (lRd 0 q 0 0) (lRd 0 q 0 0)) := by
  simp [progW, lNrm']

/-! ### Encoder, decoder, invariant -/

/-- **Encoder** (`Code` of `T` → TRM configuration). -/
def enc (T : List Quint) (z : Code) : Cfg :=
  (if norm z = z then lRd 0 z.1 0 0 else lNrm z.1, num (2 ^ width T) z.2.1, num (2 ^ width T) z.2.2)

/-- **Decoder** (TRM configuration → `Code`), independent of the table: it reads `(q, w, s)`
    from a read-phase label `lRd 0 q w s`. -/
def dec (y : Cfg) : Option Code :=
  if y.1.unpair.1 = 0 ∧ y.1.unpair.2.unpair.1 = 0 then
    some (y.1.unpair.2.unpair.2.unpair.1,
      digs (2 ^ y.1.unpair.2.unpair.2.unpair.2.unpair.1) y.2.1 y.2.1,
      consT y.1.unpair.2.unpair.2.unpair.2.unpair.2
        (digs (2 ^ y.1.unpair.2.unpair.2.unpair.2.unpair.1) y.2.2 y.2.2))
  else none

theorem dec_rd (q w s X Y : ℕ) :
    dec (lRd 0 q w s, X, Y) = some (q, digs (2 ^ w) X X, consT s (digs (2 ^ w) Y Y)) := by
  simp [dec, lRd]

/-- **Invariant**: every symbol of the code is `< 2^width T`. -/
def Inv (T : List Quint) (z : Code) : Prop := ∀ x ∈ z.2.1 ++ z.2.2, x < 2 ^ width T

theorem enc_norm (T : List Quint) (z : Code) :
    enc T (norm z) = (lRd 0 z.1 0 0, num (2 ^ width T) z.2.1, num (2 ^ width T) z.2.2) := by
  simp [enc, norm, trim_trim, num_trim]

/-! ### Phases -/

section Phases
variable {T : List Quint} {w : ℕ}

theorem mod_pow_succ' (Y k : ℕ) : Y % 2 ^ (k + 1) = Y % 2 + 2 * (Y / 2 % 2 ^ k) := by
  rw [pow_succ', Nat.mod_mul]

theorem read0 (q X : ℕ) : ∀ k j acc Y, j + k ≤ w →
    ReflTransGen (Step (progW T w)) (lRd 0 q j acc, X, Y)
      (lRd 0 q (j + k) (acc + 2 ^ j * (Y % 2 ^ k)), X, Y / 2 ^ k) := by
  intro k
  induction k with
  | zero =>
    intro j acc Y _
    simp only [Nat.add_zero, Nat.pow_zero, Nat.mod_one, Nat.mul_zero, Nat.div_one]
    exact ReflTransGen.refl
  | succ k ih =>
    intro j acc Y hk
    have hs := step_of_prog (progW_rd0_lt (T := T) (q := q) (acc := acc) (show j < w by omega)) X Y
    have e : (Op.half2 (lRd 0 q (j + 1) acc) (lRd 0 q (j + 1) (acc + 2 ^ j))).exec X Y =
        (lRd 0 q (j + 1) (acc + 2 ^ j * (Y % 2)), X, Y / 2) := by
      rcases Nat.mod_two_eq_zero_or_one Y with h | h <;> simp [Op.exec, h]
    rw [e] at hs
    have := ih (j + 1) (acc + 2 ^ j * (Y % 2)) (Y / 2) (by omega)
    have e1 : j + 1 + k = j + (k + 1) := by omega
    have e2 : acc + 2 ^ j * (Y % 2) + 2 ^ (j + 1) * (Y / 2 % 2 ^ k) = acc + 2 ^ j * (Y % 2 ^ (k + 1)) := by
      rw [mod_pow_succ', pow_succ]; ring
    have e3 : Y / 2 / 2 ^ k = Y / 2 ^ (k + 1) := by rw [Nat.div_div_eq_div_mul, pow_succ']
    rw [e1, e2, e3] at this
    exact ReflTransGen.head hs this

theorem read1 (q Y : ℕ) : ∀ k j acc X, j + k ≤ w →
    ReflTransGen (Step (progW T w)) (lRd 1 q j acc, X, Y)
      (lRd 1 q (j + k) (acc + 2 ^ j * (X % 2 ^ k)), X / 2 ^ k, Y) := by
  intro k
  induction k with
  | zero =>
    intro j acc X _
    simp only [Nat.add_zero, Nat.pow_zero, Nat.mod_one, Nat.mul_zero, Nat.div_one]
    exact ReflTransGen.refl
  | succ k ih =>
    intro j acc X hk
    have hs := step_of_prog (progW_rd1_lt (T := T) (q := q) (acc := acc) (show j < w by omega)) X Y
    have e : (Op.half1 (lRd 1 q (j + 1) acc) (lRd 1 q (j + 1) (acc + 2 ^ j))).exec X Y =
        (lRd 1 q (j + 1) (acc + 2 ^ j * (X % 2)), X / 2, Y) := by
      rcases Nat.mod_two_eq_zero_or_one X with h | h <;> simp [Op.exec, h]
    rw [e] at hs
    have := ih (j + 1) (acc + 2 ^ j * (X % 2)) (X / 2) (by omega)
    have e1 : j + 1 + k = j + (k + 1) := by omega
    have e2 : acc + 2 ^ j * (X % 2) + 2 ^ (j + 1) * (X / 2 % 2 ^ k) = acc + 2 ^ j * (X % 2 ^ (k + 1)) := by
      rw [mod_pow_succ', pow_succ]; ring
    have e3 : X / 2 / 2 ^ k = X / 2 ^ (k + 1) := by rw [Nat.div_div_eq_div_mul, pow_succ']
    rw [e1, e2, e3] at this
    exact ReflTransGen.head hs this

theorem mod_pow_succ_bit (v k : ℕ) : v % 2 ^ (k + 1) = v % 2 ^ k + 2 ^ k * (v / 2 ^ k % 2) := by
  rw [pow_succ, Nat.mod_mul]

theorem pushX (v c : ℕ) : ∀ k, 1 ≤ k → ∀ i X Y, progW T w i = some (pushOp 1 v k c) →
    TransGen (Step (progW T w)) (i, X, Y) (c, 2 ^ k * X + v % 2 ^ k, Y) := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
    intro i X Y hi
    have hs := step_of_prog hi X Y
    simp only [pushOp, if_true, le_refl, Op.exec, bit_toNat] at hs
    refine TransGen.single ?_
    convert hs using 3
    simp
  | succ k hk ih =>
    intro i X Y hi
    have hs := step_of_prog hi X Y
    simp only [pushOp, if_true, Op.exec, show ¬ k + 1 ≤ 1 by omega, if_false,
      Nat.add_sub_cancel] at hs
    have := ih _ (2 * X + (bit v k).toNat) Y progW_push
    refine TransGen.head hs ?_
    convert this using 3
    rw [bit_toNat, mod_pow_succ_bit, pow_succ]; ring

theorem pushY (v c : ℕ) : ∀ k, 1 ≤ k → ∀ i X Y, progW T w i = some (pushOp 2 v k c) →
    TransGen (Step (progW T w)) (i, X, Y) (c, X, 2 ^ k * Y + v % 2 ^ k) := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
    intro i X Y hi
    have hs := step_of_prog hi X Y
    simp only [pushOp, show (2 : ℕ) ≠ 1 by omega, if_false, le_refl, if_true, Op.exec,
      bit_toNat] at hs
    refine TransGen.single ?_
    convert hs using 3
    simp
  | succ k hk ih =>
    intro i X Y hi
    have hs := step_of_prog hi X Y
    simp only [pushOp, show (2 : ℕ) ≠ 1 by omega, Op.exec, show ¬ k + 1 ≤ 1 by omega, if_false,
      Nat.add_sub_cancel] at hs
    have := ih _ X (2 * Y + (bit v k).toNat) progW_push
    refine TransGen.head hs ?_
    convert this using 3
    rw [bit_toNat, mod_pow_succ_bit, pow_succ]; ring

end Phases

/-! ### One TM step, halting, and the exact simulation -/

theorem mem_symbols {T : List Quint} {r : Quint} (hr : r ∈ T) : r.t ∈ symbols T := by
  simp only [symbols, List.mem_flatMap]
  exact ⟨r, hr, by simp⟩

theorem look_t_lt {T : List Quint} {q s : ℕ} {o : ℕ × ℕ × ℕ} (h : look T q s = some o) :
    o.1 < 2 ^ width T := by
  obtain ⟨r, hr, -, -, rfl⟩ := look_some h
  exact lt_width (mem_symbols hr)

/-- The read phase from a normalised code's image. -/
theorem read_phase (T : List Quint) (q : ℕ) (L R : List ℕ) (hR : ∀ x ∈ R, x < 2 ^ width T) :
    ReflTransGen (Step (prog T)) (lRd 0 q 0 0, num (2 ^ width T) L, num (2 ^ width T) R)
      (lRd 0 q (width T) (R.headD 0), num (2 ^ width T) L, num (2 ^ width T) R.tail) := by
  have h := read0 (T := T) (w := width T) q (num (2 ^ width T) L) (width T) 0 0
    (num (2 ^ width T) R) (by omega)
  obtain ⟨hm, hd⟩ := num_head (by have := two_le_B T; omega) hR
  unfold prog
  simpa [hm, hd] using h

theorem fwd_step {T : List Quint} {z : Code} {o : ℕ × ℕ × ℕ} (hz : norm z = z) (hinv : Inv T z)
    (hl : look T z.1 (z.2.2.headD 0) = some o) :
    TransGen (Step (prog T)) (enc T z) (enc T (norm (mv o z))) := by
  obtain ⟨q, L, R⟩ := z
  obtain ⟨t, d, q'⟩ := o
  set B := 2 ^ width T with hBdef
  have hB : 2 ≤ B := two_le_B T
  have hL : ∀ x ∈ L, x < B := fun x hx => hinv x (List.mem_append_left _ hx)
  have hR : ∀ x ∈ R, x < B := fun x hx => hinv x (List.mem_append_right _ hx)
  have ht : t < B := look_t_lt hl
  have henc : enc T (q, L, R) = (lRd 0 q 0 0, num B L, num B R) := by
    simp only [enc, hz, ite_true]; rfl
  rw [henc, enc_norm]
  have h1 := read_phase T q L R hR
  have hact : prog T (lRd 0 q (width T) (R.headD 0)) = some (act (width T) (t, d, q')) := by
    simp only [prog, progW_rd0_w]; rw [show look T q (R.headD 0) = _ from hl]; rfl
  have hw : 1 ≤ width T := by unfold width; omega
  by_cases hd0 : d = 0
  · subst hd0
    simp only [act, if_true] at hact
    have h2 := pushY (T := T) (w := width T) t (lRd 1 q' 0 0) (width T) hw _
      (num B L) (num B R.tail) hact
    have h3 := read1 (T := T) (w := width T) q' (2 ^ width T * num B R.tail + t % 2 ^ width T)
      (width T) 0 0 (num B L) (by omega)
    obtain ⟨hm, hdv⟩ := num_head (by omega) hL
    have hs' : L.headD 0 < B := headD_lt (by omega) hL
    have h4 := pushY (T := T) (w := width T) (L.headD 0) (lRd 0 q' 0 0) (width T) hw _
      (num B L.tail) (2 ^ width T * num B R.tail + t % 2 ^ width T) progW_rd1_w
    simp only [zero_add, pow_zero, one_mul] at h3
    rw [← hBdef, hm, hdv] at h3
    rw [← hBdef] at h2 h4
    have e : (lRd 0 q' 0 0, num B L.tail,
        B * (B * num B R.tail + t % B) + L.headD 0 % B) =
        (lRd 0 q' 0 0, num B (mv (t, 0, q') (q, L, R)).2.1, num B (mv (t, 0, q') (q, L, R)).2.2) := by
      simp only [mv, if_true, num, Nat.mod_eq_of_lt ht, Nat.mod_eq_of_lt hs']; ring_nf
    rw [e] at h4
    exact (TransGen.trans_right h1 (h2.trans_left h3)).trans h4
  · by_cases hd1 : d = 1
    · subst hd1
      simp only [act, show (1 : ℕ) ≠ 0 by omega, if_false, if_true] at hact
      have h2 := pushY (T := T) (w := width T) t (lRd 0 q' 0 0) (width T) hw _
        (num B L) (num B R.tail) hact
      rw [← hBdef, Nat.mod_eq_of_lt ht] at h2
      have e : (lRd 0 q' 0 0, num B L, B * num B R.tail + t) =
          (lRd 0 q' 0 0, num B (mv (t, 1, q') (q, L, R)).2.1, num B (mv (t, 1, q') (q, L, R)).2.2) := by
        simp only [mv, show (1 : ℕ) ≠ 0 by omega, if_false, if_true, num]; ring_nf
      rw [e] at h2
      exact TransGen.trans_right h1 h2
    · simp only [act, hd0, hd1, if_false] at hact
      have h2 := pushX (T := T) (w := width T) t (lRd 0 q' 0 0) (width T) hw _
        (num B L) (num B R.tail) hact
      rw [← hBdef, Nat.mod_eq_of_lt ht] at h2
      have e : (lRd 0 q' 0 0, B * num B L + t, num B R.tail) =
          (lRd 0 (mv (t, d, q') (q, L, R)).1 0 0, num B (mv (t, d, q') (q, L, R)).2.1,
            num B (mv (t, d, q') (q, L, R)).2.2) := by
        simp only [mv, hd0, hd1, if_false, num]; ring_nf
      rw [e] at h2
      exact TransGen.trans_right h1 h2

theorem inv_norm {T : List Quint} {z : Code} (h : Inv T z) : Inv T (norm z) := by
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact h x (List.mem_append_left _ (mem_trim hx))
  · exact h x (List.mem_append_right _ (mem_trim hx))

theorem inv_mv {T : List Quint} {z : Code} {o : ℕ × ℕ × ℕ} (h : Inv T z) (ht : o.1 < 2 ^ width T) :
    Inv T (mv o z) := by
  have hB : 0 < 2 ^ width T := by have := two_le_B T; omega
  have hL : ∀ x ∈ z.2.1, x < 2 ^ width T := fun x hx => h x (List.mem_append_left _ hx)
  have hR : ∀ x ∈ z.2.2, x < 2 ^ width T := fun x hx => h x (List.mem_append_right _ hx)
  have hs := headD_lt hB hL
  intro x hx
  unfold mv at hx
  split_ifs at hx <;> simp only [List.mem_append, List.mem_cons] at hx
  · rcases hx with hx | rfl | rfl | hx
    · exact hL x (List.mem_of_mem_tail hx)
    · exact hs
    · exact ht
    · exact hR x (List.mem_of_mem_tail hx)
  · rcases hx with hx | rfl | hx
    · exact hL x hx
    · exact ht
    · exact hR x (List.mem_of_mem_tail hx)
  · rcases hx with (rfl | hx) | hx
    · exact ht
    · exact hL x hx
    · exact hR x (List.mem_of_mem_tail hx)

/-- **L1 (exact simulation)**: for every table `T`, the code-level system of `T` on codes whose
    symbols are `< 2^width T` is simulated exactly by the TRM `prog T`, with encoder `enc T`
    and the table-independent decoder `dec`. -/
theorem sim (T : List Quint) :
    ExactSim (Inv T) (CStep T) (CHalt T) (Step (prog T)) (Halt (prog T)) (enc T) dec where
  inv_step z z' hinv h := by
    unfold CStep cstep at h
    split_ifs at h with hn
    · cases hz : zstep T z with
      | none => rw [hz] at h; cases h
      | some z'' =>
        rw [hz] at h; cases h
        unfold zstep at hz
        cases hl : look T z.1 (z.2.2.headD 0) with
        | none => rw [hl] at hz; cases hz
        | some o =>
          rw [hl] at hz; cases hz
          exact inv_norm (inv_mv hinv (look_t_lt hl))
    · cases h; exact inv_norm hinv
  prog z _ := by
    cases h : cstep T z with
    | none => exact Or.inl h
    | some z' => exact Or.inr ⟨z', h⟩
  fwd z z' hinv h := by
    unfold CStep cstep at h
    split_ifs at h with hn
    · cases hz : zstep T z with
      | none => rw [hz] at h; cases h
      | some z'' =>
        rw [hz] at h; cases h
        unfold zstep at hz
        cases hl : look T z.1 (z.2.2.headD 0) with
        | none => rw [hl] at hz; cases hz
        | some o =>
          rw [hl] at hz; cases hz
          exact fwd_step hn hinv hl
    · cases h
      rw [enc_norm]
      have e : enc T z = (lNrm z.1, num (2 ^ width T) z.2.1, num (2 ^ width T) z.2.2) := by
        simp [enc, hn]
      rw [e]
      have s1 := step_of_prog (progW_nrm (T := T) (w := width T) (q := z.1))
        (num (2 ^ width T) z.2.1) (num (2 ^ width T) z.2.2)
      have s2 := step_of_prog (progW_nrm' (T := T) (w := width T) (q := z.1))
        (2 * num (2 ^ width T) z.2.1 + false.toNat) (num (2 ^ width T) z.2.2)
      simp only [Op.exec, Bool.toNat_false, add_zero, ite_self] at s1 s2
      rw [show 2 * num (2 ^ width T) z.2.1 / 2 = num (2 ^ width T) z.2.1 by omega] at s2
      exact TransGen.head s1 (TransGen.single s2)
  halt z hinv h := by
    obtain ⟨hn, hz⟩ := chalt_iff.mp h
    obtain ⟨q, L, R⟩ := z
    have hR : ∀ x ∈ R, x < 2 ^ width T := fun x hx => hinv x (List.mem_append_right _ hx)
    have hL : ∀ x ∈ L, x < 2 ^ width T := fun x hx => hinv x (List.mem_append_left _ hx)
    have hl : look T q (R.headD 0) = none := by
      unfold zstep at hz; simpa using hz
    refine ⟨(lRd 0 q (width T) (R.headD 0), num (2 ^ width T) L, num (2 ^ width T) R.tail),
      ?_, ?_, ?_⟩
    · rw [show enc T (q, L, R) = (lRd 0 q 0 0, num (2 ^ width T) L, num (2 ^ width T) R) by
        simp [enc, hn]]
      exact read_phase T q L R hR
    · show prog T (lRd 0 q (width T) (R.headD 0)) = none
      simp only [prog, progW_rd0_w, hl, Option.map_none]
    · rw [dec_rd]
      have hB := two_le_B T
      have hRt : ∀ x ∈ R.tail, x < 2 ^ width T := fun x hx => hR x (List.mem_of_mem_tail hx)
      rw [digs_num hB L hL _ le_rfl, digs_num hB R.tail hRt _ le_rfl, ← trim_eq_consT]
      simp only [norm, Prod.mk.injEq] at hn
      rw [hn.2.1, hn.2.2]
  detY := det _
  stuckY := stuck _

/-! ### Entry for `tm n` (bridge hypothesis `hin`) -/

/-- **`hin`** of `isUTMStrict_of_chain`, with `stepX n := CStep (tbl n)`,
    `haltX n := CHalt (tbl n)`, `InvX n := Inv (tbl n)`. -/
theorem hin (n : ℕ) (a : Code) (h : IsIDOf (tm n) (toID 0 a)) :
    Inv (tbl n) a ∧ RunSim (Spec.Step (tm n)) (Halted (tm n)) (CStep (tbl n)) (CHalt (tbl n))
      (fun β z => toID β.pos z = β) (toID 0 a) a := by
  obtain ⟨hs, hr⟩ := entry_tm n a h
  refine ⟨fun x hx => ?_, hr⟩
  rcases hs x hx with rfl | hx
  · exact Nat.pos_of_ne_zero (by positivity)
  · exact lt_width hx

/-- **`hmid` for L1** of `isUTMStrict_of_chain` (to be composed with L2, L3 by `ExactSim.trans`). -/
theorem hmid (n : ℕ) :
    ExactSim (Inv (tbl n)) (CStep (tbl n)) (CHalt (tbl n)) (Step (prog (tbl n)))
      (Halt (prog (tbl n))) (enc (tbl n)) dec :=
  sim (tbl n)

/-- **Spec `tm n` → TRM** at run level: halting runs are matched with exact readback of the
    Spec halting ID (through `dec` then `toID`), non-halting by non-halting. -/
theorem tm_runSim_trm (n : ℕ) (a : Code) (h : IsIDOf (tm n) (toID 0 a)) :
    RunSim (Spec.Step (tm n)) (Halted (tm n)) (Step (prog (tbl n))) (Halt (prog (tbl n)))
      (fun β y => ∃ z, toID β.pos z = β ∧ dec y = some z) (toID 0 a) (enc (tbl n) a) := by
  obtain ⟨hi, he⟩ := hin n a h
  exact he.trans ((sim (tbl n)).runSim hi)

/-- **Bridge with L0 and L1 filled in**: `IsUTMStrict U` follows from computable `c`, `d`,
    `c(n, a) ∈ ID(U)`, an exact simulation of the TRM `prog (tbl n)` by the rest of the middle
    chain (L2–L3, `hrest`, whose invariant must hold on L1's images), and the exit layer
    (L4, `hout`) with readback through `(decR y).bind dec`. -/
theorem isUTMStrict_of_trm {Y : Type*} (U : List Quint)
    (c : ℕ × Code → Code) (d : Code → Option Code) (hc : Computable c) (hd : Computable d)
    (InvY : ℕ → Cfg → Prop) (stepY : ℕ → Y → Y → Prop) (haltY : ℕ → Y → Prop)
    (encR : ℕ → Cfg → Y) (decR : Y → Option Cfg)
    (hrest : ∀ n, ExactSim (InvY n) (Step (prog (tbl n))) (Halt (prog (tbl n))) (stepY n) (haltY n)
      (encR n) decR)
    (hinvY : ∀ n z, Inv (tbl n) z → InvY n (enc (tbl n) z))
    (hID : ∀ n a, IsIDOf (tm n) (toID 0 a) → IsIDOf U (toID 0 (c (n, a))))
    (hout : ∀ n a, IsIDOf (tm n) (toID 0 a) →
      RunSim (stepY n) (haltY n) (Spec.Step U) (Halted U)
        (fun y γ => ∃ g, toID γ.pos g = γ ∧ d g = (decR y).bind dec)
        (encR n (enc (tbl n) a)) (toID 0 (c (n, a))))
    (hdinv : ∀ p g g', toID p g = toID p g' → d g = d g') :
    IsUTMStrict U :=
  isUTMStrict_of_chain U c d hc hd (fun n => CStep (tbl n)) (fun n => CHalt (tbl n))
    (fun n => Inv (tbl n)) stepY haltY (fun n => encR n ∘ enc (tbl n))
    (fun y => (decR y).bind dec) hID hin (fun n => (sim (tbl n)).trans (hrest n) (hinvY n)) hout
    hdinv

end URTM.Univ.L1
