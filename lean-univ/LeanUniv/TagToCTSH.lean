/-
  **2-TS → CTSH** (Morita 2017 Thm 7.2, re-indexed; docs/24 §2 L3, piece P3).

  Morita encodes symbols by their index in an enumeration of the non-halting and the halting
  symbols. We index by the **symbol number itself** (no `idxOf`): for the alphabet `[0, S)`
  and `k := S`,

      ϕ(x) = N^{x+1} Y N^{S-x-1}   if P x ≠ none         (length S+1)
      ϕ(x) = Y · bin_S(x)          if P x = none         (length S+1)
      Ĉ    = (2S+2, (halt, w₁, …, w_{2S+1})),  w_i = ϕ(P(i-1)) if i-1 < S and P(i-1) ≠ none,
                                               w_i = λ otherwise.

  The CTSH side is the zoo's `URTM.CTSH` (`CStep`, `Halting`), in which `Ĉ` is the list
  `[w₁, …, w_{2S+1}]` (`ctsh`).

  The layer is stated as an `ExactSim` whose target configurations carry the CTSH:
  `Y := CTSH × ID`, `stepC`, `haltC`. This makes the decoder `dec` independent of the 2-TS
  (it reads `S = (|C| - 1) / 2` off the CTSH), as `isUTMStrict_of_chain` needs.

  **Length invariant.** Morita's proof ignores 2-TS halting by `|α| < 2`: a one-letter word
  `[a]` with `a` non-halting is halting in the 2-TS, but its image does not halt at a halting
  ID of the right shape. `exactSim` therefore takes an invariant `J` closed under steps that
  excludes `Short` words; `exactSim_noShort` instantiates `J := NoShort P`.
-/
import LeanUniv.ExactSim
import LeanUniv.TagSystem
import URTM.CTSH
import Mathlib.Tactic.Ring

namespace URTM.Univ.TagToCTSH
open Relation URTM.CTSH
open URTM.Univ.Tag (Step Halt Short NoShort)

/-! ### Binary blocks -/

/-- `bin k x`: the low `k` bits of `x`, most significant first (`Y` = 1, `N` = 0). -/
def bin : ℕ → ℕ → List Ch
  | 0, _ => []
  | k + 1, x => bin k (x / 2) ++ [if x % 2 = 1 then .Y else .N]

def bitv : Ch → ℕ
  | .Y => 1
  | .N => 0

/-- Value of a binary block, most significant first. -/
def binval (l : List Ch) : ℕ := l.foldl (fun acc c => 2 * acc + bitv c) 0

theorem binval_append_single (l : List Ch) (c : Ch) :
    binval (l ++ [c]) = 2 * binval l + bitv c := by
  simp [binval, List.foldl_append]

theorem bin_length (k x : ℕ) : (bin k x).length = k := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih => simp [bin, ih]

theorem binval_bin (k x : ℕ) : binval (bin k x) = x % 2 ^ k := by
  induction k generalizing x with
  | zero => simp [bin, binval, Nat.mod_one]
  | succ k ih =>
    rw [bin, binval_append_single, ih]
    have hb : bitv (if x % 2 = 1 then .Y else .N) = x % 2 := by
      split <;> simp [bitv] <;> omega
    rw [hb, pow_succ]
    have h1 := Nat.div_add_mod x 2
    have h2 := Nat.div_add_mod (x / 2) (2 ^ k)
    have hM : 0 < 2 ^ k := Nat.two_pow_pos k
    have hlt := Nat.mod_lt (x / 2) hM
    have hr := Nat.mod_lt x (show 0 < 2 by decide)
    set M := 2 ^ k
    set t := x / 2 / M
    set u := x / 2 % M
    have hx : x = (2 * u + x % 2) + (M * 2) * t := by
      calc x = 2 * (x / 2) + x % 2 := h1.symm
        _ = 2 * (M * t + u) + x % 2 := by rw [h2]
        _ = (2 * u + x % 2) + (M * 2) * t := by ring
    have := congrArg (· % (M * 2)) hx
    rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (a := 2 * u + x % 2) (b := M * 2) (by omega)]

/-! ### Leading `N` count -/

def leadN : List Ch → ℕ
  | .N :: r => leadN r + 1
  | _ => 0

theorem leadN_rep (n : ℕ) (l : List Ch) : leadN (List.replicate n .N ++ .Y :: l) = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, leadN, ih]

/-! ### The encoding ϕ -/

variable (S : ℕ) (P : ℕ → Option (List ℕ))

/-- ϕ on one symbol (indexed by the symbol number). -/
def phi (x : ℕ) : List Ch :=
  match P x with
  | some _ => List.replicate (x + 1) .N ++ .Y :: List.replicate (S - x - 1) .N
  | none => .Y :: bin S x

/-- ϕ on words (string homomorphism). -/
def phiW (w : List ℕ) : List Ch := w.flatMap (phi S P)

/-- The production `w_{j+1}` of `Ĉ` (for `j < 2S+1`). -/
def prodOf (j : ℕ) : List Ch :=
  if j < S then
    match P j with
    | some w => phiW S P w
    | none => []
  else []

/-- The CTSH `Ĉ = (2S+2, (halt, w₁, …, w_{2S+1}))`, as the zoo's list `[w₁, …, w_{2S+1}]`. -/
def ctsh : CTSH := (List.range (2 * S + 1)).map (prodOf S P)

/-- Target configurations carry the CTSH (so that the decoder is independent of the 2-TS). -/
abbrev CID := CTSH × URTM.CTSH.ID

/-- CTSH step on configurations that carry the CTSH (which never changes). -/
def stepC (p q : CID) : Prop := q.1 = p.1 ∧ CStep p.1 p.2 q.2

/-- CTSH halting (Def. 7.5: `(Y v, 0)` or `(λ, m)`, phase in range). -/
def haltC (p : CID) : Prop := Halting p.1 p.2

/-- Encoder: `w ↦ (Ĉ, (ϕ(w), 0))`. -/
def enc (w : List ℕ) : CID := (ctsh S P, (phiW S P w, 0))

/-! ### Decoder (independent of the 2-TS) -/

/-- Decode one block of length `k+1`. -/
def decBlock : List Ch → ℕ
  | .Y :: r => binval r
  | r => leadN r - 1

/-- Split into blocks of length `n` (fuel-bounded, structural). -/
def chunks {α : Type} (n : ℕ) : ℕ → List α → List (List α)
  | 0, _ => []
  | _ + 1, [] => []
  | f + 1, a :: l => (a :: l).take n :: chunks n f ((a :: l).drop n)

/-- ϕ⁻¹ for block length `k+1`. -/
def decWord (k : ℕ) (v : List Ch) : List ℕ := (chunks (k + 1) v.length v).map decBlock

/-- Decoder: read `S = (|C| - 1) / 2` off the CTSH and invert ϕ on the string. -/
def dec (p : CID) : Option (List ℕ) := some (decWord ((p.1.length - 1) / 2) p.2.1)

/-! ### Basic facts -/

variable {S P}

theorem phi_length {x : ℕ} (hx : x < S) : (phi S P x).length = S + 1 := by
  unfold phi
  split
  · simp; omega
  · simp [bin_length]

theorem decBlock_phi {x : ℕ} (hx : x < S) : decBlock (phi S P x) = x := by
  unfold phi
  split
  · rw [List.replicate_succ, List.cons_append]
    simp [decBlock, leadN, leadN_rep]
  · simp only [decBlock, binval_bin]
    exact Nat.mod_eq_of_lt (lt_trans hx (Nat.lt_two_pow_self))

/-- All symbols of a word are `< S`. -/
def AllLt (S : ℕ) (w : List ℕ) : Prop := ∀ y ∈ w, y < S

theorem phiW_length {w : List ℕ} (hw : AllLt S w) : (phiW S P w).length = (S + 1) * w.length := by
  induction w with
  | nil => simp [phiW]
  | cons a w ih =>
    simp only [phiW, List.flatMap_cons, List.length_append, List.length_cons] at ih ⊢
    rw [phi_length (hw a (by simp)), ih (fun y hy => hw y (by simp [hy]))]
    ring

theorem chunks_phiW {w : List ℕ} (hw : AllLt S w) :
    ∀ f, w.length ≤ f → chunks (S + 1) f (phiW S P w) = w.map (phi S P) := by
  induction w with
  | nil => intro f _; cases f <;> simp [phiW, chunks]
  | cons a w ih =>
    intro f hf
    obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by simp at hf; omega⟩
    have ha := phi_length (P := P) (hw a (by simp))
    have hrest := ih (fun y hy => hw y (by simp [hy])) f (by simp at hf; omega)
    simp only [phiW, List.flatMap_cons] at hrest ⊢
    obtain ⟨c, l, hcl⟩ : ∃ c l, phi S P a = c :: l := by
      cases h : phi S P a with
      | nil => rw [h] at ha; simp at ha
      | cons c l => exact ⟨c, l, rfl⟩
    rw [hcl, List.cons_append, chunks, ← List.cons_append, ← hcl, List.take_left' ha,
      List.drop_left' ha, hrest, List.map_cons]

theorem decWord_phiW {w : List ℕ} (hw : AllLt S w) : decWord S (phiW S P w) = w := by
  unfold decWord
  rw [chunks_phiW hw _ (by rw [phiW_length hw]; exact Nat.le_mul_of_pos_left _ (by omega)),
    List.map_map]
  conv_rhs => rw [← List.map_id w]
  refine List.map_congr_left fun x hx => ?_
  exact decBlock_phi (hw x hx)

/-! ### The CTSH `Ĉ` -/

theorem ctsh_length : (ctsh S P).length = 2 * S + 1 := by simp [ctsh]

theorem ctsh_k : (ctsh S P).k = 2 * S + 2 := by simp [CTSH.k, ctsh_length]

theorem prod_ctsh (j : ℕ) : prod (ctsh S P) (j + 1) = prodOf S P j := by
  simp only [prod, ctsh]
  rw [List.getD_eq_getElem?_getD]
  by_cases hj : j < 2 * S + 1
  · simp [hj]
  · simp [hj, prodOf, show ¬ j < S by omega]

/-- `j` leading `N`s are consumed without output. -/
theorem steps_N (C : CTSH) (v : List Ch) :
    ∀ (j m : ℕ), m < C.k →
      ReflTransGen (CStep C) (List.replicate j .N ++ v, m) (v, (m + j) % C.k) := by
  intro j
  induction j with
  | zero =>
    intro m hm
    simp only [List.replicate_zero, List.nil_append, Nat.add_zero, Nat.mod_eq_of_lt hm]
    exact ReflTransGen.refl
  | succ j ih =>
    intro m hm
    rw [List.replicate_succ, List.cons_append]
    refine ReflTransGen.head (CStep.n hm) ?_
    have hk : 0 < C.k := by simp [CTSH.k]
    have := ih ((m + 1) % C.k) (Nat.mod_lt _ hk)
    rwa [Nat.mod_add_mod, show m + 1 + j = m + (j + 1) by omega] at this

/-- In phases `S+1 … 2S+1` the productions are empty: any block is consumed without output. -/
theorem steps_blank (v : List Ch) :
    ∀ (u : List Ch) (m : ℕ), S + 1 ≤ m → m < 2 * S + 2 → m + u.length ≤ 2 * S + 2 →
      ReflTransGen (CStep (ctsh S P)) (u ++ v, m) (v, (m + u.length) % (2 * S + 2)) := by
  intro u
  induction u with
  | nil =>
    intro m _ hm _
    simp only [List.nil_append, List.length_nil, Nat.add_zero, Nat.mod_eq_of_lt hm]
    exact ReflTransGen.refl
  | cons c u ih =>
    intro m hm1 _ hm2
    simp only [List.length_cons] at hm2
    have hmk : m < (ctsh S P).k := by rw [ctsh_k]; omega
    have hstep : CStep (ctsh S P) (c :: (u ++ v), m) (u ++ v, (m + 1) % (2 * S + 2)) := by
      cases c with
      | Y =>
        obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
        have h := CStep.y (C := ctsh S P) (v := u ++ v) (by omega) hmk
        rwa [prod_ctsh, prodOf, if_neg (by omega), List.append_nil, ctsh_k] at h
      | N =>
        have h := CStep.n (C := ctsh S P) (v := u ++ v) hmk
        rwa [ctsh_k] at h
    rw [List.cons_append]
    refine ReflTransGen.head hstep ?_
    by_cases hu : u = []
    · subst hu
      simpa using ReflTransGen.refl
    · have hlen : 0 < u.length := List.length_pos_iff.mpr hu
      rw [Nat.mod_eq_of_lt (show m + 1 < 2 * S + 2 by omega)]
      have := ih (m + 1) (by omega) (by omega) (by omega)
      rwa [show m + 1 + u.length = m + (u.length + 1) by omega] at this

/-- **Morita Thm 7.2, one step**: `(ϕ(a b s), 0) ⇒^{2S+2} (ϕ(s P(a)), 0)`. -/
theorem sim_step {a b : ℕ} {s w : List ℕ} (ha : a < S) (hb : b < S) (hP : P a = some w) :
    TransGen (CStep (ctsh S P)) (phiW S P (a :: b :: s), 0) (phiW S P (s ++ w), 0) := by
  have hK := ctsh_k (S := S) (P := P)
  have hphia : phi S P a = List.replicate (a + 1) .N ++ .Y :: List.replicate (S - a - 1) .N := by
    simp [phi, hP]
  simp only [phiW, List.flatMap_cons, List.flatMap_append]
  rw [hphia, List.append_assoc]
  -- 1. `a+1` leading `N`s
  have h1 := steps_N (ctsh S P)
    (.Y :: (List.replicate (S - a - 1) .N ++ (phi S P b ++ s.flatMap (phi S P)))) (a + 1) 0
    (by omega)
  rw [hK, Nat.zero_add, Nat.mod_eq_of_lt (by omega)] at h1
  -- 2. the `Y` at phase `a+1` appends `ϕ(P a)`
  have h2 := CStep.y (C := ctsh S P)
    (v := List.replicate (S - a - 1) .N ++ (phi S P b ++ s.flatMap (phi S P)))
    (m := a + 1) (by omega) (by omega)
  rw [prod_ctsh, prodOf, if_pos ha, hP, hK, Nat.mod_eq_of_lt (show a + 1 + 1 < 2 * S + 2 by omega),
    List.append_assoc, List.append_assoc] at h2
  -- 3. the remaining `S-a-1` `N`s of `ϕ(a)`
  have h3 := steps_N (ctsh S P)
    (phi S P b ++ (s.flatMap (phi S P) ++ phiW S P w)) (S - a - 1) (a + 1 + 1) (by omega)
  rw [hK, Nat.mod_eq_of_lt (show a + 1 + 1 + (S - a - 1) < 2 * S + 2 by omega)] at h3
  -- 4. the block `ϕ(b)` in the blank phases `S+1 … 2S+1`
  have h4 := steps_blank (S := S) (P := P) (s.flatMap (phi S P) ++ phiW S P w) (phi S P b)
    (a + 1 + 1 + (S - a - 1)) (by omega) (by omega) (by rw [phi_length hb]; omega)
  rw [phi_length hb, show a + 1 + 1 + (S - a - 1) + (S + 1) = 2 * S + 2 by omega,
    Nat.mod_self] at h4
  exact (TransGen.tail' h1 h2).trans_left (h3.trans h4)

/-! ### The exact simulation -/

theorem stepC_det : Det stepC := by
  rintro ⟨C, s⟩ ⟨C₁, s₁⟩ ⟨C₂, s₂⟩ ⟨h₁, hs₁⟩ ⟨h₂, hs₂⟩
  simp only at h₁ h₂ hs₁ hs₂
  subst h₁ h₂
  rw [cstep_func hs₁ hs₂]

theorem haltC_stuck : ∀ y y', haltC y → ¬ stepC y y' := by
  rintro ⟨C, v, m⟩ ⟨C', s'⟩ hh ⟨-, hs⟩
  exact (halting_iff_noStep C v m hh.1).1 hh s' hs

theorem dec_enc {w : List ℕ} (hw : AllLt S w) : dec (enc S P w) = some w := by
  simp only [dec, enc, ctsh_length, show (2 * S + 1 - 1) / 2 = S by omega, decWord_phiW hw]

/-- **Re-indexed Morita Thm 7.2 as an `ExactSim`, over a sub-alphabet** (integration
    generalisation of `exactSim`): `A` is a set of symbols, all `< S` (`hA`), closed under the
    productions (`hWF`: a production of a symbol in `A` uses only symbols in `A`); symbols
    outside `A` are unconstrained (they are never reached). `J` is any invariant of the 2-TS
    that is closed under steps and excludes `Short` words (one-letter words with a
    non-halting letter, which Morita's proof does not treat). The instance `A := (· < S)`
    is `exactSim`. -/
theorem exactSim_mem (A : ℕ → Prop) (hA : ∀ y, A y → y < S)
    (hWF : ∀ a, A a → ∀ w, P a = some w → ∀ y ∈ w, A y)
    (J : List ℕ → Prop) (hJ : ∀ x x', J x → Step P x x' → J x')
    (hJs : ∀ x, J x → ¬ Short P x) :
    ExactSim (fun x => (∀ y ∈ x, A y) ∧ J x) (Step P) (Halt P) stepC haltC (enc S P) dec where
  inv_step := by
    rintro x x' ⟨hx, hJx⟩ hs
    refine ⟨?_, hJ _ _ hJx hs⟩
    cases hs with
    | @mk a b s w hP =>
      intro y hy
      rcases List.mem_append.1 hy with hy | hy
      · exact hx y (by simp [hy])
      · exact hWF a (hx a (by simp)) w hP y hy
  prog x _ := Tag.halt_or_step P x
  fwd := by
    rintro x x' ⟨hx, -⟩ hs
    cases hs with
    | @mk a b s w hP =>
      exact TransGen.lift (fun s => (ctsh S P, s)) (fun _ _ h => ⟨rfl, h⟩)
        (sim_step (hA a (hx a (by simp))) (hA b (hx b (by simp))) hP)
  halt := by
    rintro x ⟨hx, hJx⟩ hh
    refine ⟨enc S P x, ReflTransGen.refl, ?_, dec_enc fun y hy => hA y (hx y hy)⟩
    refine ⟨by simp [enc, ctsh_k], ?_⟩
    simp only [enc]
    match x, hh, hJs x hJx with
    | [], _, _ => exact .inr rfl
    | [a], _, hns =>
      cases hP : P a with
      | none => exact .inl ⟨bin S a ++ [], by simp [phiW, phi, hP], trivial⟩
      | some v => exact absurd ⟨a, v, rfl, hP⟩ hns
    | a :: b :: s, hh, _ =>
      exact .inl ⟨bin S a ++ phiW S P (b :: s), by simp [phiW, phi, show P a = none from hh], trivial⟩
  detY := stepC_det
  stuckY := haltC_stuck

/-- **Re-indexed Morita Thm 7.2 as an `ExactSim`**, for any invariant `J` of the 2-TS that is
    closed under steps and excludes `Short` words (one-letter words with a non-halting letter,
    which Morita's proof does not treat). `hWF`: productions of symbols `< S` use only symbols
    `< S`. -/
theorem exactSim (hWF : ∀ a < S, ∀ w, P a = some w → AllLt S w)
    (J : List ℕ → Prop) (hJ : ∀ x x', J x → Step P x x' → J x')
    (hJs : ∀ x, J x → ¬ Short P x) :
    ExactSim (fun x => AllLt S x ∧ J x) (Step P) (Halt P) stepC haltC (enc S P) dec :=
  exactSim_mem (· < S) (fun _ h => h) hWF J hJ hJs

/-- The instance with the weakest invariant: no reachable word is `Short`. -/
theorem exactSim_noShort (hWF : ∀ a < S, ∀ w, P a = some w → AllLt S w) :
    ExactSim (fun x => AllLt S x ∧ NoShort P x) (Step P) (Halt P) stepC haltC (enc S P) dec :=
  exactSim hWF (NoShort P) (fun _ _ h hs => h.step hs) (fun _ h => h.not_short)

end URTM.Univ.TagToCTSH
