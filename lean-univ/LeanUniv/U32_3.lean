/-
  **Morita's URTM(32,3) as a Spec table, and its universality in the sense of Def. 7.1**
  (docs/24 P7a).

  `U = numT num T`: the zoo's typed table `URTM.Gen.K32_3.T` (generated from Morita's description
  file `data/urtm/urtm32-3.txt`) numbered by enumeration: real states `q0..q31 ↦ 0..31`,
  pseudo-states `null (h0) ↦ 32`, `halt (h1) ↦ 33`, symbols `b y n ↦ 0 1 2`.

  The rule region uses two cells per letter (`URTM.CTSH.U32_3`): `Y ↦ yy`, `N ↦ ny`, the rule
  separator is `nn` and the phase marker is `nb`. Initial ID (Morita p. 194):

      b ϕ₂(w^R_{k−1}) nn ⋯ nn ϕ₂(w^R_1) nn nb b q_begin ϕ₁(w) b.

  Final tapes (`URTM.CTSH.U32_3.finList`): `(λ, m)`: `b · RA(m) · b · ϕ₁(rm)` in `null`;
  `(Y v, 0)`: `b · RA(0) · b · ϕ₁(rm) · b · ϕ₁(v)` in `halt` (a blank stands for the leading `Y`).

  * `encList C w`: the Spec code of the initial ID (`encList_eq`, `isIDOf_encList`,
    `encList_primrec`).
  * `readU g`: with `R` the window without its leading blanks, scan `R` in pairs of cells
    (`scan`) up to the first pair that starts with a blank: `|C|` is the number of pairs whose
    second cell is `n`. In the state `halt` the final string is `Y` followed by the second run
    of lower-case letters after the rule region (`tail32`); in any other state it is empty.
    `readU_toID`: it depends only on the ID; `readU_primrec`.
  * `isUTMStrict_U`: `IsUTMStrict U` by `ChainGen.isUTMStrict_of_ctsh`.
-/
import LeanUniv.NumGen
import LeanUniv.ChainGen
import URTM.CTSH32_3Main

namespace URTM.Univ.U32_3
open URTM URTM.CTSH URTM.Gen.K32_3 URTM.Univ.KToSpec URTM.Univ.NumGen
open URTM.Univ.U10_8 (loN)
open URTM.CTSH.U32_3 (nm32 encC32 finCfg32 urtm32_3_simulates_ctsh E blk Hi Lo LoCore RA
  tapeList finList p2 lo)

/-- The numbering of URTM(32,3). -/
def num : Numbering St Ps Sy :=
  numOf qs [.h0, .h1] ss hQ (by intro p; cases p <;> decide) hS

/-- **URTM(32,3) as a Spec table** (84 quintuples). -/
def U : List Quint := numT num T

/-- **Counts** (Morita's convention): 32 states, 3 symbols. -/
theorem U_counts : Spec.NStates U = 32 ∧ Spec.NSyms U = 3 := by decide +kernel
theorem U_det : Spec.Deterministic U := by decide +kernel
theorem U_rev : Spec.Reversible U := by decide +kernel

/-- **The description-file convention** (as for (10,8), `U10_8.U_zeroShift`). Morita's description
    file says: "There are 82 rules (except halting rules) in total. Note that, here, halting states
    "halt" and "null" are added to indicate which case occurred, but they should not be counted as
    the number of states." So `U` is the 82 quintuples plus the two halting quintuples
    `[begin_,b,b,0,null]` and `[case_y_2_,b,b,0,halt]`: the quintuples of `U` that enter a state without
    outgoing quintuples are exactly these two (0-shift, into two different pseudo-states), and
    they are exactly the 0-shift quintuples of `U`. `Spec.NStates` counts the states with outgoing
    quintuples. -/
theorem U_halting :
    U.filter (fun r => decide (r.q ∉ U.map Quint.p)) = [⟨0, 0, 0, .Z, 32⟩, ⟨2, 0, 0, .Z, 33⟩] ∧
    ∀ r ∈ U, (r.d = .Z ↔ r.q ∉ U.map Quint.p) := by decide +kernel

/-! ### The list-level encoder -/

/-- ϕ₂ reversed, on numbers: `Y ↦ y y`, `N ↦ y n`. -/
def p2r : Ch → List ℕ
  | .Y => [1, 1]
  | .N => [1, 2]

/-- **Encoder** (list level). State `begin = 0`; left of the head, nearest first: the separator
    `b`, the phase marker `b n` (`nb` reversed), then for each production `n n ϕ₂(w_i)^R`, then
    the left end `b`; from the head: `ϕ₁(w)`. -/
def encList (C : CTSH) (w : List Ch) : Spec.Code :=
  (0, 0 :: 0 :: 2 :: C.flatMap (fun u => 2 :: 2 :: u.flatMap p2r) ++ [0], w.map loN)

theorem sym_lo (c : Ch) : num.sym (lo nm32 c) = loN c := by cases c <;> rfl

theorem map_lo (u : List Ch) : (u.map (lo nm32)).map num.sym = u.map loN := by
  rw [List.map_map]
  exact List.map_congr_left fun c _ => sym_lo c

theorem p2_rev (c : Ch) : ((p2 nm32 c).map num.sym).reverse = p2r c := by cases c <;> rfl

theorem E_append (a b : List Ch) : E nm32 (a ++ b) = E nm32 a ++ E nm32 b := by
  simp [E]

theorem E_rev (u : List Ch) : ((E nm32 u.reverse).map num.sym).reverse = u.flatMap p2r := by
  induction u with
  | nil => rfl
  | cons c u ih =>
    rw [List.reverse_cons, E_append, List.map_append, List.reverse_append, ih]
    have : E nm32 [c] = p2 nm32 c := by simp [E]
    rw [this, p2_rev]
    rfl

theorem Hi_zero_rev (C : CTSH) :
    ((Hi nm32 C 0).map num.sym).reverse = C.flatMap (fun u => 2 :: 2 :: u.flatMap p2r) := by
  induction C with
  | nil => rfl
  | cons u C ih =>
    have : Hi nm32 (u :: C) 0 = Hi nm32 C 0 ++ blk nm32 u := by simp [Hi]
    rw [this, List.map_append, List.reverse_append, ih]
    simp only [blk, List.map_append, List.reverse_append, E_rev, List.flatMap_cons]
    rfl

theorem RA_zero (C : CTSH) : RA nm32 C 0 = Hi nm32 C 0 ++ [Sy.s2, Sy.s0] := by
  simp [RA, prod, E, Lo, nm32]

/-- The translation between typed positions and Spec positions: the head of `encC32 C w`. -/
def δ (C : CTSH) : ℤ := ((RA nm32 C 0).length + 2 : ℕ)

/-- The encoder is the numbered, shifted typed initial configuration. -/
theorem encList_eq (C : CTSH) (w : List Ch) :
    Spec.toID 0 (encList C w) = numCfg num (δ C) (encC32 C w) := by
  have e : encC32 C w = ⟨.go .q0, (((RA nm32 C 0).length + 2 : ℕ) : ℤ),
      Sim.tp .s0 (Sy.s0 :: RA nm32 C 0 ++ Sy.s0 :: w.map (lo nm32))⟩ := by
    simp [encC32, URTM.CTSH.U32_3.encC, URTM.CTSH.U32_3.rep, tapeList, nm32]
  have hL : Sy.s0 :: RA nm32 C 0 ++ Sy.s0 :: w.map (lo nm32) =
      (Sy.s0 :: RA nm32 C 0 ++ [Sy.s0]) ++ w.map (lo nm32) := by simp
  have hp : (RA nm32 C 0).length + 2 =
      ((Sy.s0 :: RA nm32 C 0 ++ [Sy.s0]).map num.sym).length := by simp
  rw [e, numCfg_tp (N := num) Sy.s0 rfl _ _ _ _ (by simp), δ, sub_self]
  congr 1
  simp only [window]
  rw [hL, List.map_append, List.take_left' hp.symm, List.drop_left' hp.symm]
  simp only [encList, RA_zero, List.map_append, List.map_cons, List.map_nil,
    List.reverse_append, List.reverse_cons, List.reverse_nil, Hi_zero_rev, map_lo]
  rfl

/-- The encoded initial ID is an ID of U (`c(n, α) ∈ ID(U)` of Morita Def. 7.1). -/
theorem isIDOf_encList (C : CTSH) (w : List Ch) : Spec.IsIDOf U (Spec.toID 0 (encList C w)) := by
  have hs : ∀ a ∈ [0, 1, 2], a = 0 ∨ a ∈ Spec.symbols U := by decide +kernel
  have h0 : (0 : ℕ) ∈ Spec.states U := by decide +kernel
  have hlo : ∀ c : Ch, loN c ∈ [0, 1, 2] := by intro c; cases c <;> decide
  have hp : ∀ c : Ch, ∀ a ∈ p2r c, a ∈ [0, 1, 2] := by intro c; cases c <;> decide
  refine isIDOf_toID U 0 _ h0 fun a ha => hs a ?_
  simp only [encList, List.mem_append, List.mem_cons, List.mem_flatMap, List.mem_map,
    List.not_mem_nil, or_false] at ha
  rcases ha with ((rfl | rfl | rfl | ⟨u, -, rfl | rfl | ⟨c, -, hc⟩⟩) | rfl) | ⟨c, -, rfl⟩
  · decide
  · decide
  · decide
  · decide
  · decide
  · exact hp c a hc
  · decide
  · exact hlo c

open Primrec in
theorem encList_primrec : Primrec₂ encList := by
  have C := (fst : Primrec fun p : URTM.CTSH.CTSH × List Ch => p.1)
  have w := (snd : Primrec fun p : URTM.CTSH.CTSH × List Ch => p.2)
  have hp : Primrec p2r := dom_finite _
  have fl := list_flatMap C (list_cons.comp (const 2) (list_cons.comp (const 2)
    (list_flatMap snd (hp.comp snd).to₂))).to₂
  exact (pair (const 0) (pair (list_append.comp (list_cons.comp (const 0)
    (list_cons.comp (const 0) (list_cons.comp (const 2) fl))) (const [0]))
    (list_map w (ComputableEnc.loN_primrec.comp snd).to₂))).of_eq fun _ => rfl

/-! ### The readout -/

/-- One step of the pair scan. State `(mode, count, consumed)`: mode `0` = at the first cell
    of a pair, `1` = at the second cell, `2` = done (a pair starting with a blank was met).
    `count` = pairs seen whose second cell is `n = 2`; `consumed` = cells consumed. -/
def scan (s : ℕ × ℕ × ℕ) (a : ℕ) : ℕ × ℕ × ℕ :=
  if s.1 = 0 then (if a = 0 then (2, s.2.1, s.2.2) else (1, s.2.1, s.2.2 + 1))
  else if s.1 = 1 then (0, s.2.1 + (if a = 2 then 1 else 0), s.2.2 + 1)
  else s

/-- After the rule region `b ϕ₁(rm) b ϕ₁(v)`: the second run of lower-case letters. -/
def tail32 (X : List ℕ) : List ℕ :=
  (((X.drop 1).dropWhile (fun a => a == 1 || a == 2)).drop 1).takeWhile
    (fun a => a == 1 || a == 2)

/-- The readout on the state `q` and the window without its leading blanks. -/
def readR (hs q : ℕ) (R : List ℕ) : ℕ × List ℕ :=
  if q = hs then ((R.foldl scan (0, 0, 0)).2.1,
    1 :: tail32 (R.drop (R.foldl scan (0, 0, 0)).2.2))
  else ((R.foldl scan (0, 0, 0)).2.1, [])

/-- The readout on the state and the whole window list. -/
def readL (hs q : ℕ) (L : List ℕ) : ℕ × List ℕ := readR hs q (L.dropWhile (· == 0))

/-- **Readout** (list level) from a code `g` of the halting ID: `(|C|, ϕ₁(vf))`. -/
def readU (g : Spec.Code) : Option (ℕ × List ℕ) :=
  some (readL 33 g.1 (g.2.1.reverse ++ g.2.2))

/-! #### The scan on arbitrary lists -/

theorem scan_done (s : ℕ × ℕ × ℕ) (h : 2 ≤ s.1) (X : List ℕ) : X.foldl scan s = s := by
  induction X with
  | nil => rfl
  | cons a X ih =>
    have : scan s a = s := by
      simp [scan, show s.1 ≠ 0 by omega, show s.1 ≠ 1 by omega]
    rw [List.foldl_cons, this, ih]

/-- While the scan is not done, it has consumed everything; it never consumes more than the
    list. -/
theorem scan_inv (X : List ℕ) : ∀ s : ℕ × ℕ × ℕ, s.1 ≤ 1 →
    ((X.foldl scan s).1 ≤ 1 → (X.foldl scan s).2.2 = s.2.2 + X.length) ∧
    (X.foldl scan s).2.2 ≤ s.2.2 + X.length := by
  induction X with
  | nil => intro s _; simp
  | cons a X ih =>
    intro s hs
    rw [List.foldl_cons]
    obtain ⟨m, c, p⟩ := s
    simp only at hs
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hs with rfl | rfl
    · by_cases ha : a = 0
      · have : scan (0, c, p) a = (2, c, p) := by simp [scan, ha]
        rw [this, scan_done _ (by simp)]
        simp
      · have : scan (0, c, p) a = (1, c, p + 1) := by simp [scan, ha]
        rw [this]
        obtain ⟨h1, h2⟩ := ih (1, c, p + 1) (by simp)
        simp only [List.length_cons] at h1 h2 ⊢
        exact ⟨fun h => by rw [h1 h]; omega, by omega⟩
    · have : scan (1, c, p) a = (0, c + (if a = 2 then 1 else 0), p + 1) := by simp [scan]
      rw [this]
      obtain ⟨h1, h2⟩ := ih (0, c + (if a = 2 then 1 else 0), p + 1) (by simp)
      simp only [List.length_cons] at h1 h2 ⊢
      exact ⟨fun h => by rw [h1 h]; omega, by omega⟩

/-- Scanning blanks keeps the count and consumes at most the blanks. -/
theorem scan_zeros (k : ℕ) : ∀ s : ℕ × ℕ × ℕ,
    ((List.replicate k 0).foldl scan s).2.1 = s.2.1 ∧
    s.2.2 ≤ ((List.replicate k 0).foldl scan s).2.2 ∧
    ((List.replicate k 0).foldl scan s).2.2 ≤ s.2.2 + k := by
  induction k with
  | zero => intro s; simp
  | succ k ih =>
    intro s
    rw [List.replicate_succ, List.foldl_cons]
    obtain ⟨m, c, p⟩ := s
    obtain ⟨h1, h2, h3⟩ := ih (scan (m, c, p) 0)
    have hc : (scan (m, c, p) 0).2.1 = c := by
      by_cases h0 : m = 0
      · simp [scan, h0]
      · by_cases h1 : m = 1
        · simp [scan, h1]
        · simp [scan, h0, h1]
    have hp : p ≤ (scan (m, c, p) 0).2.2 ∧ (scan (m, c, p) 0).2.2 ≤ p + 1 := by
      by_cases h0 : m = 0
      · simp [scan, h0]
      · by_cases h1 : m = 1
        · simp [scan, h1]
        · simp [scan, h0, h1]
    simp only at h1 h2 h3 ⊢
    exact ⟨h1.trans hc, by omega, by omega⟩

theorem drop1_pad (X : List ℕ) (j : ℕ) :
    ∃ j', (X ++ List.replicate j 0).drop 1 = X.drop 1 ++ List.replicate j' 0 := by
  cases X with
  | nil => exact ⟨j - 1, by cases j <;> simp [List.replicate_succ]⟩
  | cons a X => exact ⟨j, by simp⟩

theorem tail32_pad (X : List ℕ) (j : ℕ) : tail32 (X ++ List.replicate j 0) = tail32 X := by
  obtain ⟨j1, h1⟩ := drop1_pad X j
  simp only [tail32]
  rw [h1, PadInv.dw_append_rep_false (p := fun a => a == 1 || a == 2) rfl]
  obtain ⟨j2, h2⟩ := drop1_pad ((X.drop 1).dropWhile (fun a => a == 1 || a == 2)) j1
  rw [h2, PadInv.tw_append_rep (p := fun a => a == 1 || a == 2) rfl]

theorem readR_pad (hs q : ℕ) (R : List ℕ) (k : ℕ) :
    readR hs q (R ++ List.replicate k 0) = readR hs q R := by
  have hf : (R ++ List.replicate k 0).foldl scan (0, 0, 0) =
      (List.replicate k 0).foldl scan (R.foldl scan (0, 0, 0)) := List.foldl_append
  obtain ⟨hz1, hz2, hz3⟩ := scan_zeros k (R.foldl scan (0, 0, 0))
  obtain ⟨hi1, hi2⟩ := scan_inv R (0, 0, 0) (by simp)
  simp only [Nat.zero_add] at hi1 hi2
  have hcnt : ((R ++ List.replicate k 0).foldl scan (0, 0, 0)).2.1 =
      (R.foldl scan (0, 0, 0)).2.1 := by rw [hf, hz1]
  have htail : tail32 ((R ++ List.replicate k 0).drop
        ((R ++ List.replicate k 0).foldl scan (0, 0, 0)).2.2) =
      tail32 (R.drop (R.foldl scan (0, 0, 0)).2.2) := by
    rw [hf]
    by_cases hm : (R.foldl scan (0, 0, 0)).1 ≤ 1
    · have hp := hi1 hm
      obtain ⟨t, ht⟩ : ∃ t, ((List.replicate k 0).foldl scan (R.foldl scan (0, 0, 0))).2.2 =
          R.length + t := ⟨_, by rw [hp] at hz2; exact (Nat.add_sub_cancel' hz2).symm⟩
      have e1 : (R ++ List.replicate k 0).drop (R.length + t) = List.replicate (k - t) 0 := by
        simp [List.drop_append, List.drop_replicate]
      rw [ht, hp, List.drop_length, e1]
      simpa using tail32_pad [] (k - t)
    · rw [scan_done _ (by omega), List.drop_append_of_le_length hi2, tail32_pad]
  simp only [readR, hcnt, htail]

theorem readL_padL (hs q k : ℕ) (L : List ℕ) :
    readL hs q (List.replicate k 0 ++ L) = readL hs q L := by
  simp only [readL, PadInv.dw_rep_append (p := (· == 0)) rfl]

theorem readL_padR (hs q k : ℕ) (L : List ℕ) :
    readL hs q (L ++ List.replicate k 0) = readL hs q L := by
  have H := PadInv.dw_append_rep_true (p := (· == 0)) rfl L k
  simp only [readL]
  rcases hA : L.dropWhile (· == 0) with _ | ⟨x, t⟩
  · rw [H.1 hA]
  · rw [(H.2 x t hA).1, ← List.cons_append, readR_pad]

/-- **The readout depends only on the ID**, not on the code chosen for it. -/
theorem readU_toID {p : ℤ} {g g' : Spec.Code} (h : Spec.toID p g = Spec.toID p g') :
    readU g = readU g' :=
  congrArg some (read_toID (readL 33) (fun q k L => readL_padL 33 q k L)
    (fun q k L => readL_padR 33 q k L) h)

/-! #### The scan on the rule region -/

/-- `PSC X k`: `X` is a sequence of pairs of cells, each starting with a non-blank, `k` of which
    have second cell `n = 2`. -/
inductive PSC : List ℕ → ℕ → Prop
  | nil : PSC [] 0
  | cons (a b : ℕ) {X : List ℕ} {k : ℕ} : a ≠ 0 → PSC X k →
      PSC (a :: b :: X) ((if b = 2 then 1 else 0) + k)

theorem PSC.cast {X : List ℕ} {k n : ℕ} (h : PSC X k) (e : k = n) : PSC X n := e ▸ h

theorem PSC.append {X Y : List ℕ} {k j : ℕ} (hX : PSC X k) (hY : PSC Y j) :
    PSC (X ++ Y) (k + j) := by
  induction hX with
  | nil => simpa using hY
  | cons a b ha _ ih => exact (PSC.cons a b ha ih).cast (by omega)

theorem PSC.scan {X : List ℕ} {k : ℕ} (h : PSC X k) : ∀ (c p : ℕ) (Z : List ℕ),
    (X ++ Z).foldl scan (0, c, p) = Z.foldl scan (0, c + k, p + X.length) := by
  induction h with
  | nil => intro c p Z; simp
  | @cons a b X k ha _ ih =>
    intro c p Z
    have h2 : U32_3.scan (U32_3.scan (0, c, p) a) b =
        (0, c + (if b = 2 then 1 else 0), p + 1 + 1) := by simp [U32_3.scan, ha]
    have e1 : c + (if b = 2 then 1 else 0) + k = c + ((if b = 2 then 1 else 0) + k) :=
      Nat.add_assoc _ _ _
    have e2 : p + 1 + 1 + X.length = p + (a :: b :: X).length := by
      simp only [List.length_cons]; omega
    simp only [List.cons_append, List.foldl_cons]
    rw [h2, ih, e1, e2]

theorem PSC.dropWhile {X : List ℕ} {k : ℕ} (h : PSC X k) (hne : X ≠ []) (Z : List ℕ) :
    (X ++ Z).dropWhile (· == 0) = X ++ Z := by
  cases h with
  | nil => exact absurd rfl hne
  | cons a b ha _ => simp [ha]

theorem psc_E (w : List Ch) : PSC ((E nm32 w).map num.sym) 0 := by
  induction w with
  | nil => exact .nil
  | cons c w ih =>
    have : E nm32 (c :: w) = p2 nm32 c ++ E nm32 w := by simp [E]
    rw [this, List.map_append]
    cases c
    · exact (PSC.cons 1 1 (by decide) ih).cast (by simp)
    · exact (PSC.cons 2 1 (by decide) ih).cast (by simp)

theorem psc_blk (w : List Ch) : PSC ((blk nm32 w).map num.sym) 1 := by
  rw [blk, List.map_append]
  exact ((psc_E w.reverse).append (PSC.cons 2 2 (by decide) .nil)).cast (by simp)

theorem psc_blks (L : List (List Ch)) :
    PSC (((L.map (blk nm32)).flatten).map num.sym) L.length := by
  induction L with
  | nil => exact .nil
  | cons u L ih =>
    rw [List.map_cons, List.flatten_cons, List.map_append]
    exact ((psc_blk u).append ih).cast (by simp; omega)

/-- The rule region is a sequence of pairs with exactly `|C|` separators `nn`. -/
theorem psc_RA (C : CTSH) {m : ℕ} (hm : m ≤ C.length) :
    PSC ((RA nm32 C m).map num.sym) C.length := by
  have hLo : PSC ((Lo nm32 C m).map num.sym) m := by
    simp only [Lo]
    split
    · subst m; exact .nil
    · rw [List.map_append]
      exact ((psc_blks _).append (PSC.cons 2 2 (by decide) .nil)).cast (by simp; omega)
  have hmk : PSC (([nm32.n, nm32.b] ++ Lo nm32 C m).map num.sym) m := by
    rw [List.map_append]
    exact ((PSC.cons 2 0 (by decide) .nil).append hLo).cast (by simp)
  have : RA nm32 C m = Hi nm32 C m ++ (E nm32 (prod C m).reverse ++
      ([nm32.n, nm32.b] ++ Lo nm32 C m)) := by simp [RA]
  rw [this, List.map_append, List.map_append]
  exact ((psc_blks _).append ((psc_E _).append hmk)).cast (by simp; omega)

theorem RA_ne_nil (C : CTSH) (m : ℕ) : (RA nm32 C m).map num.sym ≠ [] := by
  simp [RA]

/-- The scan of the final tape: the count is `|C|` and the consumed prefix is the rule region. -/
theorem scan_tape (C : CTSH) {m : ℕ} (hm : m ≤ C.length) (rest : List ℕ) :
    ((RA nm32 C m).map num.sym ++ 0 :: rest).foldl scan (0, 0, 0) =
      (2, C.length, ((RA nm32 C m).map num.sym).length) := by
  rw [(psc_RA C hm).scan 0 0, List.foldl_cons]
  have : scan (0, 0 + C.length, 0 + ((RA nm32 C m).map num.sym).length) 0 =
      (2, C.length, ((RA nm32 C m).map num.sym).length) := by simp [scan]
  rw [this, scan_done _ (by simp)]

theorem readL_null (C : CTSH) {m : ℕ} (hm : m ≤ C.length) (rest : List ℕ) (q : ℕ)
    (hq : q ≠ 33) :
    readL 33 q (0 :: (RA nm32 C m).map num.sym ++ 0 :: rest) = (C.length, []) := by
  have hd : (0 :: (RA nm32 C m).map num.sym ++ 0 :: rest).dropWhile (· == 0) =
      (RA nm32 C m).map num.sym ++ 0 :: rest := by
    rw [List.cons_append, List.dropWhile_cons_of_pos (by rfl),
      (psc_RA C hm).dropWhile (RA_ne_nil C m)]
  simp only [readL, hd, readR, if_neg hq, scan_tape C hm]

theorem readL_halt (C : CTSH) (rm v : List Ch) :
    readL 33 33 (0 :: (RA nm32 C 0).map num.sym ++ 0 :: (rm.map loN ++ 0 :: v.map loN)) =
      (C.length, (Ch.Y :: v).map loN) := by
  have hd : (0 :: (RA nm32 C 0).map num.sym ++ 0 :: (rm.map loN ++ 0 :: v.map loN)).dropWhile
      (· == 0) = (RA nm32 C 0).map num.sym ++ 0 :: (rm.map loN ++ 0 :: v.map loN) := by
    rw [List.cons_append, List.dropWhile_cons_of_pos (by rfl),
      (psc_RA C (Nat.zero_le _)).dropWhile (RA_ne_nil C 0)]
  have hlo : ∀ (u : List Ch), ∀ a ∈ u.map loN, (a == 1 || a == 2) = true := by
    intro u a ha
    obtain ⟨c, -, rfl⟩ := List.mem_map.mp ha
    cases c <;> rfl
  simp only [readL, hd, readR, if_true, scan_tape C (Nat.zero_le _), List.drop_left', tail32,
    List.drop_succ_cons, List.drop_zero]
  rw [(U10_8.takeWhile_append_of_all (hlo rm) 0 rfl _).2]
  simp only [List.drop_succ_cons, List.drop_zero, U10_8.takeWhile_of_all (hlo v)]
  rfl

/-! #### Computability of the readout -/

open Primrec in
theorem scan_primrec : Primrec₂ scan := by
  have m : Primrec fun x : (ℕ × ℕ × ℕ) × ℕ => x.1.1 := fst.comp fst
  have c : Primrec fun x : (ℕ × ℕ × ℕ) × ℕ => x.1.2.1 := fst.comp (snd.comp fst)
  have p : Primrec fun x : (ℕ × ℕ × ℕ) × ℕ => x.1.2.2 := snd.comp (snd.comp fst)
  have a : Primrec fun x : (ℕ × ℕ × ℕ) × ℕ => x.2 := snd
  exact (Primrec.ite (Primrec.eq.comp m (const 0))
    (Primrec.ite (Primrec.eq.comp a (const 0)) (pair (const 2) (pair c p))
      (pair (const 1) (pair c (nat_add.comp p (const 1)))))
    (Primrec.ite (Primrec.eq.comp m (const 1))
      (pair (const 0) (pair (nat_add.comp c
        (Primrec.ite (Primrec.eq.comp a (const 2)) (const 1) (const 0)))
        (nat_add.comp p (const 1)))) fst)).to₂.of_eq fun _ _ => rfl

open Primrec in
theorem tail32_primrec : Primrec tail32 := by
  have p12 : Primrec fun a : ℕ => a == 1 || a == 2 :=
    Primrec.or.comp (Primrec.beq.comp .id (const 1)) (Primrec.beq.comp .id (const 2))
  exact (list_takeWhile p12).comp (list_tail.comp ((list_dropWhile p12).comp list_tail)) |>.of_eq
    fun X => by simp [tail32]

open Primrec in
theorem readU_primrec : Primrec readU := by
  have p0 : Primrec fun a : ℕ => a == 0 := Primrec.beq.comp .id (const 0)
  have hR : Primrec fun g : Spec.Code => (g.2.1.reverse ++ g.2.2).dropWhile (· == 0) :=
    (list_dropWhile p0).comp
      (list_append.comp (list_reverse.comp (fst.comp snd)) (snd.comp snd))
  have hs : Primrec fun g : Spec.Code =>
      ((g.2.1.reverse ++ g.2.2).dropWhile (· == 0)).foldl scan (0, 0, 0) :=
    list_foldl hR (const (0, 0, 0)) (scan_primrec.comp (fst.comp snd) (snd.comp snd)).to₂
  have hc := fst.comp (snd.comp hs)
  have ht := tail32_primrec.comp (list_drop.comp (snd.comp (snd.comp hs)) hR)
  exact (option_some.comp (Primrec.ite (Primrec.eq.comp fst (const 33))
    (pair hc (list_cons.comp (const 1) ht)) (pair hc (const [])))).of_eq fun g => by
      simp only [readU, readL, readR]

/-! ### The run-level simulation and the main theorem -/

/-- **URTM(32,3) simulates every CTSH at the level of Spec** (run level, exact readback). -/
theorem runSim_U (C : CTSH) (w : List Ch) :
    RunSim (CStep C) (Halting C) (Spec.Step U) (Spec.Halted U)
      (fun y γ => ∃ g, Spec.toID γ.pos g = γ ∧ readU g = some (C.length, y.1.map loN))
      (w, 0) (Spec.toID 0 (encList C w)) := by
  rw [encList_eq]
  obtain ⟨hF, -, hN⟩ := urtm32_3_simulates_ctsh C w
  refine runSim_of_sim num T _ C w (encC32 C w) (fun f c => ∃ rm, c = finCfg32 C f.1 f.2 rm) _
    (fun n f hf => ?_) (fun hn => hN.mp hn) (fun f c hf hc => ?_)
  · obtain ⟨M, rm, -, h⟩ := hF n f.1 f.2 hf
    exact ⟨M, _, h, rm, rfl⟩
  · obtain ⟨rm, rfl⟩ := hc
    obtain ⟨vf, mf⟩ := f
    obtain ⟨hk, hv | hv⟩ := hf
    · obtain ⟨v, hv1, hv2⟩ := hv
      simp only at hv1 hv2
      subst hv1 hv2
      have e : finCfg32 C (Ch.Y :: v) 0 rm = ⟨.halt .h1, ((RA nm32 C 0).length : ℕ),
          Sim.tp .s0 (finList nm32 C (Ch.Y :: v) 0 rm)⟩ := by
        simp [finCfg32, URTM.CTSH.U32_3.finCfg, nm32]
      simp only [e]
      refine read_of_tp num Sy.s0 rfl _ _ _ _ (by simp [finList]; omega) _ _ ?_
      have hL : (finList nm32 C (Ch.Y :: v) 0 rm).map num.sym =
          0 :: (RA nm32 C 0).map num.sym ++ 0 :: (rm.map loN ++ 0 :: v.map loN) := by
        simp only [finList, List.map_append, List.map_cons, map_lo]
        simp [nm32]
        rfl
      simp only [readU, window_whole, window_st, hL]
      exact congrArg some (readL_halt C rm v)
    · simp only at hv
      subst hv
      have hm : mf ≤ C.length := by simp [CTSH.k] at hk; omega
      have e : finCfg32 C [] mf rm = ⟨.halt .h0, (((RA nm32 C mf).length + 2 + rm.length : ℕ) : ℤ),
          Sim.tp .s0 (finList nm32 C [] mf rm)⟩ := by
        simp [finCfg32, URTM.CTSH.U32_3.finCfg, nm32]
      simp only [e]
      refine read_of_tp num Sy.s0 rfl _ _ _ _ (by simp [finList, tapeList]; omega) _ _ ?_
      have hL : (finList nm32 C [] mf rm).map num.sym =
          0 :: (RA nm32 C mf).map num.sym ++ 0 :: rm.map loN := by
        simp only [finList, tapeList, List.map_append, List.map_cons, map_lo, List.map_nil,
          List.append_nil]
        simp [nm32]
        rfl
      simp only [readU, window_whole, window_st, hL]
      exact congrArg some (readL_null C hm _ _ (by decide))

/-- **Body form** (docs/26): the body of `IsUTMStrict U` for the explicit encoder and decoder. -/
theorem body_U : DropGen.StrictBody U (ChainGen.cOf encList) (GenDec.dOf readU) :=
  ChainGen.strictBody_of_ctsh U encList readU isIDOf_encList runSim_U (fun _ _ _ h => readU_toID h)

/-- **URTM(32,3) is a UTM in the strict sense of Morita Def. 7.1.** -/
theorem isUTMStrict_U : Spec.IsUTMStrict U :=
  ChainGen.isUTMStrict_of_body_ctsh encList_primrec readU_primrec body_U

end URTM.Univ.U32_3
