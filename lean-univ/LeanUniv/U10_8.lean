/-
  **Morita's URTM(10,8) as a Spec table, with list-level encoder and readout** (docs/24 §2 L4,
  piece P7a, for (10,8) only).

  * `U : List Quint` is the zoo's typed table `URTM.Gen.K10_8.T` (generated from Morita's
    description file `data/urtm/urtm10-8.txt`) numbered by `num10_8`: real states
    `q0..q9 ↦ 0..9`, pseudo-states `null ↦ 10`, `halt ↦ 11`, symbols `s0..s7 ↦ 0..7` (blank
    `b = s0 ↦ 0`). Counts, determinism and reversibility in Spec's sense: `U_counts`,
    `U_det`, `U_rev` (`decide +kernel`).
  * `encList C w : Code` is the Spec code of Morita's initial ID of U for the CTSH `C` and
    the initial word `w` (head on the first letter of `w`, at Spec position 0):
    `b ϕ₁(w^R_{k−1}) ∗ ⋯ ∗ ϕ₁(w^R_1) ∗ b $ ▸ϕ₁(w)`. `encList_eq`: it is the numbered, shifted
    typed initial configuration `encC C w`. `isIDOf_encList`: it is an ID of U.
  * `readU g : Option (ℕ × CTSH.ID)` reads, from a window `g` of U's halting ID, the number of
    CTSH productions `|C|` (the `∗` before `$`) and the CTSH halting ID `(vf, mf)`
    (`vf`: the lower-case letters after the upper-case ones behind `$`; `mf`: the `∗` between
    the phase marker `b` and `$`).
  * `runSim_U10_8`: the run-level simulation `RunSim` from the CTSH `(CStep C, Halting C)`
    (the zoo's `URTM.CTSH` semantics) at `(w, 0)` to Spec's `(Step U, Halted U)` at
    `toID 0 (encList C w)`, with readback `∃ g, toID γ.pos g = γ ∧ readU g = some (|C|, y)`.
    It uses the zoo's theorem `URTM.CTSH.U10_8.urtm10_8_simulates_ctsh` and the P6 bridge.
  * `hout_U10_8`: the same in the exact shape of the hypothesis `hout` of
    `URTM.Univ.isUTMStrict_of_chain`, for a middle layer ending in `CStep (Cn n)`.

  `encList` and `readU` are ordinary (computable) list functions. No proof holes, no new
  axioms; the finite checks are kernel `decide` (`tests/check.sh`).
-/
import LeanUniv.KToSpec
import LeanUniv.ExactSim
import URTM.CTSH10_8

namespace URTM.Univ.U10_8
open URTM URTM.CTSH URTM.Gen.K10_8 URTM.Univ.KToSpec Relation
open URTM.KState (Tgt Cfg Step StepN Halted HaltsIn)
open URTM.CTSH.U10_8 (lo up RA Hi Lo tapeList tapeOf rep encC finCfg urtm10_8_simulates_ctsh)

/-! ### Numbering and the Spec table -/

/-- State numbers: `q0..q9 ↦ 0..9`, pseudo-states `null (h0) ↦ 10`, `halt (h1) ↦ 11`. -/
def stN : Tgt St Ps → ℕ
  | .go .q0 => 0 | .go .q1 => 1 | .go .q2 => 2 | .go .q3 => 3 | .go .q4 => 4
  | .go .q5 => 5 | .go .q6 => 6 | .go .q7 => 7 | .go .q8 => 8 | .go .q9 => 9
  | .halt .h0 => 10 | .halt .h1 => 11

/-- Symbol numbers: `s_i ↦ i`; the blank `b = s0 ↦ 0`. -/
def syN : Sy → ℕ
  | .s0 => 0 | .s1 => 1 | .s2 => 2 | .s3 => 3 | .s4 => 4 | .s5 => 5 | .s6 => 6 | .s7 => 7

theorem stN_inj : Function.Injective stN := by
  intro a b h
  rcases a with (a | a) <;> cases a <;> rcases b with (b | b) <;> cases b <;>
    first | rfl | exact absurd h (by decide)

theorem syN_inj : Function.Injective syN := by
  intro a b h
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

/-- The numbering of URTM(10,8). -/
def num10_8 : Numbering St Ps Sy := ⟨stN, syN, stN_inj, syN_inj⟩

/-- **URTM(10,8) as a Spec table** (63 quintuples). -/
def U : List Quint := numT num10_8 T

instance (V : List Quint) : Decidable (Spec.Deterministic V) := by
  unfold Spec.Deterministic; infer_instance
instance (V : List Quint) : Decidable (Spec.Reversible V) := by
  unfold Spec.Reversible; infer_instance

theorem U_length : U.length = 63 := by decide +kernel

/-- **Counts** (Morita's convention, `LeanUniv/Strict.lean`): 10 states, 8 symbols. -/
theorem U_counts : Spec.NStates U = 10 ∧ Spec.NSyms U = 8 := by decide +kernel

/-- **Deterministic** in Spec's sense (Morita Def. 5.4). -/
theorem U_det : Spec.Deterministic U := by decide +kernel

/-- **Reversible** in Spec's sense (Morita Def. 5.4). -/
theorem U_rev : Spec.Reversible U := by decide +kernel

/-- Morita's description-file convention: a 0-shift enters only a pseudo-state (a state with
    no outgoing quintuple). -/
theorem U_zeroShift : ∀ r ∈ U, r.d = .Z → r.q ∉ U.map Quint.p := by decide +kernel

/-! ### The list-level encoder -/

/-- ϕ₁ on numbers: `Y ↦ y = 1`, `N ↦ n = 2`. -/
def loN : Ch → ℕ
  | .Y => 1
  | .N => 2

/-- **Encoder** (list level): Spec code of Morita's initial ID of U for the CTSH `C` and the
    initial word `w`. State `begin = 0`; left of the head, nearest first: `$`, the phase
    marker `b`, then for each production `w_i` (i = 1, …, k−1) `∗ ϕ₁(w_i)`, then the left end
    `b`; from the head: `ϕ₁(w)`. -/
def encList (C : CTSH) (w : List Ch) : Spec.Code :=
  (0, 7 :: 0 :: C.flatMap (fun u => 6 :: u.map loN) ++ [0], w.map loN)

/-- The translation between typed positions and Spec positions: the head of `encC C w`. -/
def δ (C : CTSH) : ℤ := ((RA C 0).length + 2 : ℕ)

theorem syN_lo (c : Ch) : syN (lo c) = loN c := by cases c <;> rfl

theorem map_lo (u : List Ch) : (u.map lo).map syN = u.map loN := by
  simp [syN_lo]

theorem syN_comp_lo : syN ∘ lo = loN := funext syN_lo

theorem Hi_zero_rev (C : CTSH) :
    ((Hi C 0).map syN).reverse = C.flatMap (fun u => 6 :: u.map loN) := by
  induction C with
  | nil => rfl
  | cons u C ih =>
    have : Hi (u :: C) 0 = Hi C 0 ++ (u.reverse.map lo ++ [.s6]) := by
      simp [Hi, CTSH.Sim.Hi]
    rw [this, List.map_append, List.reverse_append, ih]
    simp only [List.map_append, List.map_map, syN_comp_lo, List.reverse_append,
      List.map_reverse, List.reverse_reverse, List.flatMap_cons, List.map_cons, List.map_nil]
    rfl

theorem RA_zero (C : CTSH) : RA C 0 = Hi C 0 ++ [.s0] := by
  simp [RA, prod, Lo, CTSH.Sim.Lo]

/-- The encoder is the numbered, shifted typed initial configuration. -/
theorem encList_eq (C : CTSH) (w : List Ch) :
    Spec.toID 0 (encList C w) = numCfg num10_8 (δ C) (encC C w) := by
  have hL : tapeList C 0 [] w = (Sy.s0 :: RA C 0 ++ [Sy.s7]) ++ w.map lo := by simp [tapeList]
  have hp : ((RA C 0).length + 2 + ([] : List Ch).length : ℕ) =
      ((Sy.s0 :: RA C 0 ++ [Sy.s7]).map syN).length := by simp
  have e : encC C w = ⟨.go .q0, (((RA C 0).length + 2 + ([] : List Ch).length : ℕ) : ℤ),
      CTSH.Sim.tp .s0 (tapeList C 0 [] w)⟩ := by
    simp [encC, rep, tapeOf]
  rw [e, numCfg_tp (N := num10_8) .s0 rfl (δ C) _ _ _ (by rw [hL]; simp)]
  have h0 : (((RA C 0).length + 2 + ([] : List Ch).length : ℕ) : ℤ) - δ C = 0 := by simp [δ]
  rw [h0]
  congr 1
  simp only [window]
  have hp' : ((RA C 0).length + 2 + ([] : List Ch).length : ℕ) =
      ((Sy.s0 :: RA C 0 ++ [Sy.s7]).map num10_8.sym).length := hp
  rw [hL, List.map_append, List.take_left' hp'.symm, List.drop_left' hp'.symm]
  simp only [encList, RA_zero, num10_8, stN, List.map_append, List.map_cons, List.map_nil,
    List.reverse_append, List.reverse_cons, List.reverse_nil, List.map_map, syN_comp_lo,
    Hi_zero_rev]
  simp [syN]

/-- The encoded initial ID is an ID of U (`c(n, α) ∈ ID(U)` of Morita Def. 7.1). -/
theorem isIDOf_encList (C : CTSH) (w : List Ch) : Spec.IsIDOf U (Spec.toID 0 (encList C w)) := by
  have hs : ∀ a ∈ [0, 1, 2, 6, 7], a = 0 ∨ a ∈ Spec.symbols U := by decide +kernel
  have hlo : ∀ c : Ch, loN c ∈ [0, 1, 2, 6, 7] := by intro c; cases c <;> decide
  have h0 : (0 : ℕ) ∈ Spec.states U := by decide +kernel
  refine isIDOf_toID U 0 _ h0 fun a ha => hs a ?_
  simp only [encList, List.mem_append, List.mem_cons, List.mem_flatMap, List.mem_map,
    List.not_mem_nil] at ha
  rcases ha with ((rfl | rfl | ⟨u, -, rfl | ⟨c, -, rfl⟩⟩) | rfl | h) | ⟨c, -, rfl⟩
  all_goals first | decide | exact hlo c | exact absurd h id

/-! ### The list-level readout -/

/-- Letters of the final CTSH string: `1 = y ↦ Y`, otherwise `N`. -/
def chOf : ℕ → Ch
  | 1 => .Y
  | _ => .N

/-- **Readout** (list level) from a window `g` of U's halting ID. With `L` the whole window
    (left end first), `pre` the part before the first `$ = 7`:
    * `|C|` = the number of `∗ = 6` in `pre`;
    * `mf` = the number of `∗` in `pre` after its last blank (the phase marker);
    * `vf` = behind `$`, skip the upper-case letters `Y = 4`, `N = 5`, and read the lower-case
      letters `y = 1`, `n = 2`.
    `none` if there is no `$`. -/
def readU (g : Spec.Code) : Option (ℕ × CTSH.ID) :=
  let L := g.2.1.reverse ++ g.2.2
  let pre := L.takeWhile (· != 7)
  match L.dropWhile (· != 7) with
  | [] => none
  | _ :: post =>
    some (pre.count 6,
      (((post.dropWhile (fun a => a == 4 || a == 5)).takeWhile (fun a => a == 1 || a == 2)).map chOf,
       (pre.reverse.takeWhile (· != 0)).count 6))

theorem takeWhile_append_of_all {p : ℕ → Bool} {A : List ℕ} (hA : ∀ a ∈ A, p a = true)
    (b : ℕ) (hb : p b = false) (B : List ℕ) :
    (A ++ b :: B).takeWhile p = A ∧ (A ++ b :: B).dropWhile p = b :: B := by
  induction A with
  | nil => simp [hb]
  | cons a A ih =>
    have ha := hA a (by simp)
    obtain ⟨h1, h2⟩ := ih fun x hx => hA x (by simp [hx])
    simp [ha, h1, h2]

theorem dropWhile_append_of_all {p : ℕ → Bool} {A B : List ℕ} (hA : ∀ a ∈ A, p a = true)
    (hB : ∀ b ∈ B.head?, p b = false) : (A ++ B).dropWhile p = B := by
  induction A with
  | nil =>
    cases B with
    | nil => rfl
    | cons b B => simp [hB b rfl]
  | cons a A ih =>
    simp [hA a (by simp), ih fun x hx => hA x (by simp [hx])]

theorem takeWhile_of_all {p : ℕ → Bool} {A : List ℕ} (hA : ∀ a ∈ A, p a = true) :
    A.takeWhile p = A := by
  induction A with
  | nil => rfl
  | cons a A ih =>
    simp [hA a (by simp), ih fun x hx => hA x (by simp [hx])]

/-! #### Symbol classes and counts in the rule region -/

theorem mem_lo_map {x : Sy} {u : List Ch} (h : x ∈ u.map lo) : x = .s1 ∨ x = .s2 := by
  obtain ⟨c, -, rfl⟩ := List.mem_map.mp h
  cases c <;> simp [lo]

theorem mem_up_map {x : Sy} {u : List Ch} (h : x ∈ u.map up) : x = .s4 ∨ x = .s5 := by
  obtain ⟨c, -, rfl⟩ := List.mem_map.mp h
  cases c <;> simp [up]

theorem mem_Hi {C : CTSH} {m : ℕ} {x : Sy} (h : x ∈ Hi C m) : x = .s1 ∨ x = .s2 ∨ x = .s6 := by
  simp only [Hi, CTSH.Sim.Hi, List.mem_flatten, List.mem_map, List.mem_reverse] at h
  obtain ⟨_, ⟨u, -, rfl⟩, hx⟩ := h
  rcases List.mem_append.mp hx with hx | hx
  · rw [List.map_reverse, List.mem_reverse] at hx
    rcases mem_lo_map hx with h | h <;> simp [h]
  · simp at hx; simp [hx]

theorem mem_LoCore {C : CTSH} {m : ℕ} {x : Sy} (h : x ∈ CTSH.Sim.LoCore up .s6 C m) :
    x = .s4 ∨ x = .s5 ∨ x = .s6 := by
  simp only [CTSH.Sim.LoCore, List.mem_flatten, List.mem_map, List.mem_reverse] at h
  obtain ⟨_, ⟨u, -, rfl⟩, hx⟩ := h
  rcases List.mem_append.mp hx with hx | hx
  · rw [List.map_reverse, List.mem_reverse] at hx
    rcases mem_up_map hx with h | h <;> simp [h]
  · simp at hx; simp [hx]

theorem mem_Lo {C : CTSH} {m : ℕ} {x : Sy} (h : x ∈ Lo C m) : x = .s4 ∨ x = .s5 ∨ x = .s6 := by
  simp only [Lo, CTSH.Sim.Lo] at h
  split at h
  · simp at h
  · rcases List.mem_append.mp h with h | h
    · exact mem_LoCore h
    · simp at h; simp [h]

theorem count_Hi (C : CTSH) (m : ℕ) : (Hi C m).count .s6 = C.length - m := by
  simp only [Hi, CTSH.Sim.Hi, List.count_flatten, List.map_map]
  have : ∀ u : List Ch, (List.count Sy.s6 ∘ fun w => w.reverse.map lo ++ [Sy.s6]) u = 1 := by
    intro u
    simp only [Function.comp_apply, List.count_append, List.count_singleton_self]
    rw [List.count_eq_zero.mpr fun h => by rcases mem_lo_map (u := u.reverse) h with h | h <;> cases h]
  rw [List.map_congr_left (fun u _ => this u)]
  simp

theorem count_LoCore (C : CTSH) (m : ℕ) :
    (CTSH.Sim.LoCore up .s6 C m).count .s6 = min (m - 1) C.length := by
  simp only [CTSH.Sim.LoCore, List.count_flatten, List.map_map]
  have : ∀ u : List Ch, (List.count Sy.s6 ∘ fun w => w.reverse.map up ++ [Sy.s6]) u = 1 := by
    intro u
    simp only [Function.comp_apply, List.count_append, List.count_singleton_self]
    rw [List.count_eq_zero.mpr fun h => by rcases mem_up_map (u := u.reverse) h with h | h <;> cases h]
  rw [List.map_congr_left (fun u _ => this u)]
  simp

theorem count_Lo (C : CTSH) {m : ℕ} (hm : m ≤ C.length) : (Lo C m).count .s6 = m := by
  simp only [Lo, CTSH.Sim.Lo]
  split
  · simp [*]
  · rw [List.count_append, count_LoCore]; simp; omega

theorem count_lo (u : List Ch) : (u.map lo).count .s6 = 0 :=
  List.count_eq_zero.mpr fun h => by rcases mem_lo_map h with h | h <;> cases h

/-! #### Reading the final tape -/

/-- `readU` on the whole window list. -/
theorem readU_eq (g : Spec.Code) : readU g =
    match (g.2.1.reverse ++ g.2.2).dropWhile (· != 7) with
    | [] => none
    | _ :: post =>
      some (((g.2.1.reverse ++ g.2.2).takeWhile (· != 7)).count 6,
        (((post.dropWhile (fun a => a == 4 || a == 5)).takeWhile (fun a => a == 1 || a == 2)).map chOf,
         (((g.2.1.reverse ++ g.2.2).takeWhile (· != 7)).reverse.takeWhile (· != 0)).count 6)) := rfl

theorem chOf_loN (u : List Ch) : (u.map loN).map chOf = u := by
  induction u with
  | nil => rfl
  | cons c u ih => cases c <;> simp [loN, chOf, ih]

theorem count_map_syN (l : List Sy) (a : Sy) : (l.map syN).count (syN a) = l.count a :=
  List.count_map_of_injective l syN syN_inj a

/-- **The readout is right on the final tape** `b · RA(mf) · $ · ϕ_up(rm) · ϕ₁(vf)`, whatever the
    head position, for every phase `mf ≤ |C|`. -/
theorem readU_window (C : CTSH) (mf : ℕ) (hmf : mf ≤ C.length) (rm vf : List Ch) (s p : ℕ) :
    readU (window s ((tapeList C mf rm vf).map syN) p) = some (C.length, (vf, mf)) := by
  have hL : (window s ((tapeList C mf rm vf).map syN) p).2.1.reverse ++
      (window s ((tapeList C mf rm vf).map syN) p).2.2 =
      (0 :: (RA C mf).map syN) ++ 7 :: ((rm.map up).map syN ++ vf.map loN) := by
    simp [window, tapeList, List.map_map, syN_comp_lo, syN]
  have hRA7 : ∀ a ∈ 0 :: (RA C mf).map syN, (a != 7) = true := by
    intro a ha
    simp only [List.mem_cons, List.mem_map] at ha
    rcases ha with rfl | ⟨x, hx, rfl⟩
    · rfl
    · simp only [RA, List.mem_append, List.mem_cons] at hx
      rcases hx with (hx | hx) | hx | hx
      · rcases mem_Hi hx with rfl | rfl | rfl <;> rfl
      · rw [List.map_reverse, List.mem_reverse] at hx
        rcases mem_lo_map hx with rfl | rfl <;> rfl
      · subst hx; rfl
      · rcases mem_Lo hx with rfl | rfl | rfl <;> rfl
  obtain ⟨ht, hd⟩ := takeWhile_append_of_all hRA7 7 rfl ((rm.map up).map syN ++ vf.map loN)
  rw [readU_eq, hL, hd, ht]
  simp only
  have hup : ∀ a ∈ (rm.map up).map syN, (a == 4 || a == 5) = true := by
    intro a ha
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
    rcases mem_up_map hx with rfl | rfl <;> rfl
  have hvf : ∀ b ∈ (vf.map loN).head?, (b == 4 || b == 5) = false := by
    intro b hb
    cases vf with
    | nil => simp at hb
    | cons c v =>
      simp only [List.map_cons, List.head?_cons, Option.mem_def, Option.some.injEq] at hb
      subst hb; cases c <;> rfl
  have hlo : ∀ a ∈ vf.map loN, (a == 1 || a == 2) = true := by
    intro a ha
    obtain ⟨c, -, rfl⟩ := List.mem_map.mp ha
    cases c <;> rfl
  rw [dropWhile_append_of_all hup hvf, takeWhile_of_all hlo, chOf_loN]
  -- the counts
  have hcnt : (0 :: (RA C mf).map syN).count 6 = C.length := by
    rw [show (0 :: (RA C mf).map syN).count 6 = ((RA C mf).map syN).count 6 by
        simp, show (6 : ℕ) = syN .s6 from rfl, count_map_syN]
    simp only [RA, List.count_append, List.count_cons, count_Hi, count_lo, count_Lo C hmf]
    simp; omega
  have hmfc : ((0 :: (RA C mf).map syN).reverse.takeWhile (· != 0)).count 6 = mf := by
    have hLo0 : ∀ a ∈ ((Lo C mf).map syN).reverse, (a != 0) = true := by
      intro a ha
      rw [List.mem_reverse] at ha
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
      rcases mem_Lo hx with rfl | rfl | rfl <;> rfl
    have e : (0 :: (RA C mf).map syN).reverse = ((Lo C mf).map syN).reverse ++
        0 :: (0 :: (Hi C mf ++ (prod C mf).reverse.map lo).map syN).reverse := by
      simp [RA, show syN .s0 = 0 from rfl]
    rw [e, (takeWhile_append_of_all hLo0 0 rfl _).1, List.count_reverse,
      show (6 : ℕ) = syN .s6 from rfl, count_map_syN, count_Lo C hmf]
  rw [hcnt, hmfc]

/-! ### The run-level simulation -/

theorem cstepN_of_rtg {C : CTSH} {s f : CTSH.ID} (h : ReflTransGen (CStep C) s f) :
    ∃ n, CStepN C n s f := by
  induction h using ReflTransGen.head_induction_on with
  | refl => exact ⟨0, .refl _⟩
  | head h _ ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, .cons h hn⟩

theorem rtg_of_cstepN {C : CTSH} {n : ℕ} {s f : CTSH.ID} (h : CStepN C n s f) :
    ReflTransGen (CStep C) s f := by
  induction h with
  | refl => exact .refl
  | cons h _ ih => exact .head h ih

/-- The final configurations of U as Spec IDs with an explicit window. -/
theorem finCfg_window (C : CTSH) (vf : List Ch) (mf : ℕ) (rm : List Ch) (hv : vf = [] ∨ mf = 0) :
    ∃ p : ℕ, numCfg num10_8 (δ C) (finCfg C vf mf rm) =
      Spec.toID ((p : ℤ) - δ C) (window (stN (finCfg C vf mf rm).st) ((tapeList C mf rm vf).map syN) p) := by
  cases vf with
  | nil =>
    refine ⟨(RA C mf).length + 2 + rm.length, ?_⟩
    have := numCfg_tp (N := num10_8) .s0 rfl (δ C) (.halt .h0) (tapeList C mf rm [])
      ((RA C mf).length + 2 + rm.length) (by simp [tapeList]; omega)
    simpa [finCfg, tapeOf, num10_8] using this
  | cons c v =>
    have hm : mf = 0 := by simpa using hv
    subst hm
    refine ⟨(RA C 0).length, ?_⟩
    have := numCfg_tp (N := num10_8) .s0 rfl (δ C) (.halt .h1) (tapeList C 0 rm (c :: v))
      (RA C 0).length (by simp [tapeList]; omega)
    simpa [finCfg, tapeOf, num10_8] using this

/-- **URTM(10,8) simulates every CTSH at the level of Spec** (run level, exact readback):
    from `toID 0 (encList C w)`, U halts iff the CTSH `C` halts from `(w, 0)`, and when it
    halts at `y`, some window `g` of U's halting ID satisfies `readU g = some (|C|, y)`. -/
theorem runSim_U10_8 (C : CTSH) (w : List Ch) :
    RunSim (CStep C) (Halting C) (Spec.Step U) (Spec.Halted U)
      (fun y γ => ∃ g, Spec.toID γ.pos g = γ ∧ readU g = some (C.length, y))
      (w, 0) (Spec.toID 0 (encList C w)) := by
  have hmain := urtm10_8_simulates_ctsh C w
  rw [encList_eq]
  refine ⟨fun y hy => ?_, fun hn hU => ?_⟩
  · obtain ⟨n, hn⟩ := cstepN_of_rtg hy.1
    obtain ⟨vf, mf⟩ := y
    obtain ⟨N, rm, -, hN⟩ := hmain.1 n vf mf ⟨hn, hy.2⟩
    have hv : vf = [] ∨ mf = 0 := by
      rcases hy.2.2 with ⟨v, h1, h2⟩ | h
      · exact .inr h2
      · exact .inl h
    have hmf : mf ≤ C.length := by have := hy.2.1; simp [CTSH.k] at this; omega
    obtain ⟨p, hp⟩ := finCfg_window C vf mf rm hv
    refine ⟨_, (haltsAt_numCfg_iff (N := num10_8) T (δ C) _ _).mpr ⟨N, _, hN, rfl⟩,
      window (stN (finCfg C vf mf rm).st) ((tapeList C mf rm vf).map syN) p, ?_, ?_⟩
    · rw [hp]; rfl
    · exact readU_window C mf hmf rm vf _ p
  · obtain ⟨γ, hγ⟩ := hU
    obtain ⟨N, c', h, -⟩ := (haltsAt_numCfg_iff (N := num10_8) T (δ C) _ γ).mp hγ
    exact hmain.2.2.mp (fun n (f : CTSH.ID) hc => hn ⟨f, rtg_of_cstepN hc.1, hc.2⟩) N c' h

/-- **The exit layer `hout` of `isUTMStrict_of_chain` for U = URTM(10,8)**, when the middle
    layer ends in the CTSH `Cn n` (zoo semantics `CStep`/`Halting`) started at `(wn n a, 0)`,
    `c (n, a) = encList (Cn n) (wn n a)`, and the decoder `d` factors through `readU` on the
    halting CTSH IDs. -/
theorem hout_U10_8 (Cn : ℕ → CTSH) (wn : ℕ → Spec.Code → List Ch)
    (c : ℕ × Spec.Code → Spec.Code) (d : Spec.Code → Option Spec.Code)
    (decM : CTSH.ID → Option Spec.Code)
    (hc : ∀ n a, c (n, a) = encList (Cn n) (wn n a))
    (hd : ∀ n g y, Halting (Cn n) y → readU g = some ((Cn n).length, y) → d g = decM y) :
    ∀ n a, RunSim (CStep (Cn n)) (Halting (Cn n)) (Spec.Step U) (Spec.Halted U)
      (fun y γ => ∃ g, Spec.toID γ.pos g = γ ∧ d g = decM y) (wn n a, 0)
      (Spec.toID 0 (c (n, a))) := by
  intro n a
  have h := runSim_U10_8 (Cn n) (wn n a)
  rw [← hc] at h
  refine ⟨fun y hy => ?_, h.2⟩
  obtain ⟨γ, hγ, g, hg, hr⟩ := h.1 y hy
  exact ⟨γ, hγ, g, hg, hd n g y hy.2 hr⟩

/-- `c(n, α) ∈ ID(U)` (the hypothesis `hID` of `isUTMStrict_of_chain`) for such a `c`. -/
theorem hID_U10_8 (Cn : ℕ → CTSH) (wn : ℕ → Spec.Code → List Ch)
    (c : ℕ × Spec.Code → Spec.Code) (hc : ∀ n a, c (n, a) = encList (Cn n) (wn n a)) :
    ∀ n a, Spec.IsIDOf U (Spec.toID 0 (c (n, a))) := by
  intro n a
  rw [hc]
  exact isIDOf_encList _ _

end URTM.Univ.U10_8
