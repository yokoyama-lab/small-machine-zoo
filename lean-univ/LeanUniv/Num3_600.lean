/-
  **URTM(3,600) as a Spec table** (docs/24 P7d): numbering, counts, determinism, reversibility.

  `U = numT num T3py`: the 3-state machine `URTM.Gen.T3_600.T3py` (1572 quintuples; the improved
  3-state conversion of docs/09, mirrored, applied to Morita's (32,3) without its halting
  quintuples). States `L, R0, R1 ↦ 0, 1, 2`. Symbols are `CSym (VSym St Sy)`:
  `pl x ↦ vN x`, `ct x k ↦ 196·(k+1) + vN x`, where `vN` numbers the symbols of the intermediate
  one-way-updating machine (`bl ↦ 0`, `pl s ↦ 1 + s`, `mk p s ↦ 4 + 3p + s`,
  `mkp p v ↦ 100 + 3p + v`). The blank is `pl bl ↦ 0`.

  * `U_counts`: 3 states, 600 symbols (`decide +kernel`).
  * `U_det`, `U_rev`: from the zoo's general theorem (`urtm3_600_simulates_ctsh`) through the
    injective numbering (`numT_det`, `numT_rev`).
  * `U_noPseudo`: no halting quintuple and no pseudo-state.
-/
import LeanUniv.U32_3
import URTM.CTSH3_600Main

namespace URTM.Univ.U3_600
open URTM URTM.CTSH URTM.Gen.K32_3 URTM.Gen.T3_600 URTM.Univ.KToSpec
open URTM.KState (Tgt Cfg Machine)
open URTM.Conv1W (VSt VSym)
open URTM.Conv3P (CSym)
open URTM.Conv510 (TSt)

/-! ### Numbering and the Spec table -/

/-- Symbol numbers of (32,3): `b y n ↦ 0 1 2`. -/
abbrev sN (s : Sy) : ℕ := U32_3.num.sym s

/-- State numbers of (32,3). -/
abbrev qN (q : St) : ℕ := U32_3.num.st (.go q)

theorem sN_lt (s : Sy) : sN s < 3 := by cases s <;> decide
theorem qN_lt (q : St) : qN q < 32 := by cases q <;> decide
theorem sN_inj {a b : Sy} (h : sN a = sN b) : a = b := U32_3.num.sym_inj h
theorem qN_inj {a b : St} (h : qN a = qN b) : a = b := Tgt.go.inj (U32_3.num.st_inj h)

/-- The symbols of the one-way-updating machine `W`: `bl ↦ 0`, `pl s ↦ 1 + s`,
    `mk p s ↦ 4 + 3p + s`, `mkp p v ↦ 100 + 3p + v` (all `< 196`). -/
def vN : VSym St Sy → ℕ
  | .bl => 0
  | .pl s => 1 + sN s
  | .mk p s => 4 + 3 * qN p + sN s
  | .mkp p v => 100 + 3 * qN p + sN v

theorem vN_lt (x : VSym St Sy) : vN x < 196 := by
  cases x with
  | bl => simp [vN]
  | pl s => have := sN_lt s; simp only [vN]; omega
  | mk p s => have := sN_lt s; have := qN_lt p; simp only [vN]; omega
  | mkp p v => have := sN_lt v; have := qN_lt p; simp only [vN]; omega

theorem vN_inj : Function.Injective vN := by
  intro a b h
  cases a with
  | bl =>
    cases b with
    | bl => rfl
    | pl s => simp only [vN] at h; omega
    | mk p s => simp only [vN] at h; omega
    | mkp p v => simp only [vN] at h; omega
  | pl s =>
    cases b with
    | bl => simp only [vN] at h; omega
    | pl s' => simp only [vN] at h; rw [sN_inj (a := s) (b := s') (by omega)]
    | mk p s' => have := sN_lt s; simp only [vN] at h; omega
    | mkp p v => have := sN_lt s; simp only [vN] at h; omega
  | mk p s =>
    cases b with
    | bl => simp only [vN] at h; omega
    | pl s' => have := sN_lt s'; simp only [vN] at h; omega
    | mk p' s' =>
      have := sN_lt s; have := sN_lt s'
      simp only [vN] at h
      rw [qN_inj (a := p) (b := p') (by omega), sN_inj (a := s) (b := s') (by omega)]
    | mkp p' v =>
      have := sN_lt s; have := qN_lt p
      simp only [vN] at h; omega
  | mkp p v =>
    cases b with
    | bl => simp only [vN] at h; omega
    | pl s' => have := sN_lt s'; simp only [vN] at h; omega
    | mk p' s' =>
      have := sN_lt s'; have := qN_lt p'
      simp only [vN] at h; omega
    | mkp p' v' =>
      have := sN_lt v; have := sN_lt v'
      simp only [vN] at h
      rw [qN_inj (a := p) (b := p') (by omega), sN_inj (a := v) (b := v') (by omega)]

/-- The symbols of (3,600): `pl x ↦ vN x`, `ct x k ↦ 196·(k+1) + vN x`. The blank is `pl bl ↦ 0`. -/
def cN : CSym (VSym St Sy) → ℕ
  | .pl x => vN x
  | .ct x k => 196 * (k + 1) + vN x

theorem cN_inj : Function.Injective cN := by
  intro a b h
  cases a with
  | pl x =>
    cases b with
    | pl y => simp only [cN] at h; rw [vN_inj h]
    | ct y k => have := vN_lt x; simp only [cN, Nat.mul_succ] at h; omega
  | ct x k =>
    cases b with
    | pl y => have := vN_lt y; simp only [cN, Nat.mul_succ] at h; omega
    | ct y j =>
      have hx := vN_lt x; have hy := vN_lt y
      simp only [cN] at h
      have h1 := congrArg (· / 196) h
      simp only [Nat.mul_add_div (by decide : 0 < 196), Nat.div_eq_of_lt hx,
        Nat.div_eq_of_lt hy] at h1
      have hkj : k = j := by omega
      subst hkj
      rw [vN_inj (by omega : vN x = vN y)]

/-- The three states `L, R0, R1 ↦ 0, 1, 2`; the pseudo-states (which do not occur in the table)
    `h0, h1 ↦ 3, 4`. -/
def stN : Tgt TSt Ps → ℕ
  | .go .L => 0
  | .go .R0 => 1
  | .go .R1 => 2
  | .halt .h0 => 3
  | .halt .h1 => 4

theorem stN_inj : Function.Injective stN := by
  intro a b h
  rcases a with (_ | _ | _) | (_ | _) <;> rcases b with (_ | _ | _) | (_ | _) <;>
    first | rfl | exact absurd h (by decide)

/-- The numbering of URTM(3,600). -/
def num : Numbering TSt Ps (CSym (VSym St Sy)) := ⟨stN, cN, stN_inj, cN_inj⟩

/-- **URTM(3,600) as a Spec table** (1572 quintuples). -/
def U : List Quint := numT num T3py

set_option maxRecDepth 100000 in
/-- **Counts** (Morita's convention): 3 states, 600 symbols. -/
theorem U_counts : Spec.NStates U = 3 ∧ Spec.NSyms U = 600 := by decide +kernel


/-! ### Determinism and reversibility through an injective numbering -/

/-- A deterministic typed machine is deterministic in Spec's sense after numbering. -/
theorem numT_det {Q P S : Type} (N : Numbering Q P S) (T : Machine Q P S)
    (h : KState.Deterministic T) : Spec.Deterministic (numT N T) := by
  intro r₁ h₁ r₂ h₂ hp hs
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp h₁
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp h₂
  simp only [numRule] at hp hs
  have hp' : a.p = b.p := Tgt.go.inj (N.st_inj hp)
  have hs' : a.s = b.s := N.sym_inj hs
  by_cases hab : a = b
  · rw [hab]
  · exact absurd hs' (h a ha b hb hab hp')

/-- A reversible typed machine is reversible in Spec's sense after numbering. -/
theorem numT_rev {Q P S : Type} (N : Numbering Q P S) (T : Machine Q P S)
    (h : KState.Reversible T) : Spec.Reversible (numT N T) := by
  intro r₁ h₁ r₂ h₂ hne hq
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp h₁
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp h₂
  have hab : a ≠ b := fun e => hne (by rw [e])
  simp only [numRule] at hq ⊢
  obtain ⟨hd, ht⟩ := h a ha b hb hab (N.st_inj hq)
  exact ⟨hd, fun e => ht (N.sym_inj e)⟩

theorem U_det : Spec.Deterministic U :=
  numT_det num T3py (URTM.CTSH.U3_600.urtm3_600_simulates_ctsh [] []).1

theorem U_rev : Spec.Reversible U :=
  numT_rev num T3py (URTM.CTSH.U3_600.urtm3_600_simulates_ctsh [] []).2.1

set_option maxRecDepth 100000 in
/-- `U` has no halting quintuple and no pseudo-state: every target state has outgoing
    quintuples, and no quintuple is a 0-shift. It halts where no quintuple applies. -/
theorem U_noPseudo : ∀ r ∈ U, r.q ∈ U.map Quint.p ∧ r.d ≠ .Z := by decide +kernel

end URTM.Univ.U3_600
