/-
  **The 18476-symbol three-state machine as a Spec table**: numbering, counts, determinism,
  reversibility.

  The machine is the intermediate machine of Morita's three-state conversion of (32,3)
  (`lean/URTM/CTSH3_18476Main.lean`): ↑ and ↓ merged and every counter `1..61` kept,

      K = Conv3P.conv That .L .bl idx3 (fun _ => 61) allW,

  where `That` is Morita's one-way-updating machine (Lemma 5.9) of (32,3) without its halting
  quintuples, whose cells hold two cells of (32,3). `K` has on the order of 10⁵ quintuples, so
  its numbered table is never written as a literal and nothing below evaluates it: the counts,
  determinism and reversibility are transported through the injective numbering
  (`NumCount`, `U3_600.numT_det`, `U3_600.numT_rev`) from the zoo's theorems on `K`.

  Numbering (`num`): states `L, R0, R1 ↦ 0, 1, 2` (`U3_600.stN`); the cells of `That`
  `bl ↦ 0`, `pr s t ↦ 1 + 3s + t`, `hp p s t ↦ 10 + 9p + 3s + t` (`U3_36654.cW`, the numbering of
  the description file urtm3-36654, all `< 298`); the symbols of `K`: `pl x ↦ cW x`,
  `ct x k ↦ 298·(k+1) + cW x`. The blank `pl bl ↦ 0`.

  * `U_is_conv`: `U` is the numbering of `K` (by definition).
  * `U_counts`: 3 states (`L`, `R0`, `R1` each have quintuples), 18476 symbols
    (`Values32_3.shared_32_3`: `nsym K = 298 · 62`).
  * `U_det`, `U_rev`: from `CTSH.U3_18476.hD18476`, `hR18476`.
  No `sorry`, no new axiom, no `native_decide`.
-/
import LeanUniv.NumCount
import LeanUniv.Num3_600
import LeanUniv.Values32_3
import URTM.CTSH3_18476Main

namespace URTM.Univ.U3_18476
open URTM URTM.CTSH URTM.Gen.K32_3 URTM.Univ.KToSpec URTM.Univ.NumCount
open URTM.KState (Tgt Cfg Machine Rule)
open URTM.Conv59 (WSt WSym)
open URTM.Conv3P (CSym)
open URTM.Conv510 (TSt)
open URTM.CTSH.U3_36654 (That allW allW_all idx3 cS cQ cW)
open URTM.Univ.U3_600 (stN stN_inj numT_det numT_rev sN qN)

/-- **The symbolic machine** (the intermediate machine of Morita's three-state conversion of (32,3),
    every counter kept). -/
abbrev K : Machine TSt Ps (CSym (WSym St Sy)) := Conv3P.conv That .L .bl idx3 (fun _ => 61) allW

/-! ### Numbering -/

theorem cS_sN (s : Sy) : cS s = sN s := rfl
theorem cQ_qN (q : St) : cQ q = qN q := rfl

theorem cS_lt (s : Sy) : cS s < 3 := by cases s <;> decide
theorem cQ_lt (q : St) : cQ q < 32 := by cases q <;> decide
theorem cS_inj {a b : Sy} (h : cS a = cS b) : a = b := (List.idxOf_inj (hS a)).mp h
theorem cQ_inj {a b : St} (h : cQ a = cQ b) : a = b := (List.idxOf_inj (hQ a)).mp h

theorem cW_lt (x : WSym St Sy) : cW x < 298 := by
  cases x with
  | bl => simp [cW]
  | pr s t => have := cS_lt s; have := cS_lt t; simp only [cW]; omega
  | hp p s t => have := cS_lt s; have := cS_lt t; have := cQ_lt p; simp only [cW]; omega

theorem cW_inj : Function.Injective cW := by
  intro a b h
  cases a with
  | bl =>
    cases b with
    | bl => rfl
    | pr s t => simp only [cW] at h; omega
    | hp p s t => simp only [cW] at h; omega
  | pr s t =>
    have := cS_lt s; have := cS_lt t
    cases b with
    | bl => simp only [cW] at h; omega
    | pr s' t' =>
      have := cS_lt s'; have := cS_lt t'
      simp only [cW] at h
      rw [cS_inj (a := s) (b := s') (by omega), cS_inj (a := t) (b := t') (by omega)]
    | hp p' s' t' => simp only [cW] at h; omega
  | hp p s t =>
    have := cS_lt s; have := cS_lt t
    cases b with
    | bl => simp only [cW] at h; omega
    | pr s' t' => have := cS_lt s'; have := cS_lt t'; simp only [cW] at h; omega
    | hp p' s' t' =>
      have := cS_lt s'; have := cS_lt t'
      simp only [cW] at h
      have := cQ_lt p; have := cQ_lt p'
      rw [cQ_inj (a := p) (b := p') (by omega), cS_inj (a := s) (b := s') (by omega),
        cS_inj (a := t) (b := t') (by omega)]

/-- The symbols of `K`: `pl x ↦ cW x`, `ct x k ↦ 298·(k+1) + cW x`. The blank is `pl bl ↦ 0`. -/
def cN : CSym (WSym St Sy) → ℕ
  | .pl x => cW x
  | .ct x k => 298 * (k + 1) + cW x

theorem cN_inj : Function.Injective cN := by
  intro a b h
  cases a with
  | pl x =>
    cases b with
    | pl y => simp only [cN] at h; rw [cW_inj h]
    | ct y k => have := cW_lt x; simp only [cN, Nat.mul_succ] at h; omega
  | ct x k =>
    cases b with
    | pl y => have := cW_lt y; simp only [cN, Nat.mul_succ] at h; omega
    | ct y j =>
      have hx := cW_lt x; have hy := cW_lt y
      simp only [cN] at h
      have h1 := congrArg (· / 298) h
      simp only [Nat.mul_add_div (by decide : 0 < 298), Nat.div_eq_of_lt hx,
        Nat.div_eq_of_lt hy] at h1
      have hkj : k = j := by omega
      subst hkj
      rw [cW_inj (by omega : cW x = cW y)]

/-- The numbering of the 18476-symbol machine. -/
def num : Numbering TSt Ps (CSym (WSym St Sy)) := ⟨stN, cN, stN_inj, cN_inj⟩

/-- **The 18476-symbol three-state machine as a Spec table** (the numbering of `K`; never evaluated). -/
def U : List Quint := numT num K

/-- **The witness is the numbering of the symbolic machine** `Conv3P.conv That .L .bl idx3 (fun _ => 61) allW`
    of `CTSH3_18476Main` (Morita's three-state conversion of the 1WU machine of (32,3), every counter kept). -/
theorem U_is_conv : U = numT num (Conv3P.conv That .L .bl idx3 (fun _ => 61) allW) := rfl

/-! ### Some quintuples of `K` -/

/-- `[L, pl x, pl x, −, L]` for `x ≠ bl` (δ8). -/
theorem mem_d8 {x : WSym St Sy} (hx : x ≠ .bl) :
    (⟨.L, .pl x, .pl x, .L, .go .L⟩ : Rule TSt Ps (CSym (WSym St Sy))) ∈ K :=
  Conv3P.mem_d8 (allW_all x) hx

/-- `[R0, pl u, ct u 1, −, L]` (δ3). -/
theorem mem_d3 (u : WSym St Sy) :
    (⟨.R0, .pl u, .ct u 1, .L, .go .L⟩ : Rule TSt Ps (CSym (WSym St Sy))) ∈ K :=
  Conv3P.mem_d3 (allW_all u) (by decide)

/-- `[R1, ct x 1, ct x 2, −, L]` (δ5). -/
theorem mem_d5 (x : WSym St Sy) :
    (⟨.R1, .ct x (0 + 1), .ct x (0 + 2), .L, .go .L⟩ : Rule TSt Ps (CSym (WSym St Sy))) ∈ K :=
  Conv3P.mem_d5 (allW_all x) (by decide)

/-! ### Counts -/

theorem K_nst : SymCount.nst K = 3 := by
  refine (SymCount.nst_eq_of (L := [TSt.L, .R0, .R1]) (by decide) fun x => ?_).trans rfl
  constructor
  · rintro -
    cases x <;> simp
  · intro _
    cases x with
    | L => exact ⟨_, mem_d8 (x := .pr .s0 .s0) (by decide), rfl⟩
    | R0 => exact ⟨_, mem_d3 .bl, rfl⟩
    | R1 => exact ⟨_, mem_d5 .bl, rfl⟩

theorem bl_syms : (CSym.pl (WSym.bl : WSym St Sy)) ∈ SymCount.syms K :=
  SymCount.s_mem_syms (mem_d3 .bl)

/-- **Counts** (Morita's convention): 3 states, 18476 symbols. -/
theorem U_counts : Spec.NStates U = 3 ∧ Spec.NSyms U = 18476 := by
  refine ⟨(nstates_numT num K).trans K_nst, ?_⟩
  rw [U, nsyms_numT num K (.pl .bl) rfl bl_syms, Values32_3.shared_32_3]

/-! ### Determinism and reversibility -/

theorem U_det : Spec.Deterministic U := numT_det num K URTM.CTSH.U3_18476.hD18476

theorem U_rev : Spec.Reversible U := numT_rev num K URTM.CTSH.U3_18476.hR18476

end URTM.Univ.U3_18476
