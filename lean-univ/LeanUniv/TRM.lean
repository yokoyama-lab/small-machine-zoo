/-
  **Two-register machines** (TRM; docs/24 §2 L1, the source of layer L2, piece P4).

  Two registers X, Y ∈ ℕ and a program `prog : ℕ → Option Op` (label ↦ instruction;
  `none` = halt). The instructions, literally as in docs/24 §2 L1:

      dbl1 b j    : X := 2X + b,                      goto j
      dbl2 b j    : Y := 2Y + b,                      goto j
      half1 j₀ j₁ : (X, r) := (X / 2, X % 2),         goto j_r
      half2 j₀ j₁ : (Y, r) := (Y / 2, Y % 2),         goto j_r

  A configuration is `(i, X, Y) : ℕ × ℕ × ℕ` (label, X, Y). It halts iff `prog i = none`.

  Integration: P4 (this file) and P5 (`TRMDef.lean`) had written the same machine from the
  same design text, character for character up to names; P5's copy was removed and its three
  lemmas (`det`, `stuck`, `step_of_prog`) moved here. `run` is P4's (returns a halted flag).
-/
import LeanUniv.ExactSim

namespace URTM.Univ.TRM

/-- TRM instructions (docs/24 §2 L1). -/
inductive Op
  | dbl1 (b : Bool) (j : ℕ)
  | dbl2 (b : Bool) (j : ℕ)
  | half1 (j₀ j₁ : ℕ)
  | half2 (j₀ j₁ : ℕ)
  deriving DecidableEq, Repr

/-- A configuration `(label, X, Y)`. -/
abbrev Cfg := ℕ × ℕ × ℕ

/-- The effect of an instruction on the registers, with the next label. -/
def Op.exec : Op → ℕ → ℕ → Cfg
  | .dbl1 b j, X, Y => (j, 2 * X + b.toNat, Y)
  | .dbl2 b j, X, Y => (j, X, 2 * Y + b.toNat)
  | .half1 j₀ j₁, X, Y => (if X % 2 = 0 then j₀ else j₁, X / 2, Y)
  | .half2 j₀ j₁, X, Y => (if Y % 2 = 0 then j₀ else j₁, X, Y / 2)

/-- One step (`none` at a halt label). -/
def step (prog : ℕ → Option Op) (c : Cfg) : Option Cfg :=
  (prog c.1).map fun op => op.exec c.2.1 c.2.2

/-- The step relation. -/
def Step (prog : ℕ → Option Op) (c c' : Cfg) : Prop := step prog c = some c'

/-- Halting configurations: the label has no instruction. -/
def Halt (prog : ℕ → Option Op) (c : Cfg) : Prop := prog c.1 = none

theorem halt_or_step (prog : ℕ → Option Op) (c : Cfg) : Halt prog c ∨ ∃ c', Step prog c c' := by
  unfold Halt Step step
  cases prog c.1 with
  | none => exact .inl rfl
  | some op => exact .inr ⟨_, rfl⟩

theorem step_det {prog : ℕ → Option Op} {c c₁ c₂ : Cfg} (h₁ : Step prog c c₁)
    (h₂ : Step prog c c₂) : c₁ = c₂ := by
  unfold Step at h₁ h₂; rw [h₁] at h₂; exact Option.some.inj h₂

theorem step_iff {prog : ℕ → Option Op} {i X Y : ℕ} {c' : Cfg} :
    Step prog (i, X, Y) c' ↔ ∃ op, prog i = some op ∧ op.exec X Y = c' := by
  simp [Step, step]

theorem det (prog : ℕ → Option Op) : Det (Step prog) :=
  fun _ _ _ h₁ h₂ => step_det h₁ h₂

theorem stuck (prog : ℕ → Option Op) : ∀ y y', Halt prog y → ¬ Step prog y y' := by
  intro y y' hy hs
  unfold Step step at hs
  unfold Halt at hy
  rw [hy] at hs
  cases hs

theorem step_of_prog {prog : ℕ → Option Op} {i : ℕ} {o : Op} (h : prog i = some o) (X Y : ℕ) :
    Step prog (i, X, Y) (o.exec X Y) := by
  simp [Step, step, h]

/-- Run with fuel; the flag reports that a halting configuration was reached. -/
def run (prog : ℕ → Option Op) : ℕ → Cfg → Cfg × Bool
  | 0, c => (c, false)
  | fuel + 1, c => match step prog c with
    | none => (c, true)
    | some c' => run prog fuel c'

end URTM.Univ.TRM
