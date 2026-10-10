/-
  停止つき巡回タグ系（CTSH）。Morita 2017, *Theory of Reversible Computing*, Def. 7.5。

  Ĉ = (k, (halt, w₁, …, w_{k−1}))。Lean では `C : CTSH := List (List Ch)` を
  [w₁, …, w_{k−1}] とし、k = |C| + 1。ID は (v, m)（v ∈ {Y,N}*, 0 ≤ m < k）。

      (Y v, m) ⇒ (v w_m, m+1 mod k)   ただし m ≠ 0
      (N v, m) ⇒ (v,     m+1 mod k)

  (Y v, 0) と (λ, m) には後続が無く、停止 ID と呼ぶ（`halting_iff_noStep` で確かめる）。
  mathlib 非依存。
-/

namespace URTM.CTSH

/-- CTSH の記号。 -/
inductive Ch where
  | Y
  | N
  deriving DecidableEq, Repr

/-- CTSH の本体: 生成規則 [w₁, …, w_{k−1}]。周期 k = 長さ + 1（phase 0 は halt）。 -/
abbrev CTSH := List (List Ch)

/-- 周期 k。 -/
def CTSH.k (C : CTSH) : Nat := C.length + 1

/-- 相 m の生成規則 w_m（1 ≤ m ≤ k−1）。m = 0 では空列（使われない）。 -/
def prod (C : CTSH) (m : Nat) : List Ch :=
  match m with
  | 0 => []
  | m + 1 => C.getD m []

/-- ID。 -/
abbrev ID := List Ch × Nat

/-- 1 ステップ（Def. 7.5 の ⇒）。相は k 未満に限る。 -/
inductive CStep (C : CTSH) : ID → ID → Prop
  | y {v : List Ch} {m : Nat} : m ≠ 0 → m < C.k → CStep C (.Y :: v, m) (v ++ prod C m, (m + 1) % C.k)
  | n {v : List Ch} {m : Nat} : m < C.k → CStep C (.N :: v, m) (v, (m + 1) % C.k)

/-- 停止 ID: (Y v, 0) または (λ, m)。 -/
def Halting (C : CTSH) (s : ID) : Prop :=
  s.2 < C.k ∧ ((∃ v, s.1 = .Y :: v ∧ s.2 = 0) ∨ s.1 = [])

/-- ちょうど n ステップ。 -/
inductive CStepN (C : CTSH) : Nat → ID → ID → Prop
  | refl (s : ID) : CStepN C 0 s s
  | cons {n : Nat} {s s' s'' : ID} : CStep C s s' → CStepN C n s' s'' → CStepN C (n + 1) s s''

/-- n ステップで停止 ID f に達する（完全な計算過程、Def. 7.5）。 -/
def CHaltsIn (C : CTSH) (n : Nat) (s f : ID) : Prop :=
  CStepN C n s f ∧ Halting C f

theorem CStep.phase_lt {C : CTSH} {s s' : ID} (h : CStep C s s') : s'.2 < C.k := by
  cases h <;> exact Nat.mod_lt _ (by simp [CTSH.k])

/-- 相 < k の ID について、停止 ID ⇔ 後続が無い（Def. 7.5 の「停止 ID」の定義の確認）。 -/
theorem halting_iff_noStep (C : CTSH) (v : List Ch) (m : Nat) (hm : m < C.k) :
    Halting C (v, m) ↔ ∀ s', ¬ CStep C (v, m) s' := by
  constructor
  · rintro ⟨_, ⟨v', hv, h0⟩ | hv⟩ s' hs
    · simp only at hv h0; subst hv; subst h0
      cases hs with
      | y h _ => exact h rfl
    · simp only at hv; subst hv; cases hs
  · intro h
    refine ⟨hm, ?_⟩
    match v with
    | [] => exact .inr rfl
    | .N :: v => exact absurd (CStep.n hm) (h _)
    | .Y :: v =>
      by_cases h0 : m = 0
      · exact .inl ⟨v, rfl, h0⟩
      · exact absurd (CStep.y h0 hm) (h _)

theorem cstep_func {C : CTSH} {s a b : ID} (ha : CStep C s a) (hb : CStep C s b) : a = b := by
  cases ha <;> cases hb <;> rfl

theorem CStepN.phase_lt {C : CTSH} {n : Nat} {s f : ID} (h : CStepN C n s f) (hs : s.2 < C.k) :
    f.2 < C.k := by
  induction h with
  | refl => exact hs
  | cons h₁ _ ih => exact ih h₁.phase_lt

/-- 停止しない CTSH は任意の長さの計算を持つ。 -/
theorem run_of_not_halts {C : CTSH} {s : ID} (hs : s.2 < C.k)
    (hn : ∀ n f, ¬ CHaltsIn C n s f) : ∀ n, ∃ f, CStepN C n s f := by
  intro n
  induction n generalizing s with
  | zero => exact ⟨s, .refl s⟩
  | succ n ih =>
    have hnh : ¬ Halting C s := fun h => hn 0 s ⟨.refl s, h⟩
    obtain ⟨v, m⟩ := s
    have : ∃ s', CStep C (v, m) s' := by
      rw [halting_iff_noStep C v m hs] at hnh
      exact Classical.byContradiction fun h' => hnh fun s' hs' => h' ⟨s', hs'⟩
    obtain ⟨s', hs'⟩ := this
    obtain ⟨f, hf⟩ := ih (s := s') hs'.phase_lt (fun k f h => hn (k + 1) f ⟨.cons hs' h.1, h.2⟩)
    exact ⟨f, .cons hs' hf⟩

/-- 有限回の実行（`decide` による具体例の照合用）。停止 ID で止まる。 -/
def step? (C : CTSH) : ID → Option ID
  | (.Y :: v, m) => if m = 0 then none else some (v ++ prod C m, (m + 1) % C.k)
  | (.N :: v, m) => some (v, (m + 1) % C.k)
  | ([], _) => none

def run (C : CTSH) : Nat → ID → ID × Bool
  | 0, s => (s, false)
  | fuel + 1, s => match step? C s with
    | none => (s, true)
    | some s' => run C fuel s'

theorem step?_sound {C : CTSH} {s s' : ID} (hs : s.2 < C.k) (h : step? C s = some s') :
    CStep C s s' := by
  obtain ⟨v, m⟩ := s
  match v, h with
  | .Y :: v, h =>
    simp only [step?] at h
    split at h
    · cases h
    · cases h; exact CStep.y (by assumption) hs
  | .N :: v, h => simp only [step?, Option.some.injEq] at h; subst h; exact CStep.n hs

theorem step?_none {C : CTSH} {s : ID} (hs : s.2 < C.k) (h : step? C s = none) : Halting C s := by
  obtain ⟨v, m⟩ := s
  refine ⟨hs, ?_⟩
  match v, h with
  | [], _ => exact .inr rfl
  | .Y :: v, h =>
    simp only [step?] at h
    split at h
    · exact .inl ⟨v, rfl, by assumption⟩
    · cases h
  | .N :: v, h => simp [step?] at h

/-- `run` が停止を報告したなら、それは本当に完全な計算過程（`decide` で具体例を照合するための橋）。 -/
theorem run_sound {C : CTSH} : ∀ (fuel : Nat) {s f : ID}, s.2 < C.k →
    run C fuel s = (f, true) → ∃ n, CHaltsIn C n s f
  | 0, _, _, _, h => by simp [run] at h
  | fuel + 1, s, f, hs, h => by
    simp only [run] at h
    split at h
    · rename_i hn
      cases h
      exact ⟨0, .refl _, step?_none hs hn⟩
    · rename_i s' hs'
      have hst := step?_sound hs hs'
      obtain ⟨n, h₁, h₂⟩ := run_sound fuel hst.phase_lt h
      exact ⟨n + 1, .cons hst h₁, h₂⟩

end URTM.CTSH
