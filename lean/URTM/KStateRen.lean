/-
  状態の名前の付け替え。単射 `f : Q → Q'` で規則と配置の状態を付け替えると、1 ステップ・停止配置・
  ちょうど n ステップの停止が保たれる（`haltsIn_ren`）。逆写像を持つ付け替えなら、付け替えた機械の
  停止は元の機械の停止から来る（`haltsIn_ren_rev`）。

  未証明の穴・新規公理・native_decide を使わない。mathlib 非依存。
-/
import URTM.KState

namespace URTM.KStateRen

open URTM.KState

variable {Q Q' P S : Type}

/-- 行き先の付け替え（疑似状態はそのまま）。 -/
def renT (f : Q → Q') : Tgt Q P → Tgt Q' P
  | .go q => .go (f q)
  | .halt h => .halt h

/-- 規則の状態の付け替え。 -/
def renR (f : Q → Q') (r : Rule Q P S) : Rule Q' P S :=
  ⟨f r.p, r.s, r.t, r.d, renT f r.q⟩

/-- 配置の状態の付け替え。 -/
def renC (f : Q → Q') (c : Cfg Q P S) : Cfg Q' P S :=
  ⟨renT f c.st, c.pos, c.tape⟩

theorem renC_fire (f : Q → Q') (r : Rule Q P S) (c : Cfg Q P S) :
    renC f (fire r c) = fire (renR f r) (renC f c) := rfl

theorem renC_renC {f : Q → Q'} {g : Q' → Q} (hfg : ∀ b, f (g b) = b) (c : Cfg Q' P S) :
    renC f (renC g c) = c := by
  rcases c with ⟨st, pos, tape⟩
  cases st <;> simp [renC, renT, hfg]

theorem step_ren (f : Q → Q') {T : Machine Q P S} {c c' : Cfg Q P S} (h : Step T c c') :
    Step (T.map (renR f)) (renC f c) (renC f c') := by
  obtain ⟨r, hr, hst, hs, rfl⟩ := h
  refine ⟨renR f r, List.mem_map.mpr ⟨r, hr, rfl⟩, ?_, hs, rfl⟩
  show renT f c.st = _
  rw [hst]
  rfl

theorem stepN_ren (f : Q → Q') {T : Machine Q P S} :
    ∀ {n : Nat} {c c' : Cfg Q P S}, StepN T n c c' →
      StepN (T.map (renR f)) n (renC f c) (renC f c')
  | _, _, _, .refl _ => .refl _
  | _, _, _, .cons h hs => .cons (step_ren f h) (stepN_ren f hs)

theorem halted_ren {f : Q → Q'} (hf : ∀ a b, f a = f b → a = b) {T : Machine Q P S}
    {e : Cfg Q P S} (h : Halted T e) : Halted (T.map (renR f)) (renC f e) := by
  rintro c' ⟨ρ, hρ, hst, hs, -⟩
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hρ
  apply h (fire r e)
  refine ⟨r, hr, ?_, hs, rfl⟩
  cases he : e.st with
  | go q =>
    have hq : f q = f r.p := by simpa [renC, renR, renT, he] using hst
    rw [hf _ _ hq]
  | halt _ => simp [renC, renT, he] at hst

/-- **付け替えは停止を保つ**（単射なら）。 -/
theorem haltsIn_ren {f : Q → Q'} (hf : ∀ a b, f a = f b → a = b) {T : Machine Q P S} {n : Nat}
    {c e : Cfg Q P S} (h : HaltsIn T n c e) :
    HaltsIn (T.map (renR f)) n (renC f c) (renC f e) :=
  ⟨stepN_ren f h.1, halted_ren hf h.2⟩

/-- **逆写像 `g` を持つ付け替え**: 付け替えた機械の停止は、元の機械の同じ歩数の停止から来る。 -/
theorem haltsIn_ren_rev {f : Q → Q'} {g : Q' → Q} (hgf : ∀ a, g (f a) = a)
    (hfg : ∀ b, f (g b) = b) {T : Machine Q P S} {n : Nat} {c : Cfg Q P S} {e' : Cfg Q' P S}
    (h : HaltsIn (T.map (renR f)) n (renC f c) e') : HaltsIn T n c (renC g e') := by
  have hg : ∀ a b, g a = g b → a = b := fun a b hab => by rw [← hfg a, ← hfg b, hab]
  have hid : ∀ r : Rule Q P S, renR g (renR f r) = r := by
    intro ⟨p, s, t, d, q⟩
    cases q <;> simp [renR, renT, hgf]
  have h2 := haltsIn_ren hg h
  rwa [List.map_map, show renR g ∘ renR f = id from funext hid, List.map_id, renC_renC hgf] at h2

end URTM.KStateRen
