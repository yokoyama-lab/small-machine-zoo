/-
  2 状態 RTM の停止問題の決定可能性 その 5: 鏡像。**手書き**。

  テープを x ↦ -x で折り返し、向き L/R を入れ替えると、規則 `mirπ π` の実行になる。
  右の半直線についての結果（`depth_bound`・`inside_halt_bound`）を左の半直線へ移すのに使う。
-/
import URTM.TSDClock

namespace URTM.TwoState

theorem flipD_flipD (d : Dir) : flipD (flipD d) = d := by cases d <;> rfl

def mirπ (π : Rule) : Rule := fun d s => (π (flipD d) s).map (fun r => (r.1, flipD r.2))

def mirC (c : Conf2) : Conf2 := ⟨fun x => c.tape (-x), -c.pos, flipD c.dir⟩

theorem move_mir (d : Dir) (p : Int) : move (flipD d) (-p) = -(move d p) := by
  cases d <;> simp [flipD, move] <;> omega

theorem step2_mir (π : Rule) (c : Conf2) :
    step2 (mirπ π) (mirC c) = (step2 π c).map mirC := by
  have hread : (mirC c).tape (mirC c).pos = c.tape c.pos := by
    show c.tape (-(-c.pos)) = c.tape c.pos; rw [Int.neg_neg]
  have hdir : (mirC c).dir = flipD c.dir := rfl
  cases hr : π c.dir (c.tape c.pos) with
  | none =>
    have h1 : step2 (mirπ π) (mirC c) = none := by
      unfold step2; rw [hread, hdir]; simp [mirπ, flipD_flipD, hr]
    have h2 : step2 π c = none := by unfold step2; rw [hr]
    rw [h1, h2]; rfl
  | some vd =>
    obtain ⟨v, d'⟩ := vd
    have h2 : step2 π c = some ⟨write c.tape c.pos v, move d' c.pos, d'⟩ := by
      unfold step2; rw [hr]
    have hm : mirπ π (flipD c.dir) (c.tape c.pos) = some (v, flipD d') := by
      simp [mirπ, flipD_flipD, hr]
    have h1 : step2 (mirπ π) (mirC c)
        = some ⟨write (mirC c).tape (mirC c).pos v, move (flipD d') (mirC c).pos, flipD d'⟩ := by
      unfold step2; rw [hread, hdir, hm]
    rw [h1, h2]
    show some _ = some (mirC _)
    congr 1
    show (⟨write (fun x => c.tape (-x)) (-c.pos) v, move (flipD d') (-c.pos), flipD d'⟩ : Conf2)
        = ⟨fun x => write c.tape c.pos v (-x), -(move d' c.pos), flipD d'⟩
    rw [move_mir]
    congr 1
    funext x
    unfold write
    by_cases h : x = -c.pos
    · have h' : -x = c.pos := by omega
      simp [h, h']
    · have h' : ¬ -x = c.pos := by omega
      simp [h, h']

theorem run2_mir (π : Rule) :
    ∀ (n : Nat) (c : Conf2), run2 (mirπ π) n (mirC c) = (run2 π n c).map mirC := by
  intro n
  induction n with
  | zero => intro c; rfl
  | succ n ih =>
    intro c
    cases hs : step2 π c with
    | none =>
      have hs' : step2 (mirπ π) (mirC c) = none := by rw [step2_mir, hs]; rfl
      rw [run2_succ_none _ n hs', run2_succ_none _ n hs]; rfl
    | some c' =>
      have hs' : step2 (mirπ π) (mirC c) = some (mirC c') := by rw [step2_mir, hs]; rfl
      rw [run2_succ_some _ n hs', run2_succ_some _ n hs, ih]

theorem NoZ_mir {π : Rule} (hZ : NoZ π) : NoZ (mirπ π) := by
  intro d s v d' h
  simp only [mirπ] at h
  cases hr : π (flipD d) s with
  | none => rw [hr] at h; exact absurd h (by simp)
  | some r =>
    rw [hr] at h
    have hh : (r.1, flipD r.2) = (v, d') := Option.some.inj h
    have e : d' = flipD r.2 := (congrArg Prod.snd hh).symm
    obtain ⟨r1, r2⟩ := r
    have := hZ _ _ _ _ hr
    rw [e]; cases r2 <;> simp [flipD] at this ⊢

theorem Closed_mir {π : Rule} {nsym : Nat} (hcl : Closed π nsym) : Closed (mirπ π) nsym := by
  intro d s v d' hs h
  simp only [mirπ] at h
  cases hr : π (flipD d) s with
  | none => rw [hr] at h; exact absurd h (by simp)
  | some r =>
    rw [hr] at h
    have hh : (r.1, flipD r.2) = (v, d') := Option.some.inj h
    have e : v = r.1 := (congrArg Prod.fst hh).symm
    obtain ⟨r1, r2⟩ := r
    rw [e]; exact hcl _ _ _ _ hs hr

theorem tr_mir (π : Rule) (c : Conf2) (t : Nat) : tr (mirπ π) (mirC c) t = mirC (tr π c t) := by
  unfold tr
  rw [run2_mir]
  cases run2 π t c <;> rfl

theorem HaltRun.mir {π : Rule} {c : Conf2} {T : Nat} (hR : HaltRun π c T) :
    HaltRun (mirπ π) (mirC c) T := by
  refine ⟨?_, ?_⟩
  · rw [run2_mir, hR.run T (Nat.le_refl _)]; simp
  · rw [run2_mir, hR.dead]; rfl

theorem P_mir (π : Rule) (c : Conf2) (t : Nat) : P (mirπ π) (mirC c) t = - P π c t := by
  show (tr (mirπ π) (mirC c) t).pos = _
  rw [tr_mir]; rfl

/-- 左の半直線 (-∞, a-1] への入場（位置 a → a-1）。 -/
def LStep (π : Rule) (c : Conf2) (a : Int) (t : Nat) : Prop :=
  P π c t = a ∧ P π c (t + 1) = a - 1

instance (π : Rule) (c : Conf2) (a : Int) (t : Nat) : Decidable (LStep π c a t) := by
  unfold LStep; infer_instance

def EntL (π : Rule) (c : Conf2) (a : Int) : Nat → Nat
  | 0 => 0
  | t + 1 => EntL π c a t + if LStep π c a t then 1 else 0

theorem EntL_eq_mir (π : Rule) (c : Conf2) (a : Int) :
    ∀ t, EntL π c a t = Ent (mirπ π) (mirC c) (1 - a) t := by
  intro t
  induction t with
  | zero => rfl
  | succ t ih =>
    have hiff : LStep π c a t ↔ EntStep (mirπ π) (mirC c) (1 - a) t := by
      unfold LStep EntStep
      rw [P_mir, P_mir]
      constructor
      · rintro ⟨h1, h2⟩; constructor <;> omega
      · rintro ⟨h1, h2⟩; constructor <;> omega
    show EntL π c a t + (if LStep π c a t then 1 else 0)
        = Ent (mirπ π) (mirC c) (1 - a) t + (if EntStep (mirπ π) (mirC c) (1 - a) t then 1 else 0)
    rw [ih]
    by_cases h : LStep π c a t
    · rw [if_pos h, if_pos (hiff.mp h)]
    · rw [if_neg h, if_neg (fun h' => h (hiff.mpr h'))]

section Left
variable {π : Rule} {c : Conf2} {T : Nat}

/-- **左の深さの上界**。 -/
theorem HaltRun.depth_bound_left (hZ : NoZ π) (hR : HaltRun π c T) (a : Int)
    (hblank : ∀ x, x ≤ a - 1 → c.tape x = 0) (h0 : a ≤ c.pos) :
    ∀ t, t ≤ T → a - 1 - (EntL π c a T : Int) < P π c t := by
  intro t ht
  have := hR.mir.depth_bound (NoZ_mir hZ) (1 - a)
    (fun x hx => by show c.tape (-x) = 0; exact hblank (-x) (by omega))
    (by show -c.pos < 1 - a; omega) t ht
  rw [P_mir, ← EntL_eq_mir] at this
  omega

/-- **左の半直線の中で停止するなら、入場は 2·nsym + 1 回以下**。 -/
theorem HaltRun.inside_halt_bound_left (hZ : NoZ π) (hR : HaltRun π c T) {nsym : Nat}
    (hcl : Closed π nsym) (hinit : ∀ x, c.tape x < nsym) (a : Int)
    (hblank : ∀ x, x ≤ a - 1 → c.tape x = 0) (h0 : a ≤ c.pos) (hin : P π c T ≤ a - 1) :
    EntL π c a T ≤ 2 * nsym + 1 := by
  rw [EntL_eq_mir]
  exact hR.mir.inside_halt_bound (NoZ_mir hZ) (Closed_mir hcl)
    (fun x => by show c.tape (-x) < nsym; exact hinit (-x)) (1 - a)
    (fun x hx => by show c.tape (-x) = 0; exact hblank (-x) (by omega))
    (by show -c.pos < 1 - a; omega)
    (by rw [P_mir]; omega)

end Left

end URTM.TwoState
