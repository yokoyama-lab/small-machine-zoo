/-
  改良版の 3 状態化（docs/09_three_state_2026-09-26.md）の一般証明の土台。

  * 左右反転（`mirror`）: 規則の方向を入れ替えた機械は、テープを折り返した配置（`flipC`）の上で元の機械と
    1 ステップずつ一致する。決定性・可逆性・停止は保たれる。
  * 条件付きの実行（`GRun`）: 各ステップの行き先の配置が述語 G を満たす実行。1WU 機械の掃引の補題が
    「行き先の状態が読みうる記号」の仮定（計数記号の刈り込みの健全性）を運ぶのに使う。

  mathlib 非依存。未証明の穴・新規公理・native_decide を使わない。
-/
import URTM.SimLemmas

namespace URTM.Conv3Base

open URTM URTM.KState URTM.SimLemmas

variable {Q P S : Type}

/-! ## 1. 左右反転 -/

/-- 規則の方向を入れ替える。 -/
def flipR (r : Rule Q P S) : Rule Q P S := { p := r.p, s := r.s, t := r.t, d := opp r.d, q := r.q }

/-- **左右反転した機械**。 -/
def mirror (T : Machine Q P S) : Machine Q P S := T.map flipR

/-- 配置を位置 0 で折り返す。 -/
def flipC (c : Cfg Q P S) : Cfg Q P S := { st := c.st, pos := -c.pos, tape := fun i => c.tape (-i) }

theorem opp_opp (d : Dir) : opp (opp d) = d := by cases d <;> rfl
theorem mv_opp (d : Dir) : mv (opp d) = - mv d := by cases d <;> rfl

theorem flipR_flipR (r : Rule Q P S) : flipR (flipR r) = r := by
  cases r; simp [flipR, opp_opp]

theorem flipR_inj {r r' : Rule Q P S} (h : flipR r = flipR r') : r = r' := by
  rw [← flipR_flipR r, h, flipR_flipR]

theorem mirror_mirror (T : Machine Q P S) : mirror (mirror T) = T := by
  simp [mirror, List.map_map, Function.comp_def, flipR_flipR]

theorem flipC_flipC (c : Cfg Q P S) : flipC (flipC c) = c := by
  cases c; simp [flipC]

theorem mem_mirror {T : Machine Q P S} {r : Rule Q P S} : r ∈ mirror T ↔ flipR r ∈ T := by
  constructor
  · intro h; obtain ⟨r', hr', rfl⟩ := List.mem_map.mp h; rwa [flipR_flipR]
  · intro h; exact List.mem_map.mpr ⟨flipR r, h, flipR_flipR r⟩

theorem fire_flip (r : Rule Q P S) (c : Cfg Q P S) : flipC (fire r c) = fire (flipR r) (flipC c) := by
  simp only [flipC, fire, flipR, mv_opp]
  congr 1
  · omega
  · funext i; simp only [upd]
    by_cases h : i = -c.pos
    · rw [if_pos h, if_pos (by omega)]
    · rw [if_neg h, if_neg (by omega)]

theorem step_mirror {T : Machine Q P S} {c c' : Cfg Q P S} (h : Step T c c') :
    Step (mirror T) (flipC c) (flipC c') := by
  obtain ⟨r, hr, hst, hs, rfl⟩ := h
  refine ⟨flipR r, mem_mirror.mpr (by rwa [flipR_flipR]), hst, ?_, fire_flip r c⟩
  simp only [flipC, Int.neg_neg]; exact hs

theorem stepN_mirror {T : Machine Q P S} {n : Nat} {a b : Cfg Q P S} (h : StepN T n a b) :
    StepN (mirror T) n (flipC a) (flipC b) := by
  induction h with
  | refl => exact .refl _
  | cons h _ ih => exact .cons (step_mirror h) ih

theorem stepN_mirror_iff {T : Machine Q P S} {n : Nat} {a b : Cfg Q P S} :
    StepN (mirror T) n (flipC a) (flipC b) ↔ StepN T n a b := by
  refine ⟨fun h => ?_, stepN_mirror⟩
  have := stepN_mirror h
  rwa [mirror_mirror, flipC_flipC, flipC_flipC] at this

theorem halted_mirror {T : Machine Q P S} {c : Cfg Q P S} (h : Halted T c) : Halted (mirror T) (flipC c) := by
  intro c' hs
  have := step_mirror hs
  rw [mirror_mirror, flipC_flipC] at this
  exact h _ this

theorem halted_mirror_iff {T : Machine Q P S} {c : Cfg Q P S} : Halted (mirror T) (flipC c) ↔ Halted T c := by
  refine ⟨fun h => ?_, halted_mirror⟩
  have := halted_mirror h
  rwa [mirror_mirror, flipC_flipC] at this

theorem haltsIn_mirror_iff {T : Machine Q P S} {n : Nat} {a e : Cfg Q P S} :
    HaltsIn (mirror T) n (flipC a) (flipC e) ↔ HaltsIn T n a e := by
  simp only [HaltsIn, stepN_mirror_iff, halted_mirror_iff]

/-- 反転した機械の停止配置は、ある配置の折り返し。 -/
theorem haltsIn_mirror_of {T : Machine Q P S} {n : Nat} {a e : Cfg Q P S}
    (h : HaltsIn (mirror T) n (flipC a) e) : HaltsIn T n a (flipC e) := by
  rw [← haltsIn_mirror_iff, flipC_flipC]; exact h

theorem det_mirror {T : Machine Q P S} (hD : Deterministic T) : Deterministic (mirror T) := by
  intro r₁ h₁ r₂ h₂ hne hp hs
  exact hD _ (mem_mirror.mp h₁) _ (mem_mirror.mp h₂) (fun e => hne (flipR_inj e)) hp hs

theorem rev_mirror {T : Machine Q P S} (hR : Reversible T) : Reversible (mirror T) := by
  intro r₁ h₁ r₂ h₂ hne hq
  obtain ⟨hd, ht⟩ := hR _ (mem_mirror.mp h₁) _ (mem_mirror.mp h₂) (fun e => hne (flipR_inj e)) hq
  exact ⟨opp_inj hd, ht⟩

/-! ## 2. 条件付きの実行 -/

/-- 各ステップの行き先が G を満たす、ちょうど n ステップの実行。 -/
inductive GRun (T : Machine Q P S) (G : Cfg Q P S → Prop) : Nat → Cfg Q P S → Cfg Q P S → Prop
  | refl (c : Cfg Q P S) : GRun T G 0 c c
  | cons {n : Nat} {c c' c'' : Cfg Q P S} : Step T c c' → G c' → GRun T G n c' c'' → GRun T G (n + 1) c c''

theorem GRun.trans {T : Machine Q P S} {G : Cfg Q P S → Prop} {n m : Nat} {a b c : Cfg Q P S}
    (h₁ : GRun T G n a b) (h₂ : GRun T G m b c) : GRun T G (n + m) a c := by
  induction h₁ with
  | refl => simpa using h₂
  | cons h hg _ ih =>
    have := GRun.cons h hg (ih h₂)
    rwa [show ∀ k l : Nat, k + 1 + l = k + l + 1 from fun k l => by omega]

theorem GRun.single {T : Machine Q P S} {G : Cfg Q P S → Prop} {a b : Cfg Q P S} (h : Step T a b) (hg : G b) :
    GRun T G 1 a b := GRun.cons h hg (GRun.refl b)

end URTM.Conv3Base
