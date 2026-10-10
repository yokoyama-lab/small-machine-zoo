/-
  `KRun` の検査器の、規則を「引き当ての関数」で引く版。

  `KRun.check` は 1 ステップごとに表（規則のリスト）を先頭から線形に探す。3.8 万本の表（URTM(3,36654)）では
  これがカーネルの評価で重すぎるので、(状態, 記号) から規則を返す関数 `f` を使う。

  * `fstep bk f z` — 1 ステップ。`f p h` の返した規則の (状態, 記号) が (p, h) と一致することをその場で確かめる。
  * `fhalted f z` — 状態が疑似状態か、`f p h = none`。
  * `fcheck` / `freach` — `KRun.check` / `reach` と同じ。

  健全性（`fhalts_of_check`・`fhalts_of_reach`）の仮定は、`f` の値が表 T の規則であること（`hs`）と、
  T の規則はどれも自分の (状態, 記号) で `f` に引き当てられること（`hc`。停止の判定に使う）だけ。

  mathlib 非依存。未証明の穴・新規公理・native_decide を使わない。
-/
import URTM.KRun

namespace URTM.KState.RunF

open URTM URTM.KState URTM.KState.Run URTM.CTSH.Sim

variable {Q P S : Type} [DecidableEq Q] [DecidableEq S]

/-- 1 ステップ（規則は `f` で引く）。停止配置・左端からの逸脱・`f` の値の不一致では `none`。 -/
def fstep (bk : S) (f : Q → S → Option (Rule Q P S)) (z : Zip Q P S) : Option (Zip Q P S) :=
  match z.st with
  | .halt _ => none
  | .go p =>
    match f p z.h with
    | none => none
    | some r =>
      if r.p = p ∧ r.s = z.h then
        match r.d, z.l with
        | .R, l => some ⟨r.q, r.t :: l, z.r.headD bk, z.r.tail⟩
        | .Z, l => some ⟨r.q, l, r.t, z.r⟩
        | .L, y :: l => some ⟨r.q, l, y, r.t :: z.r⟩
        | .L, [] => none
      else none

/-- 停止配置の判定（疑似状態、または `f` が規則を返さない）。 -/
def fhalted (f : Q → S → Option (Rule Q P S)) (z : Zip Q P S) : Bool :=
  match z.st with
  | .halt _ => true
  | .go p => (f p z.h).isNone

/-- ちょうど `n` ステップの実行。 -/
def frun (bk : S) (f : Q → S → Option (Rule Q P S)) : Nat → Zip Q P S → Option (Zip Q P S)
  | 0, z => some z
  | n + 1, z =>
    match fstep bk f z with
    | none => none
    | some z' => frun bk f n z'

/-- 検査器: `z` からちょうど `n` ステップで `e` に達し、`e` は停止配置。 -/
def fcheck [DecidableEq P] (bk : S) (f : Q → S → Option (Rule Q P S)) (n : Nat) (z e : Zip Q P S) : Bool :=
  match frun bk f n z with
  | none => false
  | some z' => decide (z' = e) && fhalted f z'

/-- 途中までの検査器。 -/
def freach [DecidableEq P] (bk : S) (f : Q → S → Option (Rule Q P S)) (n : Nat) (z m : Zip Q P S) : Bool :=
  match frun bk f n z with
  | none => false
  | some z' => decide (z' = m)

/-! ## 健全性 -/

section Sound
variable {T : Machine Q P S} {f : Q → S → Option (Rule Q P S)} {bk : S}

theorem fstep_sound (hs : ∀ p s r, f p s = some r → r ∈ T) {z z' : Zip Q P S}
    (h : fstep bk f z = some z') : Step T (z.cfg bk) (z'.cfg bk) := by
  obtain ⟨st, l, hd, rr⟩ := z
  cases st with
  | halt _ => simp [fstep] at h
  | go p =>
    simp only [fstep] at h
    split at h
    · cases h
    · rename_i r hl
      have hmem := hs _ _ _ hl
      split at h
      · rename_i hps
        obtain ⟨hp, hs'⟩ := hps
        obtain ⟨rp, rs, rt, rd, rq⟩ := r
        simp only at hp hs'
        subst hp hs'
        cases rd with
        | R =>
          simp only [Option.some.injEq] at h; subst h
          have := stepR' (bk := bk) hmem l rr
          rw [zr_headD] at this
          exact this
        | Z =>
          simp only [Option.some.injEq] at h; subst h
          exact stepZ hmem l rr
        | L =>
          cases l with
          | nil => simp at h
          | cons y l =>
            simp only [Option.some.injEq] at h; subst h
            exact stepL hmem y l rr
      · cases h

omit [DecidableEq Q] [DecidableEq S] in
theorem fhalted_sound (hc : ∀ r ∈ T, f r.p r.s = some r) {z : Zip Q P S}
    (h : fhalted f z = true) : Halted T (z.cfg bk) := by
  intro c' ⟨r, hr, hst, hs, _⟩
  obtain ⟨st, l, hd, rr⟩ := z
  have hread := zc_read (bk := bk) st l hd rr
  simp only [Zip.cfg] at hst hs
  rw [hread] at hs
  simp only [zc] at hst
  subst hst
  simp only [fhalted, Option.isNone_iff_eq_none] at h
  have := hc r hr
  rw [← hs, h] at this
  cases this

theorem frun_sound (hs : ∀ p s r, f p s = some r → r ∈ T) :
    ∀ (n : Nat) {z e : Zip Q P S}, frun bk f n z = some e → StepN T n (z.cfg bk) (e.cfg bk)
  | 0, z, e, h => by
    simp only [frun, Option.some.injEq] at h; subst h; exact .refl _
  | n + 1, z, e, h => by
    simp only [frun] at h
    split at h
    · cases h
    · rename_i z' hz
      exact .cons (fstep_sound hs hz) (frun_sound hs n h)

variable [DecidableEq P]

/-- **健全性**: 検査器が通れば、`z` の表す配置からちょうど `n` ステップで停止配置 `e` に達する。 -/
theorem fhalts_of_check (hs : ∀ p s r, f p s = some r → r ∈ T) (hc : ∀ r ∈ T, f r.p r.s = some r)
    {n : Nat} {z e : Zip Q P S} (h : fcheck bk f n z e = true) : HaltsIn T n (z.cfg bk) (e.cfg bk) := by
  simp only [fcheck] at h
  split at h
  · cases h
  · rename_i z' hz
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨rfl, hh⟩ := h
    exact ⟨frun_sound hs n hz, fhalted_sound hc hh⟩

/-- 途中までの検査器の健全性。 -/
theorem fstepN_of_reach (hs : ∀ p s r, f p s = some r → r ∈ T) {n : Nat} {z m : Zip Q P S}
    (h : freach bk f n z m = true) : StepN T n (z.cfg bk) (m.cfg bk) := by
  simp only [freach] at h
  split at h
  · cases h
  · rename_i z' hz
    simp only [decide_eq_true_eq] at h
    subst h
    exact frun_sound hs n hz

/-- 分割した実行の合成。 -/
theorem fhalts_of_reach (hs : ∀ p s r, f p s = some r → r ∈ T) {a b : Nat} {z m e : Zip Q P S}
    (h : freach bk f a z m = true) (h' : HaltsIn T b (m.cfg bk) (e.cfg bk)) :
    HaltsIn T (a + b) (z.cfg bk) (e.cfg bk) :=
  ⟨(fstepN_of_reach hs h).trans h'.1, h'.2⟩

end Sound

end URTM.KState.RunF
