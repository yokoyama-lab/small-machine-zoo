/-
  機械の変換を CTSH の模倣定理に合成するための一般補題（機械の型に依らない）。

  * `StepN.last`・`stepN_go`: 計算過程の最後の 1 ステップを取り出す、途中の配置が実状態であること。
  * `run_forever`: 停止しない機械は任意の長さの計算を持つ。
  * **停止規則の除去** `dropHalt T`（疑似状態へ入る規則を取り除いた機械）: 停止規則がどれも 0 シフトで
    読んだ記号をそのまま書くなら、T の「停止の 3 項」（停止の順方向・逆方向・非停止の同値）は、
    停止配置を「停止規則を適用する直前の配置」`unhalt f e` に置き換えて dropHalt T にも成り立つ
    （`drop_simulates`）。Morita の (4,168)・(138,2) は、元の機械から停止規則を除いたものを変換している。

  mathlib 非依存。未証明の穴・新規公理・native_decide を使わない。
-/
import URTM.KState
import URTM.CTSH

namespace URTM.SimLemmas

open URTM URTM.KState URTM.CTSH

variable {Q P S : Type}

theorem Step.go {T : Machine Q P S} {c c' : Cfg Q P S} (h : Step T c c') : ∃ p, c.st = .go p :=
  let ⟨r, _, hst, _⟩ := h; ⟨r.p, hst⟩

theorem StepN.last {T : Machine Q P S} : ∀ {n : Nat} {a e : Cfg Q P S}, StepN T (n + 1) a e →
    ∃ e₀, StepN T n a e₀ ∧ Step T e₀ e := by
  intro n
  induction n with
  | zero =>
    intro a e h
    cases h with
    | cons h₁ h₂ => cases h₂; exact ⟨a, .refl a, h₁⟩
  | succ n ih =>
    intro a e h
    cases h with
    | cons h₁ h₂ =>
      obtain ⟨e₀, h₃, h₄⟩ := ih h₂
      exact ⟨e₀, .cons h₁ h₃, h₄⟩

/-- 停止しない機械は任意の長さの計算を持つ。 -/
theorem run_forever {T : Machine Q P S} {a : Cfg Q P S} (hn : ∀ n e, ¬ HaltsIn T n a e) :
    ∀ k, ∃ b, StepN T k a b := by
  intro k
  induction k with
  | zero => exact ⟨a, .refl a⟩
  | succ k ih =>
    obtain ⟨b, hb⟩ := ih
    by_cases hh : Halted T b
    · exact absurd ⟨hb, hh⟩ (hn k b)
    · obtain ⟨c, hc⟩ := exists_step_of_not_halted hh
      exact ⟨c, hb.trans (StepN.single hc)⟩

theorem halts_unique {T : Machine Q P S} (hD : Deterministic T) {N N' : Nat} {a e e' : Cfg Q P S}
    (h : HaltsIn T N a e) (h' : HaltsIn T N' a e') : e = e' := by
  obtain ⟨_, h₂⟩ := stepN_prefix hD h.1 h.2 h'.1
  exact (stepN_from_halted h'.2 h₂).2

/-- 疑似状態の配置はどの機械でも止まっている。 -/
theorem halted_of_halt {M : Machine Q P S} {c : Cfg Q P S} {h : P} (hc : c.st = .halt h) : Halted M c :=
  fun _ ⟨_, _, hst, _⟩ => by rw [hc] at hst; cases hst

section Back
variable {Q' P' S' : Type} {T : Machine Q P S} {T' : Machine Q' P' S'}

/-- 各ステップを 1 ステップ以上で模倣できるなら、n ステップの実行は n ステップ以上で模倣できる。 -/
theorem stepN_sim_of_step (E : Cfg Q P S → Cfg Q' P' S')
    (h : ∀ {c c'}, Step T c c' → ∃ N, 1 ≤ N ∧ StepN T' N (E c) (E c')) :
    ∀ {n a b}, StepN T n a b → ∃ N, n ≤ N ∧ StepN T' N (E a) (E b) := by
  intro n a b hs
  induction hs with
  | refl => exact ⟨0, Nat.le_refl _, .refl _⟩
  | cons h₁ _ ih =>
    obtain ⟨j, hj, h₁'⟩ := h h₁
    obtain ⟨N, hN, hs⟩ := ih
    exact ⟨j + N, by omega, h₁'.trans hs⟩

/-- **逆向きの一般形**: 前向き（T の停止を T' の停止 F N e へ移す）と、「T が止まらないなら、T の各計算を
    少なくとも同じ長さで T' が追える」から、T'（決定的）の停止は T の停止に対応する。 -/
theorem back_of_fwd (hD : Deterministic T') {a : Cfg Q P S} {a' : Cfg Q' P' S'}
    (F : Nat → Cfg Q P S → Cfg Q' P' S')
    (fwd : ∀ N e, HaltsIn T N a e → ∃ M, HaltsIn T' M a' (F N e))
    (run : (∀ n e, ¬ HaltsIn T n a e) → ∀ N b, StepN T N a b → ∃ M, N ≤ M ∧ ∃ b', StepN T' M a' b') :
    ∀ M e', HaltsIn T' M a' e' → ∃ N e, HaltsIn T N a e ∧ e' = F N e := by
  intro M e' he'
  by_cases hT : ∃ n e₀, HaltsIn T n a e₀
  · obtain ⟨n, e₀, h₀⟩ := hT
    obtain ⟨_, h'⟩ := fwd n e₀ h₀
    exact ⟨n, e₀, h₀, halts_unique hD he' h'⟩
  · have hn : ∀ n e, ¬ HaltsIn T n a e := fun n e h => hT ⟨n, e, h⟩
    obtain ⟨b, hb⟩ := run_forever hn (M + 1)
    obtain ⟨M', hM', b', hs⟩ := run hn _ _ hb
    have := (stepN_prefix hD he'.1 he'.2 hs).1
    omega

/-- **停止の 3 項の移送**。T の実行 a の停止を T'（決定的）の実行 a' の停止 G e へ移せて（ステップ数は減らない）、
    T が止まらないときは T の計算を T' が追えるなら、CTSH C から T への停止の 3 項（前向きの下界は `n ≤ N + 1`）は
    停止配置を G ∘ fin として T' に移る。 -/
theorem transfer3 (hD : Deterministic T') {a : Cfg Q P S} {a' : Cfg Q' P' S'} (G : Cfg Q P S → Cfg Q' P' S')
    (haltsT : ∀ N e, HaltsIn T N a e → ∃ N', N ≤ N' ∧ HaltsIn T' N' a' (G e))
    (run : (∀ n e, ¬ HaltsIn T n a e) → ∀ N b, StepN T N a b → ∃ M, N ≤ M ∧ ∃ b', StepN T' M a' b')
    (C : CTSH) (w : List Ch) (fin : List Ch → Nat → List Ch → Cfg Q P S)
    (hsim :
      (∀ n vf mf, CHaltsIn C n (w, 0) (vf, mf) → ∃ N rm, n ≤ N + 1 ∧ HaltsIn T N a (fin vf mf rm)) ∧
      (∀ N e, HaltsIn T N a e → ∃ n vf mf rm, CHaltsIn C n (w, 0) (vf, mf) ∧ e = fin vf mf rm)) :
    (∀ n vf mf, CHaltsIn C n (w, 0) (vf, mf) →
      ∃ N rm, n ≤ N + 1 ∧ HaltsIn T' N a' (G (fin vf mf rm))) ∧
    (∀ N e, HaltsIn T' N a' e → ∃ n vf mf rm, CHaltsIn C n (w, 0) (vf, mf) ∧ e = G (fin vf mf rm)) ∧
    ((∀ n e, ¬ CHaltsIn C n (w, 0) e) ↔ (∀ N e, ¬ HaltsIn T' N a' e)) := by
  have fwd : ∀ n vf mf, CHaltsIn C n (w, 0) (vf, mf) →
      ∃ N rm, n ≤ N + 1 ∧ HaltsIn T' N a' (G (fin vf mf rm)) := by
    intro n vf mf hc
    obtain ⟨N, rm, hN, hh⟩ := hsim.1 n vf mf hc
    obtain ⟨N', hN', hh'⟩ := haltsT _ _ hh
    exact ⟨N', rm, by omega, hh'⟩
  have bwd : ∀ N e, HaltsIn T' N a' e → ∃ n vf mf rm, CHaltsIn C n (w, 0) (vf, mf) ∧ e = G (fin vf mf rm) := by
    intro N e he
    obtain ⟨M, e₀, h₀, rfl⟩ := back_of_fwd hD (fun _ e => G e)
      (fun N e h => let ⟨M, _, hM⟩ := haltsT N e h; ⟨M, hM⟩) run N e he
    obtain ⟨k, vf, mf, rm, hc, rfl⟩ := hsim.2 M e₀ h₀
    exact ⟨k, vf, mf, rm, hc, rfl⟩
  refine ⟨fwd, bwd, ⟨fun hn N e he => ?_, fun hu n ⟨vf, mf⟩ hc => ?_⟩⟩
  · obtain ⟨n, vf, mf, rm, hc, _⟩ := bwd N e he
    exact hn n _ hc
  · obtain ⟨N, rm, _, hN⟩ := fwd n vf mf hc
    exact hu N _ hN

end Back

/-! ## 停止規則の除去 -/

/-- 疑似状態へ入る規則（停止規則）を取り除いた機械。 -/
def dropHalt (T : Machine Q P S) : Machine Q P S := T.filter (fun r => r.q.isGo)

/-- 停止配置を「停止規則を適用する直前の配置」に戻す（疑似状態 h を、h へ入る規則の現状態 f h に）。 -/
def unhalt (f : P → Q) (c : Cfg Q P S) : Cfg Q P S :=
  match c.st with
  | .go _ => c
  | .halt h => { c with st := .go (f h) }

variable {T : Machine Q P S}

theorem mem_dropHalt {r : Rule Q P S} : r ∈ dropHalt T ↔ r ∈ T ∧ r.q.isGo = true := by
  simp [dropHalt]

theorem Step.of_drop {c c' : Cfg Q P S} (h : Step (dropHalt T) c c') : Step T c c' :=
  let ⟨r, hr, h₁, h₂, h₃⟩ := h; ⟨r, (mem_dropHalt.mp hr).1, h₁, h₂, h₃⟩

theorem StepN.of_drop {n : Nat} {a b : Cfg Q P S} (h : StepN (dropHalt T) n a b) : StepN T n a b := by
  induction h with
  | refl => exact .refl _
  | cons h₁ _ ih => exact .cons (Step.of_drop h₁) ih

theorem Step.to_drop {c c' : Cfg Q P S} (h : Step T c c') (h' : ∃ q, c'.st = .go q) :
    Step (dropHalt T) c c' := by
  obtain ⟨r, hr, h₁, h₂, rfl⟩ := h
  obtain ⟨q, hq⟩ := h'
  refine ⟨r, mem_dropHalt.mpr ⟨hr, ?_⟩, h₁, h₂, rfl⟩
  simp only [fire] at hq
  rw [hq]; rfl

/-- 実状態の配置で終わる計算過程は、停止規則を使っていない。 -/
theorem StepN.to_drop {n : Nat} {a b : Cfg Q P S} (h : StepN T n a b) (hb : ∃ q, b.st = .go q) :
    StepN (dropHalt T) n a b := by
  induction h with
  | refl => exact .refl _
  | @cons k a₀ a₁ b h₁ h₂ ih =>
    have ha₁ : ∃ q, a₁.st = .go q := by
      cases h₂ with
      | refl => exact hb
      | cons h₃ _ => exact Step.go h₃
    exact .cons (Step.to_drop h₁ ha₁) (ih hb)

theorem StepN.drop_go {n : Nat} {a b : Cfg Q P S} (h : StepN (dropHalt T) n a b)
    (ha : ∃ q, a.st = .go q) : ∃ q, b.st = .go q := by
  cases n with
  | zero => cases h; exact ha
  | succ n =>
    obtain ⟨_, _, r, hr, _, _, rfl⟩ := StepN.last h
    have := (mem_dropHalt.mp hr).2
    simp only [fire]
    cases hq : r.q with
    | go q => exact ⟨q, rfl⟩
    | halt _ => rw [hq] at this; cases this

/-- 疑似状態 h を f h に戻す（実状態はそのまま）。 -/
def unhaltTgt (f : P → Q) : Tgt Q P → Tgt Q P
  | .halt h => .go (f h)
  | .go q => .go q

/-- 停止規則はどれも 0 シフトで読んだ記号をそのまま書き、疑似状態 h へ入る規則の現状態は f h
    （具体機械では `decide` で確かめられるよう、規則ごとの場合分けで書く）。 -/
def HaltRulesId (T : Machine Q P S) (f : P → Q) : Prop :=
  ∀ r ∈ T, r.q.isGo = false → r.d = .Z ∧ r.t = r.s ∧ (Tgt.go r.p : Tgt Q P) = unhaltTgt f r.q

theorem HaltRulesId.get {f : P → Q} (hH : HaltRulesId T f) {r : Rule Q P S} (hr : r ∈ T) {h : P}
    (hq : r.q = .halt h) : r.d = .Z ∧ r.t = r.s ∧ r.p = f h := by
  obtain ⟨hd, ht, hp⟩ := hH r hr (by rw [hq]; rfl)
  rw [hq] at hp
  exact ⟨hd, ht, by injection hp⟩

instance [DecidableEq Q] [DecidableEq P] [DecidableEq S] (T : Machine Q P S) (f : P → Q) :
    Decidable (HaltRulesId T f) := by unfold HaltRulesId; infer_instance

/-! ## 規則の集合が同じ機械 -/

theorem Step.mono {A B : Machine Q P S} (hAB : ∀ r ∈ A, r ∈ B) {c c' : Cfg Q P S} (h : Step A c c') :
    Step B c c' :=
  let ⟨r, hr, h₁, h₂, h₃⟩ := h; ⟨r, hAB r hr, h₁, h₂, h₃⟩

theorem StepN.mono {A B : Machine Q P S} (hAB : ∀ r ∈ A, r ∈ B) {n : Nat} {a b : Cfg Q P S}
    (h : StepN A n a b) : StepN B n a b := by
  induction h with
  | refl => exact .refl _
  | cons h₁ _ ih => exact .cons (Step.mono hAB h₁) ih

/-- 停止規則を持たない機械の、実状態から始まる計算過程の終わりは実状態。 -/
theorem StepN.go_of_allGo (hG : ∀ r ∈ T, r.q.isGo = true) {n : Nat} {a b : Cfg Q P S}
    (h : StepN T n a b) (ha : ∃ q, a.st = .go q) : ∃ q, b.st = .go q :=
  StepN.drop_go (StepN.mono (fun r hr => mem_dropHalt.mpr ⟨hr, hG r hr⟩) h) ha

theorem HaltsIn.congr {A B : Machine Q P S} (h₁ : ∀ r ∈ A, r ∈ B) (h₂ : ∀ r ∈ B, r ∈ A)
    {n : Nat} {a e : Cfg Q P S} (h : HaltsIn A n a e) : HaltsIn B n a e :=
  ⟨StepN.mono h₁ h.1, fun c hc => h.2 c (Step.mono h₂ hc)⟩

theorem Reversible.mono {A B : Machine Q P S} (hAB : ∀ r ∈ A, r ∈ B) (hB : Reversible B) :
    Reversible A := fun r₁ h₁ r₂ h₂ => hB r₁ (hAB r₁ h₁) r₂ (hAB r₂ h₂)

theorem Deterministic.mono {A B : Machine Q P S} (hAB : ∀ r ∈ A, r ∈ B) (hB : Deterministic B) :
    Deterministic A := fun r₁ h₁ r₂ h₂ => hB r₁ (hAB r₁ h₁) r₂ (hAB r₂ h₂)

/-- 大きい機械で止まっている配置は、部分集合の機械でも止まっている。 -/
theorem Halted.mono {A B : Machine Q P S} (hAB : ∀ r ∈ A, r ∈ B) {c : Cfg Q P S} (hB : Halted B c) :
    Halted A c := fun c' h => hB c' (Step.mono hAB h)

/-- 停止規則を 1 回適用した配置は、unhalt で適用前の配置に戻る。 -/
theorem unhalt_fire {f : P → Q} (hH : HaltRulesId T f) {r : Rule Q P S} (hr : r ∈ T) {h : P}
    (hq : r.q = .halt h) {c : Cfg Q P S} (hst : c.st = .go r.p) (hs : c.tape c.pos = r.s) :
    unhalt f (fire r c) = c := by
  obtain ⟨hd, ht, hp⟩ := hH.get hr hq
  obtain ⟨st, pos, tape⟩ := c
  simp only at hst hs
  simp only [unhalt, fire, hq, hd, mv, Int.add_zero, hst, hp]
  congr 1
  funext i
  simp only [upd]
  split
  · subst i; rw [ht, hs]
  · rfl

/-- **停止規則の除去**。T が決定的で、停止規則がどれも「0 シフト・読んだ記号をそのまま書く」なら、
    実状態から始まる T の「停止の 3 項」（停止配置 fin はどれも疑似状態）は、停止配置を unhalt f で
    適用前の配置に戻して dropHalt T に移る。ステップ数の下界は 1 だけ弱くなる（停止規則の 1 ステップ分）。 -/
theorem drop_simulates {f : P → Q} (hD : Deterministic T) (hH : HaltRulesId T f)
    (C : CTSH) (w : List Ch) (a : Cfg Q P S) (ha : ∃ q, a.st = .go q)
    (fin : List Ch → Nat → List Ch → Cfg Q P S) (hfin : ∀ vf mf rm, ∃ h, (fin vf mf rm).st = .halt h)
    (hsim :
      (∀ n vf mf, CHaltsIn C n (w, 0) (vf, mf) → ∃ N rm, n ≤ N ∧ HaltsIn T N a (fin vf mf rm)) ∧
      (∀ N e, HaltsIn T N a e → ∃ n vf mf rm, CHaltsIn C n (w, 0) (vf, mf) ∧ e = fin vf mf rm)) :
    (∀ n vf mf, CHaltsIn C n (w, 0) (vf, mf) →
      ∃ N rm, n ≤ N + 1 ∧ HaltsIn (dropHalt T) N a (unhalt f (fin vf mf rm))) ∧
    (∀ N e, HaltsIn (dropHalt T) N a e →
      ∃ n vf mf rm, CHaltsIn C n (w, 0) (vf, mf) ∧ e = unhalt f (fin vf mf rm)) ∧
    ((∀ n e, ¬ CHaltsIn C n (w, 0) e) ↔ (∀ N e, ¬ HaltsIn (dropHalt T) N a e)) := by
  have fwd : ∀ n vf mf, CHaltsIn C n (w, 0) (vf, mf) →
      ∃ N rm, n ≤ N + 1 ∧ HaltsIn (dropHalt T) N a (unhalt f (fin vf mf rm)) := by
    intro n vf mf hc
    obtain ⟨N, rm, hN, hs, hh⟩ := hsim.1 n vf mf hc
    obtain ⟨h, hfh⟩ := hfin vf mf rm
    cases N with
    | zero => cases hs; obtain ⟨q, hq⟩ := ha; rw [hq] at hfh; cases hfh
    | succ N =>
      obtain ⟨e₀, h₁, r, hr, hst, hsr, he⟩ := StepN.last hs
      have hq : r.q = .halt h := by rw [← hfh, he]; rfl
      have hu : unhalt f (fin vf mf rm) = e₀ := by rw [he]; exact unhalt_fire hH hr hq hst hsr
      refine ⟨N, rm, by omega, ?_, ?_⟩
      · rw [hu]; exact StepN.to_drop h₁ ⟨r.p, hst⟩
      · rw [hu]
        intro c' ⟨r', hr', hst', hsr', _⟩
        have hr'T := (mem_dropHalt.mp hr').1
        have hne : r' ≠ r := by
          rintro rfl; have := (mem_dropHalt.mp hr').2; rw [hq] at this; cases this
        have hp : r'.p = r.p := by rw [hst] at hst'; injection hst' with h'; exact h'.symm
        exact hD r' hr'T r hr hne hp (hsr'.symm.trans hsr)
  have bwd : ∀ N e, HaltsIn (dropHalt T) N a e →
      ∃ n vf mf rm, CHaltsIn C n (w, 0) (vf, mf) ∧ e = unhalt f (fin vf mf rm) := by
    intro N e ⟨hs, hh⟩
    have hsT := StepN.of_drop hs
    have heg := StepN.drop_go hs ha
    by_cases hT : Halted T e
    · obtain ⟨n, vf, mf, rm, hc, rfl⟩ := hsim.2 N e ⟨hsT, hT⟩
      obtain ⟨h, hfh⟩ := hfin vf mf rm
      obtain ⟨q, hq⟩ := heg; rw [hq] at hfh; cases hfh
    · obtain ⟨c', r, hr, hst, hsr, rfl⟩ := exists_step_of_not_halted hT
      cases hq : r.q with
      | go q =>
        exact absurd (Step.to_drop ⟨r, hr, hst, hsr, rfl⟩ ⟨q, by simp [fire, hq]⟩) (hh _)
      | halt h =>
        have hH' : Halted T (fire r e) := by
          intro c'' ⟨r'', _, hst'', _⟩
          simp only [fire, hq] at hst''; cases hst''
        obtain ⟨n, vf, mf, rm, hc, hfe⟩ := hsim.2 (N + 1) (fire r e)
          ⟨hsT.trans (StepN.single ⟨r, hr, hst, hsr, rfl⟩), hH'⟩
        refine ⟨n, vf, mf, rm, hc, ?_⟩
        rw [← hfe]; exact (unhalt_fire hH hr hq hst hsr).symm
  refine ⟨fwd, bwd, ?_⟩
  constructor
  · intro hn N e he
    obtain ⟨n, vf, mf, rm, hc, _⟩ := bwd N e he
    exact hn n _ hc
  · intro hu n ⟨vf, mf⟩ hc
    obtain ⟨N, rm, _, hN⟩ := fwd n vf mf hc
    exact hu N _ hN

/-! ## 大きな表の照合用: 鳩の巣と、鍵の狭義単調増加 -/

/-- 重複の無い l₁ が l₂ に含まれ、l₂ が l₁ より長くないなら、l₂ も l₁ に含まれる。 -/
theorem subset_of_nodup_length {α : Type} [DecidableEq α] :
    ∀ (l₁ l₂ : List α), l₁.Nodup → (∀ x ∈ l₁, x ∈ l₂) → l₂.length ≤ l₁.length → ∀ x ∈ l₂, x ∈ l₁
  | [], l₂, _, _, hl, x, hx => by
    cases l₂ with
    | nil => cases hx
    | cons _ _ => simp at hl
  | a :: t, l₂, hn, hs, hl, x, hx => by
    obtain ⟨ha, ht⟩ := List.nodup_cons.mp hn
    have haL : a ∈ l₂ := hs a (List.mem_cons_self ..)
    have hsub : ∀ y ∈ t, y ∈ l₂.erase a := fun y hy =>
      (List.mem_erase_of_ne (fun (e : y = a) => ha (by rw [← e]; exact hy))).mpr (hs y (List.mem_cons_of_mem _ hy))
    have hlen : (l₂.erase a).length ≤ t.length := by
      rw [List.length_erase_of_mem haL]; simp at hl; omega
    by_cases e : x = a
    · subst e; exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (subset_of_nodup_length t (l₂.erase a) ht hsub hlen x
        ((List.mem_erase_of_ne e).mpr hx))

/-- 隣り合う要素が狭義単調増加か（`decide` 用）。 -/
def incr : List Nat → Bool
  | a :: b :: t => decide (a < b) && incr (b :: t)
  | _ => true

theorem incr_pairwise : ∀ (l : List Nat), incr l = true → l.Pairwise (· < ·)
  | [], _ => .nil
  | [_], _ => .cons (by simp) .nil
  | a :: b :: t, h => by
    simp only [incr, Bool.and_eq_true, decide_eq_true_eq] at h
    have ih := incr_pairwise (b :: t) h.2
    refine .cons ?_ ih
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact h.1
    · exact Nat.lt_trans h.1 (List.rel_of_pairwise_cons ih hc)

/-- 鍵が狭義単調増加なら重複は無い。 -/
theorem nodup_of_incr {α : Type} (key : α → Nat) (l : List α) (h : incr (l.map key) = true) : l.Nodup := by
  have := incr_pairwise _ h
  rw [List.pairwise_map] at this
  exact this.imp (fun hab e => by subst e; exact Nat.lt_irrefl _ hab)

/-- 鍵の列がどれも [lo, hi] に入る。 -/
def InRange (l : List Nat) (lo hi : Nat) : Prop := ∀ a ∈ l, lo ≤ a ∧ a ≤ hi

/-- 2 つの狭義単調増加の列を、範囲が重ならないようにつなぐ。 -/
theorem glue {l₁ l₂ : List Nat} {lo₁ hi₁ lo₂ hi₂ : Nat}
    (p₁ : l₁.Pairwise (· < ·)) (r₁ : InRange l₁ lo₁ hi₁) (p₂ : l₂.Pairwise (· < ·)) (r₂ : InRange l₂ lo₂ hi₂)
    (h : hi₁ < lo₂) (hlo : lo₁ ≤ lo₂) (hhi : hi₁ ≤ hi₂) :
    (l₁ ++ l₂).Pairwise (· < ·) ∧ InRange (l₁ ++ l₂) lo₁ hi₂ := by
  refine ⟨List.pairwise_append.mpr ⟨p₁, p₂, fun a ha b hb => ?_⟩, fun a ha => ?_⟩
  · have := r₁ a ha; have := r₂ b hb; omega
  · rcases List.mem_append.mp ha with ha | ha
    · have := r₁ a ha; omega
    · have := r₂ a ha; omega

theorem inRange_of_all {l : List Nat} {lo hi : Nat} (h : l.all (fun a => decide (lo ≤ a) && decide (a ≤ hi)) = true) :
    InRange l lo hi := by
  intro a ha
  have := List.all_eq_true.mp h a ha
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  exact this

end URTM.SimLemmas
