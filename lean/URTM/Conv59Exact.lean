/-
  Morita 2017, Lemma 5.9 の歩数（C14）。`Conv59.lean` の `step_sim`・`run_sim`・`halts_sim` は T̂ のステップ数を
  `∃ k, … (k + 1)`・`N ≤ M` で隠していたので、その値を式で述べる。n は T̂ の組の数（`encW a n …`）。

  * `step_sim_exact`: T の 1 ステップにつき、T̂ は 1 回の掃引でちょうど 2n + 4 ステップ（δ̂1 から右端の
    δ̂8・δ̂9 まで n + 3 ステップ、q_L で位置 0 へ戻るのに n + 1 ステップ）。T が行き先で止まる最後の 1 ステップでは、
    T̂ は右端の次の空白（位置 n + 1）で止まるまでちょうど n + 1 ステップ。
  * `run_sim_exact`: T が N ステップ進む（途中で止まらない）なら、T̂ はちょうど
    Σ_{i<N} (2(n0 + i) + 4) = N (2 n0 + N + 3) ステップ（掃引ごとに組が 1 つ増える）。
  * `halts_sim_exact`: T が N + 1 ステップで止まるなら、T̂ はちょうど N (2 n0 + N + 3) + (n0 + N + 1) ステップで
    `Conv59.E` の停止配置に止まる。

  証明は `Conv59.step_sim` の連鎖（`prefix_sweep`・ヘッドの組・`sweepR`・δ̂8・δ̂9・`sweepL`）の長さを数えたもの。
  後半の掃引だけは歩数を隠していた `suffix_q`・`suffix_h` を歩数つきで示し直した（`suffix_q_exact`・`suffix_h_exact`）。
  `Conv59.lean` を書き換えずに別ファイルにした理由は `Conv510Exact.lean` と同じ（下流の重い検査を建て直さない）。

  T が最初の配置で止まる場合（N = 0、`Conv59.imm_sim`）の歩数は述べない。

  mathlib 非依存。未証明の穴・新規公理・native_decide を使わない。
-/
import URTM.Conv59

namespace URTM.Conv59

open URTM URTM.KState URTM.CTSH URTM.SimLemmas
open URTM.Conv55 (upd_eq upd_ne upd_upd upd_comm)

variable {Q P S : Type} [DecidableEq Q] [DecidableEq S]

section Exact
variable {T : Machine Q P S} {s0 : S} {ss : List S} {qs qp : List Q}

/-- `suffix_q` の歩数つき版: 位置 i0 から右端の次まで δ̂2 で (n + 1 − i0) ステップ、δ̂8・δ̂9 で 2 ステップ、
    q_L で位置 0 へ n + 1 ステップ。 -/
theorem suffix_q_exact (hS : ∀ s, s ∈ ss) (hQ : ∀ q, q ∈ qs) {a : Int} {n : Nat} {g : Int → S}
    (O F : Int → WSym Q S) (i0 : Int) (h1 : i0 ≤ n + 1)
    (hmid : ∀ j, i0 ≤ j → j < n + 1 →
      O j = .pr (g (a + 2 * j - 2)) (g (a + 2 * j - 1)) ∧ F j = .pr (g (a + 2 * j - 3)) (g (a + 2 * j - 2)))
    (hlast : g (a + 2 * n - 1) = s0) (hFn : F (n + 1) = .pr s0 s0)
    (hOout : ∀ j : Int, (n : Int) + 1 ≤ j → O j = .bl) (hFout : ∀ j : Int, (n : Int) + 2 ≤ j → F j = .bl)
    (hFne : ∀ j : Int, 1 ≤ j → j ≤ (n + 1 : Nat) → F j ≠ .bl) :
    StepN (conv T s0 ss qs qp) ((n + 1 - i0).toNat + (n + 3))
      { st := .go (.q (g (a + 2 * i0 - 3))), pos := i0, tape := mix i0 F O }
      { st := .go .L, pos := 0, tape := F } := by
  have s1 := sweepR (T := T) (s0 := s0) (ss := ss) (qs := qs) (qp := qp) WSt.q (mem_c2 hS) g a F O
    (n + 1 - i0).toNat i0 (fun j h1 h2 => hmid j h1 (by omega))
  rw [show i0 + ((n + 1 - i0).toNat : Int) = n + 1 by omega, show a + 2 * ((n : Int) + 1) - 3 = a + 2 * n - 1 by omega,
    hlast] at s1
  have s2 : Step (conv T s0 ss qs qp) { st := .go (.q s0), pos := (n : Int) + 1, tape := mix (n + 1) F O }
      { st := .go .lam, pos := n + 2, tape := mix (n + 2) F O } := by
    refine ⟨_, mem_c8 hS s0, rfl, ?_, ?_⟩
    · simp only; rw [mix_ge (Int.le_refl _), hOout _ (Int.le_refl _)]
    · simp only [fire, mv]; rw [← hFn, mix_step, show (n : Int) + 1 + 1 = n + 2 by omega]
  have s3 : Step (conv T s0 ss qs qp) { st := .go .lam, pos := (n : Int) + 2, tape := mix (n + 2) F O }
      { st := .go .L, pos := ((n + 1 : Nat) : Int), tape := F } := by
    refine ⟨_, mem_c9, rfl, ?_, ?_⟩
    · simp only; rw [mix_ge (Int.le_refl _), hOout _ (by omega)]
    · simp only [fire, mv]; congr 1
      · push_cast; omega
      · funext i; simp only [upd, mix]
        by_cases h : i = n + 2
        · subst h; rw [if_pos rfl, hFout _ (Int.le_refl _)]
        · rw [if_neg h]; by_cases h' : i < n + 2
          · rw [if_pos h']
          · rw [if_neg h', hOout _ (by omega), hFout _ (by omega)]
  have s4 := sweepL (T := T) (s0 := s0) (qp := qp) hS hQ F (n + 1) hFne
  have := s1.trans ((StepN.single s2).trans ((StepN.single s3).trans s4))
  rwa [show (n + 1 - i0).toNat + (1 + (1 + (n + 1))) = (n + 1 - i0).toNat + (n + 3) by omega] at this

/-- `suffix_h` の歩数つき版: 位置 i0 から右端の次の空白まで δ̂12 で (n + 1 − i0) ステップ。 -/
theorem suffix_h_exact (hS : ∀ s, s ∈ ss) {a : Int} {n : Nat} {g : Int → S}
    (O F : Int → WSym Q S) (i0 : Int) (h1 : i0 ≤ n + 1)
    (hmid : ∀ j, i0 ≤ j → j < n + 1 →
      O j = .pr (g (a + 2 * j - 2)) (g (a + 2 * j - 1)) ∧ F j = .pr (g (a + 2 * j - 3)) (g (a + 2 * j - 2)))
    (hlast : g (a + 2 * n - 1) = s0) :
    StepN (conv T s0 ss qs qp) (n + 1 - i0).toNat
      { st := .go (.h (g (a + 2 * i0 - 3))), pos := i0, tape := mix i0 F O }
      { st := .go (.h s0), pos := n + 1, tape := mix (n + 1) F O } := by
  have s1 := sweepR (T := T) (s0 := s0) (ss := ss) (qs := qs) (qp := qp) WSt.h (mem_c12 hS) g a F O
    (n + 1 - i0).toNat i0 (fun j h1 h2 => hmid j h1 (by omega))
  rw [show i0 + ((n + 1 - i0).toNat : Int) = n + 1 by omega, show a + 2 * ((n : Int) + 1) - 3 = a + 2 * n - 1 by omega,
    hlast] at s1
  exact s1

/-- **Lemma 5.9 の歩数（1 回の掃引）**。T の規則 r = [p, g x, t, d, p'] による c → c'（ヘッドは x' = x ± 1）について、
    T̂ は encW a n c から、c' で T が止まらなければちょうど 2n + 4 ステップで encW (a−1) (n+1) c' へ、
    止まるならちょうど n + 1 ステップで停止配置 haltW (a−1) n c' へ（n は T̂ の組の数）。 -/
theorem step_sim_exact (hS : ∀ s, s ∈ ss) (hQ : ∀ q, q ∈ qs)
    (hqp : ∀ r ∈ T, ∀ p', r.q = .go p' → r.d = .R → p' ∈ qp)
    {a : Int} {n : Nat} {p : Q} {x : Int} {g : Int → S} (hI : Inv s0 a n x g)
    {r : Rule Q P S} (hr : r ∈ T) (hp : r.p = p) (hs : g x = r.s) {p' : Q} (hq : r.q = .go p')
    (x' : Int) (hx' : (r.d = .R ∧ x' = x + 1) ∨ (r.d = .L ∧ x' = x - 1)) :
    (has T p' (upd g x r.t x') = true →
      StepN (conv T s0 ss qs qp) (2 * n + 4) (encW a n p x g) (encW (a - 1) (n + 1) p' x' (upd g x r.t))) ∧
    (has T p' (upd g x r.t x') = false →
      StepN (conv T s0 ss qs qp) (n + 1) (encW a n p x g) (haltW s0 (a - 1) n p' x' (upd g x r.t))) := by
  have hlo := hI.lo; have hhi := hI.hi; have hev := hI.even
  have hx : a + 2 * ((x - a) / 2) = x := by omega
  have hOout : ∀ j : Int, (n : Int) + 1 ≤ j → pack a n p x g j = .bl := fun j h => pack_out (by omega)
  have hOpr : ∀ j : Int, 1 ≤ j → j ≤ n → j ≠ (x - a) / 2 + 1 →
      pack a n p x g j = .pr (g (a + 2 * j - 2)) (g (a + 2 * j - 1)) :=
    fun j h1 h2 h3 => pack_pr' h1 h2 (by omega)
  have hOhp : pack a n p x g ((x - a) / 2 + 1) = .hp p (g x) (g (x + 1)) :=
    pack_hp (by omega) (by omega) (by omega)
  have hFout : ∀ j : Int, (n : Int) + 2 ≤ j → pack (a - 1) (n + 1) p' x' (upd g x r.t) j = .bl :=
    fun j h => pack_out (by push_cast; omega)
  have hF0 : ∀ j : Int, j < 1 → pack (a - 1) (n + 1) p' x' (upd g x r.t) j = .bl :=
    fun j h => pack_out (by omega)
  have hFne : ∀ j : Int, 1 ≤ j → j ≤ ((n + 1 : Nat) : Int) → pack (a - 1) (n + 1) p' x' (upd g x r.t) j ≠ .bl := by
    intro j h1 h2; simp only [pack]; rw [if_pos ⟨h1, h2⟩]; split <;> nofun
  have hFpr : ∀ j : Int, 1 ≤ j → j ≤ (n : Int) + 1 → a + 2 * j - 3 ≠ x' → a + 2 * j - 3 ≠ x →
      a + 2 * j - 2 ≠ x →
      pack (a - 1) (n + 1) p' x' (upd g x r.t) j = .pr (g (a + 2 * j - 3)) (g (a + 2 * j - 2)) := by
    intro j h1 h2 h3 h4 h5
    rw [pack_pr' h1 (by push_cast; omega) (by omega), upd_ne _ _ (by omega), upd_ne _ _ (by omega)]
    congr 2 <;> omega
  have hFn : pack (a - 1) (n + 1) p' x' (upd g x r.t) ((n : Int) + 1) = .pr s0 s0 := by
    rw [hFpr _ (by omega) (Int.le_refl _) (by omega) (by omega) (by omega),
      show a + 2 * ((n : Int) + 1) - 3 = a + 2 * n - 1 by omega, hI.last,
      show a + 2 * ((n : Int) + 1) - 2 = a + 2 * n by omega, hI.out _ (by omega)]
  have hpre := prefix_sweep (T := T) (s0 := s0) (ss := ss) (qs := qs) (qp := qp) hS (p := p) hI
    (pack (a - 1) (n + 1) p' x' (upd g x r.t)) hF0
    (fun j h1 h2 => hFpr j h1 (by omega) (by omega) (by omega) (by omega))
  have hlast := hI.last
  -- 掃引の位置 i0 まで（ちょうど i0 ステップ）来たら、後半は i0 に依らず合計 2n + 4 / n + 1
  have fin : ∀ (i0 : Int), (x - a) / 2 + 2 ≤ i0 → i0 ≤ (n : Int) + 1 →
      (∀ j, i0 ≤ j → j < (n : Int) + 1 →
        pack (a - 1) (n + 1) p' x' (upd g x r.t) j = .pr (g (a + 2 * j - 3)) (g (a + 2 * j - 2))) →
      StepN (conv T s0 ss qs qp) i0.toNat (encW a n p x g)
        { st := .go ((if has T p' (upd g x r.t x') then WSt.q else WSt.h) (g (a + 2 * i0 - 3))),
          pos := i0, tape := mix i0 (pack (a - 1) (n + 1) p' x' (upd g x r.t)) (pack a n p x g) } →
      (has T p' (upd g x r.t x') = true →
        StepN (conv T s0 ss qs qp) (2 * n + 4) (encW a n p x g) (encW (a - 1) (n + 1) p' x' (upd g x r.t))) ∧
      (has T p' (upd g x r.t x') = false →
        StepN (conv T s0 ss qs qp) (n + 1) (encW a n p x g) (haltW s0 (a - 1) n p' x' (upd g x r.t))) := by
    intro i0 hi0 hi1 hF h₀
    have hmid : ∀ j, i0 ≤ j → j < (n : Int) + 1 →
        pack a n p x g j = .pr (g (a + 2 * j - 2)) (g (a + 2 * j - 1)) ∧
        pack (a - 1) (n + 1) p' x' (upd g x r.t) j = .pr (g (a + 2 * j - 3)) (g (a + 2 * j - 2)) :=
      fun j h1 h2 => ⟨hOpr j (by omega) (by omega) (by omega), hF j h1 h2⟩
    refine ⟨fun hh => ?_, fun hh => ?_⟩
    · rw [hh, if_pos rfl] at h₀
      have hk := suffix_q_exact (T := T) (s0 := s0) (ss := ss) (qs := qs) (qp := qp) hS hQ
        (pack a n p x g) _ i0 hi1 hmid hlast hFn hOout hFout hFne
      have := h₀.trans hk
      rwa [show i0.toNat + ((n + 1 - i0).toNat + (n + 3)) = 2 * n + 4 by omega] at this
    · rw [hh, if_neg (by simp)] at h₀
      have hk := suffix_h_exact (T := T) (s0 := s0) (ss := ss) (qs := qs) (qp := qp) hS
        (pack a n p x g) _ i0 hi1 hmid hlast
      have := h₀.trans hk
      rw [show i0.toNat + (n + 1 - i0).toNat = n + 1 by omega] at this
      rw [haltW, ← mix_trunc (pack a n p x g) hOout]; exact this
  rcases hx' with ⟨hdR, hR⟩ | ⟨hdL, hL⟩
  · -- 右へ: δ̂5 → δ̂6/δ̂7
    have s1 : Step (conv T s0 ss qs qp)
        { st := .go (.q (g (x - 1))), pos := (x - a) / 2 + 1,
          tape := mix ((x - a) / 2 + 1) (pack (a - 1) (n + 1) p' x' (upd g x r.t)) (pack a n p x g) }
        { st := .go (.qp p' (g (x + 1))), pos := (x - a) / 2 + 1 + 1,
          tape := mix ((x - a) / 2 + 1 + 1) (pack (a - 1) (n + 1) p' x' (upd g x r.t)) (pack a n p x g) } := by
      have hρ := mem_c35 (s0 := s0) (qs := qs) (qp := qp) hS hr hq (g (x - 1)) (g (x + 1))
      unfold rule35 at hρ
      rw [if_neg (by rw [hdR]; nofun)] at hρ
      refine ⟨_, hρ, rfl, ?_, ?_⟩
      · simp only; rw [mix_ge (Int.le_refl _), hOhp, hp, hs]
      · simp only [fire, mv]
        rw [← mix_step]; congr 2
        rw [pack_pr' (i := (x - a) / 2 + 1) (by omega) (by push_cast; omega) (by omega),
          show a - 1 + 2 * ((x - a) / 2 + 1) - 2 = x - 1 by omega,
          show a - 1 + 2 * ((x - a) / 2 + 1) - 1 = x by omega, upd_ne _ _ (by omega), upd_eq]
    have s2 : Step (conv T s0 ss qs qp)
        { st := .go (.qp p' (g (x + 1))), pos := (x - a) / 2 + 1 + 1,
          tape := mix ((x - a) / 2 + 1 + 1) (pack (a - 1) (n + 1) p' x' (upd g x r.t)) (pack a n p x g) }
        { st := .go ((if has T p' (upd g x r.t x') then WSt.q else WSt.h)
            (g (a + 2 * ((x - a) / 2 + 1 + 1 + 1) - 3))),
          pos := (x - a) / 2 + 1 + 1 + 1,
          tape := mix ((x - a) / 2 + 1 + 1 + 1) (pack (a - 1) (n + 1) p' x' (upd g x r.t))
            (pack a n p x g) } := by
      have hρ := mem_c67 (T := T) (s0 := s0) (qs := qs) hS (hqp r hr p' hq hdR) (g (x + 1)) (g (x + 2))
        (g (x + 3))
      have e1 : upd g x r.t x' = g (x + 1) := by rw [hR, upd_ne _ _ (by omega)]
      have e2 : a + 2 * ((x - a) / 2 + 1 + 1 + 1) - 3 = x + 3 := by omega
      refine ⟨_, hρ, rfl, ?_, ?_⟩
      · simp only; rw [mix_ge (Int.le_refl _), hOpr _ (by omega) (by omega) (by omega)]
        congr 1 <;> congr 1 <;> omega
      · simp only [fire, mv]
        rw [← mix_step, e1, e2]
        congr 1
        · split <;> rfl
        · congr 1
          rw [pack_hp (by omega) (by push_cast; omega) (by omega), hR, upd_ne _ _ (by omega),
            upd_ne _ _ (by omega), show x + 1 + 1 = x + 2 by omega]
    have := hpre.trans ((StepN.single s1).trans (StepN.single s2))
    rw [show 1 + ((x - a) / 2).toNat + (1 + 1) = ((x - a) / 2 + 1 + 1 + 1).toNat by omega] at this
    exact fin ((x - a) / 2 + 1 + 1 + 1) (by omega) (by omega) (fun j h1 h2 =>
      hFpr j (by omega) (by omega) (by omega) (by omega) (by omega)) this
  · -- 左へ: δ̂3/δ̂4
    have e1 : upd g x r.t x' = g (x - 1) := by rw [hL, upd_ne _ _ (by omega)]
    have s1 : Step (conv T s0 ss qs qp)
        { st := .go (.q (g (x - 1))), pos := (x - a) / 2 + 1,
          tape := mix ((x - a) / 2 + 1) (pack (a - 1) (n + 1) p' x' (upd g x r.t)) (pack a n p x g) }
        { st := .go ((if has T p' (upd g x r.t x') then WSt.q else WSt.h)
            (g (a + 2 * ((x - a) / 2 + 1 + 1) - 3))),
          pos := (x - a) / 2 + 1 + 1,
          tape := mix ((x - a) / 2 + 1 + 1) (pack (a - 1) (n + 1) p' x' (upd g x r.t))
            (pack a n p x g) } := by
      have hρ := mem_c35 (s0 := s0) (qs := qs) (qp := qp) hS hr hq (g (x - 1)) (g (x + 1))
      unfold rule35 at hρ
      rw [if_pos hdL] at hρ
      refine ⟨_, hρ, rfl, ?_, ?_⟩
      · simp only; rw [mix_ge (Int.le_refl _), hOhp, hp, hs]
      · simp only [fire, mv]
        rw [← mix_step, e1, show a + 2 * ((x - a) / 2 + 1 + 1) - 3 = x + 1 by omega]
        congr 1
        · split <;> rfl
        · congr 1
          rw [pack_hp (by omega) (by push_cast; omega) (by omega), hL, upd_ne _ _ (by omega),
            show x - 1 + 1 = x by omega, upd_eq]
    have := hpre.trans (StepN.single s1)
    rw [show 1 + ((x - a) / 2).toNat + 1 = ((x - a) / 2 + 1 + 1).toNat by omega] at this
    exact fin ((x - a) / 2 + 1 + 1) (by omega) (by omega) (fun j h1 h2 =>
      hFpr j (by omega) (by omega) (by omega) (by omega) (by omega)) this

theorem sweeps_succ (n0 N : Nat) :
    (N + 1) * (2 * n0 + (N + 1) + 3) = N * (2 * n0 + N + 3) + (2 * (n0 + N) + 4) := by
  rw [Nat.add_mul, Nat.one_mul, show 2 * n0 + (N + 1) + 3 = (2 * n0 + N + 3) + 1 by omega, Nat.mul_add,
    Nat.mul_one]
  omega

/-- **Lemma 5.9 の歩数（計算過程）**: T が c0 から N ステップで c に達し、c で規則が適用できるなら（あるいは N = 0）、
    T̂ は W 0 c0 からちょうど Σ_{i<N} (2(n0 + i) + 4) = N (2 n0 + N + 3) ステップで W N c に達する
    （n0 は最初の組の数。掃引ごとに組が 1 つ増える）。 -/
theorem run_sim_exact (H : Hyp T s0 ss qs qp) {a0 : Int} {n0 : Nat} {c0 : Cfg Q P S} {p0 : Q}
    (hc0 : c0.st = .go p0) (hI : Inv s0 a0 n0 c0.pos c0.tape) :
    ∀ N {c : Cfg Q P S}, StepN T N c0 c → ∀ p, c.st = .go p → (N = 0 ∨ has T p (c.tape c.pos) = true) →
      StepN (conv T s0 ss qs qp) (N * (2 * n0 + N + 3)) (W a0 n0 0 c0) (W a0 n0 N c) := by
  intro N
  induction N with
  | zero =>
    intro c h _ _ _
    cases h
    simpa using StepN.refl (T := conv T s0 ss qs qp) (W a0 n0 0 c0)
  | succ N ih =>
    intro c h p hp hh
    obtain ⟨c₁, h₁, r, hr, hst, hs, rfl⟩ := StepN.last h
    obtain ⟨p₁, hp₁, hI₁⟩ := (run_sim H hc0 hI N h₁).1
    have hgo := (H.hG r hr)
    obtain ⟨p', hq⟩ : ∃ p', r.q = .go p' := by
      cases hq : r.q with
      | go q => exact ⟨q, rfl⟩
      | halt _ => rw [hq] at hgo; cases hgo.1
    have hdir : (r.d = .R ∧ c₁.pos + mv r.d = c₁.pos + 1) ∨ (r.d = .L ∧ c₁.pos + mv r.d = c₁.pos - 1) := by
      cases hd : r.d with
      | L => right; simp [mv]; omega
      | Z => exact absurd hd hgo.2
      | R => left; simp [mv]
    have hr' : r.p = p₁ := by rw [hp₁] at hst; injection hst with h; exact h.symm
    have hp' : p = p' := by simp [fire, hq] at hp; exact hp.symm
    subst hp'
    have hh' : has T p (upd c₁.tape c₁.pos r.t (c₁.pos + mv r.d)) = true := by
      rcases hh with h0 | h0
      · omega
      · simpa [fire] using h0
    have hs₁ := ih h₁ p₁ hp₁ (.inr ((has_iff T p₁ _).mpr ⟨r, hr, hr', hs.symm⟩))
    have hk := (step_sim_exact (s0 := s0) (ss := ss) (qs := qs) (qp := qp) H.hS H.hQ H.hqp hI₁ hr hr' hs hq
      (c₁.pos + mv r.d) hdir).1 hh'
    have hW : W a0 n0 N c₁ = encW (a0 - N) (n0 + N) p₁ c₁.pos c₁.tape := by simp [W, hp₁]
    rw [hW] at hs₁
    have := hs₁.trans hk
    have hW' : W a0 n0 (N + 1) (fire r c₁) =
        encW (a0 - N - 1) (n0 + N + 1) p (c₁.pos + mv r.d) (upd c₁.tape c₁.pos r.t) := by
      simp only [W, fire, hq]
      rw [show a0 - ((N + 1 : Nat) : Int) = a0 - (N : Int) - 1 by push_cast; omega,
        show n0 + (N + 1) = n0 + N + 1 by omega]
    rw [hW', sweeps_succ]; exact this

/-- **Lemma 5.9 の歩数（停止）**: T が c0 から N + 1 ステップで e に止まるなら、T̂ は W 0 c0 から
    ちょうど N (2 n0 + N + 3) + (n0 + N + 1) ステップで停止配置 E (N + 1) e に止まる
    （N 回の完全な掃引と、T が止まったことを検出して右端の次の空白で止まる最後の掃引）。 -/
theorem halts_sim_exact (H : Hyp T s0 ss qs qp) {a0 : Int} {n0 : Nat} {c0 : Cfg Q P S} {p0 : Q}
    (hc0 : c0.st = .go p0) (hI : Inv s0 a0 n0 c0.pos c0.tape) {N : Nat} {e : Cfg Q P S}
    (h : HaltsIn T (N + 1) c0 e) :
    HaltsIn (conv T s0 ss qs qp) (N * (2 * n0 + N + 3) + (n0 + N + 1)) (W a0 n0 0 c0) (E s0 a0 n0 (N + 1) e) := by
  obtain ⟨hs, hh⟩ := h
  have hnot : ∀ p, e.st = .go p → has T p (e.tape e.pos) = false := by
    intro p hp
    cases h' : has T p (e.tape e.pos) with
    | false => rfl
    | true =>
      obtain ⟨r, hr, hrp, hrs⟩ := (has_iff T p _).mp h'
      exact absurd ⟨r, hr, by rw [hp, hrp], hrs.symm, rfl⟩ (hh (fire r e))
  obtain ⟨c₁, h₁, r, hr, hst, hsr, rfl⟩ := StepN.last hs
  obtain ⟨p₁, hp₁, hI₁⟩ := (run_sim H hc0 hI N h₁).1
  have hgo := H.hG r hr
  obtain ⟨p', hq⟩ : ∃ p', r.q = .go p' := by
    cases hq : r.q with
    | go q => exact ⟨q, rfl⟩
    | halt _ => rw [hq] at hgo; cases hgo.1
  have hr' : r.p = p₁ := by rw [hp₁] at hst; injection hst with h; exact h.symm
  have hs₁ := run_sim_exact H hc0 hI N h₁ p₁ hp₁ (.inr ((has_iff T p₁ _).mpr ⟨r, hr, hr', hsr.symm⟩))
  have hne := hnot p' (by simp [fire, hq])
  simp only [fire] at hne
  have hdir : (r.d = .R ∧ c₁.pos + mv r.d = c₁.pos + 1) ∨ (r.d = .L ∧ c₁.pos + mv r.d = c₁.pos - 1) := by
    cases hd : r.d with
    | L => right; simp [mv]; omega
    | Z => exact absurd hd hgo.2
    | R => left; simp [mv]
  have hk := (step_sim_exact (s0 := s0) (ss := ss) (qs := qs) (qp := qp) H.hS H.hQ H.hqp hI₁ hr hr'
    hsr hq (c₁.pos + mv r.d) hdir).2 hne
  refine ⟨?_, ?_⟩
  · have hW : W a0 n0 N c₁ = encW (a0 - N) (n0 + N) p₁ c₁.pos c₁.tape := by simp [W, hp₁]
    rw [hW] at hs₁
    have := hs₁.trans hk
    simp only [E, fire, hq, Nat.add_one_ne_zero, if_false]
    rw [show a0 - ((N + 1 : Nat) : Int) = a0 - (N : Int) - 1 by push_cast; omega,
      show n0 + (N + 1) - 1 = n0 + N by omega]
    exact this
  · simp only [E, fire, hq, Nat.add_one_ne_zero, if_false]
    exact haltW_halted _ _ _ _ _

end Exact

end URTM.Conv59
