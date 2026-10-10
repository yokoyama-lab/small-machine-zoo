/-
  3 状態 2 記号 RTM の停止問題の決定可能性 その 6: **止まるなら有界な歩数で止まる**。**手書き**。

  状態が 0, 1, 2 で記号が 0, 1 の表で、両側の閉包の検査（右側と、鏡像の右側＝左側）が通るなら、
  窓 [a, b] の外が空白の配置から止まる実行は、ヘッドが [a − ML, b + MR] を出ない（`right_bound` と鏡像）。
  その箱の中の配置は有限個なので、鳩の巣から歩数は `bound3` 未満（同じ配置を繰り返せば止まらない）。
  止まる欄の無い表（`noHalt`）は、働く状態からは決して止まらないので 1 歩で決まる。
-/
import URTM.ThreeClosure
import URTM.ThreeEnum

namespace URTM.Three
open URTM URTM.TwoState

/-! ### 鏡像 -/

theorem flipDir_eq : flipDir = flipD := by
  funext d; cases d <;> rfl

theorem mirTbl_eq (tbl : List Quint) : mirTbl tbl = mirT tbl := by
  unfold mirTbl mirT mirQuint; rw [flipDir_eq]

theorem qtr_mir (tbl : List Quint) (c : QConf) (t : Nat) :
    qtr (mirT tbl) (mirQ c) t = mirQ (qtr tbl c t) := by
  unfold qtr; rw [qrun_mir]; cases qrun tbl t c <;> rfl

theorem _root_.URTM.TwoState.QHaltRun.mir {tbl : List Quint} {c : QConf} {T : Nat} (hR : QHaltRun tbl c T) :
    QHaltRun (mirT tbl) (mirQ c) T := by
  refine ⟨?_, ?_⟩
  · rw [qrun_mir]; intro h; apply hR.alive; cases hq : qrun tbl T c <;> simp_all
  · rw [qrun_mir, hR.dead]; rfl

theorem dirConsistent_mir {tbl : List Quint} (h : DirConsistent tbl) : DirConsistent (mirT tbl) := by
  intro r hr r' hr' hq
  obtain ⟨r₀, h₀, rfl⟩ := mem_mirT hr
  obtain ⟨r₀', h₀', rfl⟩ := mem_mirT hr'
  show flipD r₀.d = flipD r₀'.d
  rw [h r₀ h₀ r₀' h₀' hq]

/-- **左側の有界性**（鏡像の右側の有界性）。 -/
theorem left_bound {tbl : List Quint} {c : QConf} {T : Nat} (hR : QHaltRun tbl c T) (hdir : DirConsistent tbl)
    {C : List (List Nat)} {M : Nat} (hC : closedR (mirTbl tbl) C M = true) (a : Int)
    (ha : a ≤ c.pos) (hz : ∀ x, x < a → c.tape x = 0) :
    ∀ t, t ≤ T → a - M ≤ (qtr tbl c t).pos := by
  rw [mirTbl_eq] at hC
  intro t ht
  have := right_bound (c := mirQ c) hR.mir (dirConsistent_mir hdir) hC (-a) (by show -c.pos ≤ -a; omega)
    (fun x hx => by show c.tape (-x) = 0; exact hz (-x) (by omega)) t ht
  rw [qtr_mir] at this
  show a - M ≤ (qtr tbl c t).pos
  have : -(qtr tbl c t).pos ≤ -a + M := this
  omega

/-! ### 鳩の巣 -/

/-- 状態 0, 1, 2 を `Conf2` の向きの欄に詰める（窓の番号づけ `ccode` を使い回すため）。 -/
def stDir (q : Nat) : Dir := if q = 0 then Dir.L else if q = 1 then Dir.Z else Dir.R

theorem stDir_inj {q q' : Nat} (hq : q < 3) (hq' : q' < 3) (h : stDir q = stDir q') : q = q' := by
  unfold stDir at h
  by_cases h0 : q = 0 <;> by_cases h0' : q' = 0 <;> by_cases h1 : q = 1 <;> by_cases h1' : q' = 1 <;>
    simp_all <;> omega

def toC2 (c : QConf) : Conf2 := ⟨c.tape, c.pos, stDir c.st⟩

/-- 止まる実行の歩数の上界。 -/
def bound3 (MR ML : Nat) (a b : Int) : Nat := csize 2 ((b + MR) - (a - ML) + 1).toNat + 1

/-- 働く状態は 0, 1, 2（どの規則もそこから出る）。 -/
def Src3 (tbl : List Quint) : Prop := ∀ r ∈ tbl, r.p < 3

theorem _root_.URTM.TwoState.QHaltRun.st_lt {tbl : List Quint} {c : QConf} {T : Nat} (hR : QHaltRun tbl c T)
    (hsrc : Src3 tbl) (t : Nat) (ht : t < T) : (qtr tbl c t).st < 3 := by
  obtain ⟨r, hr, hf, _⟩ := qstep_some (hR.step t ht)
  obtain ⟨_, hp, _⟩ := find?_spec hf
  rw [← hp]; exact hsrc r hr

/-- **有界停止**: 両側の閉包の検査が通る表は、止まるなら `bound3` 歩以内に止まる。 -/
theorem halts_iff_bound3 {tbl : List Quint} (hsrc : Src3 tbl) (hcl : QClosed tbl 2) (hdir : DirConsistent tbl)
    {CR CL : List (List Nat)} {MR ML : Nat}
    (hRc : closedR tbl CR MR = true) (hLc : closedR (mirTbl tbl) CL ML = true)
    (c : QConf) (a b : Int) (ha : a ≤ c.pos) (hb : c.pos ≤ b)
    (hz : ∀ x, (x < a ∨ b < x) → c.tape x = 0) (h2 : ∀ x, c.tape x < 2) :
    QHalts tbl c ↔ qrun tbl (bound3 MR ML a b) c = none := by
  constructor
  · intro hH
    obtain ⟨T, hR⟩ := qhalts_haltRun hH
    have hr := right_bound hR hdir hRc b hb (fun x hx => hz x (Or.inr hx))
    have hl := left_bound hR hdir hLc a ha (fun x hx => hz x (Or.inl hx))
    obtain ⟨W, hW⟩ : ∃ W : Nat, W = ((b + MR) - (a - ML) + 1).toNat := ⟨_, rfl⟩
    have hWi : (W : Int) = (b + MR) - (a - ML) + 1 := by rw [hW]; omega
    have hinw : ∀ t, t ≤ T → InWin 2 (a - ML) W (toC2 (qtr tbl c t)) := by
      intro t ht
      refine ⟨hl t ht, by have := hr t ht; show (qtr tbl c t).pos < a - ML + W; omega, ?_,
        hR.tape_lt hcl h2 t ht⟩
      intro x hx
      show (qtr tbl c t).tape x = 0
      have := hR.cell_frozen x 0 t (by omega) (fun u _ h2 he => by
        have h1 := hl u (by omega); have h2' := hr u (by omega)
        unfold QP at he; rw [he] at h1 h2'; omega)
      rw [Nat.zero_add] at this
      rw [this]; exact hz x (by omega)
    have hTle : T ≤ csize 2 W := by
      rcases Nat.lt_or_ge (csize 2 W) T with hbig | hok
      · obtain ⟨i, j, hij, hjK, hq⟩ := pigeon (csize 2 W)
          (fun t => ccode 2 (a - ML) W (toC2 (qtr tbl c t))) (fun t ht => ccode_lt (hinw t (by omega)))
        have he := ccode_inj (hinw i (by omega)) (hinw j (by omega)) hq
        exfalso
        apply hR.no_repeat i j hij (by omega)
        have si := hR.st_lt hsrc i (by omega)
        have sj := hR.st_lt hsrc j (by omega)
        unfold toC2 at he
        injection he with h1 h2 h3
        have hst' := stDir_inj si sj h3
        cases hqi : qtr tbl c i
        cases hqj : qtr tbl c j
        rw [hqi, hqj] at h1 h2 hst'
        simp only at h1 h2 hst'
        rw [h1, h2, hst']
      · exact hok
    have := hR.dead
    exact qrun_none_mono tbl c (T + 1) _ this (by unfold bound3; rw [← hW]; omega)
  · intro h; exact ⟨_, h⟩

/-! ### 止まる欄の無い表 -/

/-- 止まる欄が無い表: 状態 0, 1, 2 と記号 0, 1 のどの組にも、状態 0, 1, 2 へ入る規則がある。 -/
def Total3 (tbl : List Quint) : Prop :=
  ∀ p s, p < 3 → s < 2 → ∃ r, find? tbl p s = some r ∧ r.q < 3

theorem never_halts_total {tbl : List Quint} (htot : Total3 tbl) (hcl : QClosed tbl 2) :
    ∀ n (c : QConf), c.st < 3 → (∀ x, c.tape x < 2) → qrun tbl n c ≠ none := by
  intro n
  induction n with
  | zero => intro c _ _; simp [qrun]
  | succ n ih =>
    intro c hst h2
    obtain ⟨r, hf, hq⟩ := htot c.st (c.tape c.pos) hst (h2 _)
    have hs : qstep tbl c = some ⟨r.q, move r.d c.pos, write c.tape c.pos r.t⟩ := by
      unfold qstep; rw [hf]
    rw [qrun_succ_some tbl n hs]
    refine ih _ hq fun x => ?_
    show write c.tape c.pos r.t x < 2
    unfold write; split
    · obtain ⟨hm, _, hrs⟩ := find?_spec hf
      exact hcl r hm (by rw [hrs]; exact h2 _)
    · exact h2 x

theorem halts_iff_total {tbl : List Quint} (hsrc : Src3 tbl) (htot : Total3 tbl) (hcl : QClosed tbl 2)
    (c : QConf) (h2 : ∀ x, c.tape x < 2) (B : Nat) (hB : 1 ≤ B) :
    QHalts tbl c ↔ qrun tbl B c = none := by
  constructor
  · rintro ⟨n, hn⟩
    by_cases hst : c.st < 3
    · exact absurd hn (never_halts_total htot hcl n c hst h2)
    · -- 働かない状態からは規則が無い
      have hs : qstep tbl c = none := by
        unfold qstep
        cases hf : find? tbl c.st (c.tape c.pos) with
        | none => rfl
        | some r =>
          obtain ⟨hm, hp, _⟩ := find?_spec hf
          have := hsrc r hm
          rw [hp] at this; exact absurd this hst
      exact qrun_none_mono tbl c 1 B (qrun_succ_none tbl 0 hs) hB
  · intro h; exact ⟨_, h⟩

end URTM.Three
