/-
  Morita 2017, Theorem 5.4（§5.3.3）: 多記号の可逆 TM T を 2 記号 {0, 1} の TM T̃ に変換する方法の、
  記号数 4（2 ビットの符号。原典 Example 5.7 の形）の場合の一般の模倣証明。

  記号 s の符号 c(s) = c1(s) c2(s)（`code s = (c1, c2)`）。T の配置 a1 ⋯ am q b1 ⋯ bn は
  T̃ の配置 c(a1) ⋯ c(am) [q^r] c(b1) ⋯ c(bn) に対応する（ヘッドは 2 倍の位置、状態は読み込み状態 [q^r]）。
  hsd(q) は状態 q に入る向き（原典 Def. 5.11、ここでは `dir q`）。

      δr : [[p^r], x1, 0, +, [p^r, x1]]
      δt : [[p^r, c1(s)], c2(s), c2(t), −, [q^w, c1(t)]]      （[p, s, t, hsd(q), q] ∈ δ）
      δw : [[q^w, x1], 0, x1, hsd(q), [q^s]]
      δs : [[q^s], x, x, hsd(q), [q^r]]

  原典の δr・δw はすべての (p, x1)・(q, x1) について置くが、記述ファイル urtm138-2.txt は、続く規則の無い
  組（p から c1 = x1 の記号を読む規則が無い δr、c1(t) = x1 を書いて q に入る規則が無い δw）を省いている
  （docs/10 §7.1）。そこで本ファイルの `conv` は**使われうる規則だけ**を並べる: δr と δw を T の規則ごとに作る。
  原典の δ̃ との関係（記述ファイルの表 ⊆ 原典の δ̃）は具体機械で `decide` により確かめる（`convFull`）。

  T が止まる配置 c では、T̃ は enc c で止まるか、δr を 1 回だけ進んで止まる（`pre`）。

  主定理:
  * `step_sim` : T の 1 ステップを T̃ はちょうど 4 ステップで模倣する（原典 Fig. 5.9 の 2 ビット版）。
  * `pre_halted` : T が止まる配置 c では T̃ は enc c から 0 か 1 ステップで `pre c` に達して止まる。
  * `conv_simulates` : 停止の 3 項（CTSH の模倣定理の形）を T̃ に移す（逆向きは T̃ の決定性を仮定）。
  * `conv_det` : 決定性の保存（符号が単射なら）。

  mathlib 非依存。未証明の穴・新規公理・native_decide を使わない。
-/
import URTM.SimLemmas
import URTM.Conv55

namespace URTM.Conv54

open URTM URTM.KState URTM.CTSH URTM.SimLemmas
open URTM.Conv55 (upd_eq upd_ne upd_upd upd_comm upd_self)

/-- T̃ の状態: 読み込み [q^r]、[q^r, x1]、書き込み [q^w, x1]、移動 [q^s]。 -/
inductive BSt (Q : Type) where
  | r (q : Q)
  | r1 (q : Q) (x : Bool)
  | w (q : Q) (x : Bool)
  | s (q : Q)
  deriving DecidableEq, Repr

variable {Q P S : Type}

/-- 規則 1 本から δr・δt・δw を 1 本ずつ（停止規則は変換しない）。 -/
def rRule (code : S → Bool × Bool) (r : Rule Q P S) : Option (Rule (BSt Q) P Bool) :=
  match r.q with
  | .go _ => some ⟨.r r.p, (code r.s).1, false, .R, .go (.r1 r.p (code r.s).1)⟩
  | .halt _ => none
def tRule (code : S → Bool × Bool) (r : Rule Q P S) : Option (Rule (BSt Q) P Bool) :=
  match r.q with
  | .go q => some ⟨.r1 r.p (code r.s).1, (code r.s).2, (code r.t).2, .L, .go (.w q (code r.t).1)⟩
  | .halt _ => none
def wRule (code : S → Bool × Bool) (dir : Q → Dir) (r : Rule Q P S) : Option (Rule (BSt Q) P Bool) :=
  match r.q with
  | .go q => some ⟨.w q (code r.t).1, false, (code r.t).1, dir q, .go (.s q)⟩
  | .halt _ => none
/-- δs（状態 q ごとに 2 本）。 -/
def sRules (dir : Q → Dir) (q : Q) : List (Rule (BSt Q) P Bool) :=
  [⟨.s q, false, false, dir q, .go (.r q)⟩, ⟨.s q, true, true, dir q, .go (.r q)⟩]

/-- **Theorem 5.4 の変換（2 ビット、使われうる規則だけ）**。 -/
def conv (T : Machine Q P S) (code : S → Bool × Bool) (dir : Q → Dir) (qs : List Q) :
    Machine (BSt Q) P Bool :=
  T.filterMap (rRule code) ++ T.filterMap (tRule code) ++ T.filterMap (wRule code dir) ++
    qs.flatMap (sRules dir)

/-- 原典どおりの δ̃（δr・δw をすべての組について置く）。記述ファイルの表との関係を確かめるためだけに使う。 -/
def convFull (T : Machine Q P S) (code : S → Bool × Bool) (dir : Q → Dir) (qs : List Q) :
    Machine (BSt Q) P Bool :=
  qs.flatMap (fun p => [false, true].map (fun x => (⟨.r p, x, false, .R, .go (.r1 p x)⟩ : Rule (BSt Q) P Bool))) ++
  T.filterMap (tRule code) ++
  qs.flatMap (fun q => [false, true].map (fun x => (⟨.w q x, false, x, dir q, .go (.s q)⟩ : Rule (BSt Q) P Bool))) ++
  qs.flatMap (sRules dir)

/-- テープの符号化: マス 2i に c1、2i+1 に c2。 -/
def bits (code : S → Bool × Bool) (g : Int → S) (i : Int) : Bool :=
  if i % 2 = 0 then (code (g (i / 2))).1 else (code (g (i / 2))).2

/-- 配置の符号化。 -/
def enc (code : S → Bool × Bool) (c : Cfg Q P S) : Cfg (BSt Q) P Bool :=
  { st := match c.st with
      | .go p => .go (.r p)
      | .halt h => .halt h,
    pos := 2 * c.pos, tape := bits code c.tape }

/-! ## 1. テープの符号化の補題 -/

theorem bits_even (code : S → Bool × Bool) (g : Int → S) (x : Int) :
    bits code g (2 * x) = (code (g x)).1 := by
  simp only [bits, show (2 * x) % 2 = 0 by omega, if_true, show 2 * x / 2 = x by omega]

theorem bits_odd (code : S → Bool × Bool) (g : Int → S) (x : Int) :
    bits code g (2 * x + 1) = (code (g x)).2 := by
  simp only [bits, show ¬ (2 * x + 1) % 2 = 0 by omega, if_false, show (2 * x + 1) / 2 = x by omega]

theorem bits_upd (code : S → Bool × Bool) (g : Int → S) (x : Int) (t : S) :
    bits code (upd g x t) = upd (upd (bits code g) (2 * x) (code t).1) (2 * x + 1) (code t).2 := by
  funext i
  simp only [bits, upd]
  by_cases h0 : i % 2 = 0
  · have : i ≠ 2 * x + 1 := by omega
    rw [if_pos h0, if_neg this]
    by_cases h1 : i = 2 * x
    · rw [if_pos h1, if_pos (by omega)]
    · rw [if_neg h1, if_neg (by omega), if_pos h0]
  · have : i ≠ 2 * x := by omega
    rw [if_neg h0]
    by_cases h1 : i = 2 * x + 1
    · rw [if_pos h1, if_pos (by omega)]
    · rw [if_neg h1, if_neg this, if_neg (by omega), if_neg h0]

/-! ## 2. 1 ステップの模倣 -/

/-- 規則 r の向きが行き先の向き dir q に等しく、0 シフトでない（`decide` 用の Bool 版）。 -/
def dirOK [DecidableEq Q] (dir : Q → Dir) (r : Rule Q P S) : Bool :=
  match r.q with
  | .go q => r.d == dir q && r.d != .Z
  | .halt _ => true

theorem dirOK_spec [DecidableEq Q] {dir : Q → Dir} {r : Rule Q P S} (h : dirOK dir r = true) {q : Q}
    (hq : r.q = .go q) : r.d = dir q ∧ r.d ≠ .Z := by
  unfold dirOK at h; rw [hq] at h
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h
  exact h

/-- 仮定のまとめ: 状態は qs に列挙され、T は停止規則を持たず、規則の向きは行き先の向き `dir` に等しく
    0 シフトでない。符号は単射。 -/
structure Hyp [DecidableEq Q] (T : Machine Q P S) (code : S → Bool × Bool) (dir : Q → Dir) (qs : List Q) :
    Prop where
  hQ : ∀ q, q ∈ qs
  hG : ∀ r ∈ T, r.q.isGo = true
  hdir : ∀ r ∈ T, dirOK dir r = true
  hinj : ∀ s t, code s = code t → s = t

section Sim
variable [DecidableEq Q] {T : Machine Q P S} {code : S → Bool × Bool} {dir : Q → Dir} {qs : List Q}

omit [DecidableEq Q] in
theorem mem_r {r : Rule Q P S} (hr : r ∈ T) {q : Q} (hq : r.q = .go q) :
    (⟨.r r.p, (code r.s).1, false, .R, .go (.r1 r.p (code r.s).1)⟩ : Rule (BSt Q) P Bool) ∈
      conv T code dir qs := by
  unfold conv
  refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ ?_))
  exact List.mem_filterMap.mpr ⟨r, hr, by simp [rRule, hq]⟩
omit [DecidableEq Q] in
theorem mem_t {r : Rule Q P S} (hr : r ∈ T) {q : Q} (hq : r.q = .go q) :
    (⟨.r1 r.p (code r.s).1, (code r.s).2, (code r.t).2, .L, .go (.w q (code r.t).1)⟩ :
      Rule (BSt Q) P Bool) ∈ conv T code dir qs := by
  unfold conv
  refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ ?_))
  exact List.mem_filterMap.mpr ⟨r, hr, by simp [tRule, hq]⟩
omit [DecidableEq Q] in
theorem mem_w {r : Rule Q P S} (hr : r ∈ T) {q : Q} (hq : r.q = .go q) :
    (⟨.w q (code r.t).1, false, (code r.t).1, dir q, .go (.s q)⟩ : Rule (BSt Q) P Bool) ∈
      conv T code dir qs := by
  unfold conv
  refine List.mem_append_left _ (List.mem_append_right _ ?_)
  exact List.mem_filterMap.mpr ⟨r, hr, by simp [wRule, hq]⟩
omit [DecidableEq Q] in
theorem mem_s (hQ : ∀ q, q ∈ qs) (q : Q) (b : Bool) :
    (⟨.s q, b, b, dir q, .go (.r q)⟩ : Rule (BSt Q) P Bool) ∈ conv T code dir qs := by
  unfold conv
  refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨q, hQ q, ?_⟩)
  cases b <;> simp [sRules]

/-- **1 ステップの模倣**: T の規則 [p, s, t, d, q] による c → c' を、T̃ は enc c からちょうど 4 ステップで enc c' へ。 -/
theorem step_sim (H : Hyp T code dir qs) {c c' : Cfg Q P S} (h : Step T c c') :
    StepN (conv T code dir qs) 4 (enc code c) (enc code c') := by
  obtain ⟨r, hr, hst, hsr, rfl⟩ := h
  obtain ⟨st, x, g⟩ := c
  simp only at hst hsr
  subst hst
  have hG := H.hG r hr
  cases hq : r.q with
  | halt h => rw [hq] at hG; cases hG
  | go q =>
  obtain ⟨hd, hZ⟩ := dirOK_spec (H.hdir r hr) hq
  have hne : 2 * x + 1 ≠ 2 * x := by omega
  -- 1: δr
  have s1 : Step (conv T code dir qs) (enc code ⟨.go r.p, x, g⟩)
      { st := .go (.r1 r.p (code r.s).1), pos := 2 * x + 1, tape := upd (bits code g) (2 * x) false } := by
    refine ⟨_, mem_r hr hq, rfl, ?_, ?_⟩
    · simp only [enc]; rw [bits_even, hsr]
    · simp only [enc, fire, mv]
  -- 2: δt
  have s2 : Step (conv T code dir qs)
      { st := .go (.r1 r.p (code r.s).1), pos := 2 * x + 1, tape := upd (bits code g) (2 * x) false }
      { st := .go (.w q (code r.t).1), pos := 2 * x,
        tape := upd (upd (bits code g) (2 * x) false) (2 * x + 1) (code r.t).2 } := by
    refine ⟨_, mem_t hr hq, rfl, ?_, ?_⟩
    · simp only; rw [upd_ne _ _ hne, bits_odd, hsr]
    · simp only [fire, mv]; congr 1; omega
  -- 3: δw
  have s3 : Step (conv T code dir qs)
      { st := .go (.w q (code r.t).1), pos := 2 * x,
        tape := upd (upd (bits code g) (2 * x) false) (2 * x + 1) (code r.t).2 }
      { st := .go (.s q), pos := 2 * x + mv r.d, tape := bits code (upd g x r.t) } := by
    refine ⟨_, mem_w hr hq, rfl, ?_, ?_⟩
    · simp only; rw [upd_ne _ _ (Ne.symm hne), upd_eq]
    · simp only [fire, hd]
      rw [bits_upd, upd_comm _ _ _ hne, upd_upd, upd_comm _ _ _ (Ne.symm hne)]
  -- 4: δs
  have s4 : Step (conv T code dir qs)
      { st := .go (.s q), pos := 2 * x + mv r.d, tape := bits code (upd g x r.t) }
      (enc code { st := .go q, pos := x + mv r.d, tape := upd g x r.t }) := by
    refine ⟨_, mem_s (P := P) H.hQ q (bits code (upd g x r.t) (2 * x + mv r.d)), rfl, rfl, ?_⟩
    simp only [enc, fire, ← hd]
    congr 1
    · cases r.d <;> simp [mv] <;> omega
    · exact (upd_self _ _).symm
  have := (StepN.single s1).trans ((StepN.single s2).trans ((StepN.single s3).trans (StepN.single s4)))
  simpa [fire, hq] using this

theorem stepN_sim (H : Hyp T code dir qs) {n : Nat} {a b : Cfg Q P S} (h : StepN T n a b) :
    StepN (conv T code dir qs) (4 * n) (enc code a) (enc code b) := by
  induction h with
  | refl => exact .refl _
  | @cons k c₀ c₁ c₂ h₁ _ ih =>
    have := (step_sim H h₁).trans ih
    rwa [show 4 + 4 * k = 4 * (k + 1) by omega] at this

end Sim

/-! ## 3. 停止の対応 -/

section Halt
variable [DecidableEq Q] {T : Machine Q P S} {code : S → Bool × Bool} {dir : Q → Dir} {qs : List Q}

/-- T が止まる配置 c に対応する T̃ の停止配置: c の状態 p から「c1 がヘッドの記号の c1 と等しい記号」を読む
    規則が T にあれば、δr を 1 回進んだ配置（その先の δt が無いので止まる）。無ければ enc c のまま。 -/
def pre (T : Machine Q P S) (code : S → Bool × Bool) (c : Cfg Q P S) : Cfg (BSt Q) P Bool :=
  match c.st with
  | .go p =>
    if T.any (fun r => r.p == p && r.q.isGo && (code r.s).1 == (code (c.tape c.pos)).1) then
      { st := .go (.r1 p (code (c.tape c.pos)).1), pos := 2 * c.pos + 1,
        tape := upd (bits code c.tape) (2 * c.pos) false }
    else enc code c
  | .halt _ => enc code c

omit [DecidableEq Q] in
theorem mem_conv {ρ : Rule (BSt Q) P Bool} (h : ρ ∈ conv T code dir qs) :
    (∃ r ∈ T, ∃ q, r.q = .go q ∧ ρ = ⟨.r r.p, (code r.s).1, false, .R, .go (.r1 r.p (code r.s).1)⟩) ∨
    (∃ r ∈ T, ∃ q, r.q = .go q ∧
      ρ = ⟨.r1 r.p (code r.s).1, (code r.s).2, (code r.t).2, .L, .go (.w q (code r.t).1)⟩) ∨
    (∃ r ∈ T, ∃ q, r.q = .go q ∧ ρ = ⟨.w q (code r.t).1, false, (code r.t).1, dir q, .go (.s q)⟩) ∨
    (∃ q, ∃ b : Bool, ρ = ⟨.s q, b, b, dir q, .go (.r q)⟩) := by
  unfold conv at h
  simp only [List.mem_append] at h
  rcases h with ((h | h) | h) | h
  · obtain ⟨r, hr, e⟩ := List.mem_filterMap.mp h
    unfold rRule at e; split at e
    · rename_i q hq; cases e; exact .inl ⟨r, hr, q, hq, rfl⟩
    · cases e
  · obtain ⟨r, hr, e⟩ := List.mem_filterMap.mp h
    unfold tRule at e; split at e
    · rename_i q hq; cases e; exact .inr (.inl ⟨r, hr, q, hq, rfl⟩)
    · cases e
  · obtain ⟨r, hr, e⟩ := List.mem_filterMap.mp h
    unfold wRule at e; split at e
    · rename_i q hq; cases e; exact .inr (.inr (.inl ⟨r, hr, q, hq, rfl⟩))
    · cases e
  · obtain ⟨q, _, h⟩ := List.mem_flatMap.mp h
    simp only [sRules, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl
    · exact .inr (.inr (.inr ⟨q, false, rfl⟩))
    · exact .inr (.inr (.inr ⟨q, true, rfl⟩))

/-- T が実状態の配置 c で止まるなら、T̃ は enc c から 0 か 1 ステップで pre c に達し、そこで止まる。 -/
theorem pre_halted (H : Hyp T code dir qs) {c : Cfg Q P S} {p : Q} (hc : c.st = .go p)
    (hh : Halted T c) :
    ∃ k, k ≤ 1 ∧ StepN (conv T code dir qs) k (enc code c) (pre T code c) ∧
      Halted (conv T code dir qs) (pre T code c) := by
  obtain ⟨st, x, g⟩ := c
  simp only at hc; subst hc
  by_cases ha : T.any (fun r => r.p == p && r.q.isGo && (code r.s).1 == (code (g x)).1) = true
  · have hpre : pre T code ⟨.go p, x, g⟩ =
        { st := .go (.r1 p (code (g x)).1), pos := 2 * x + 1, tape := upd (bits code g) (2 * x) false } := by
      simp only [pre]; rw [if_pos ha]
    rw [hpre]
    obtain ⟨r, hr, hc⟩ := List.any_eq_true.mp ha
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    obtain ⟨⟨hp, hgo⟩, h1⟩ := hc
    subst hp
    cases hq : r.q with
    | halt _ => rw [hq] at hgo; cases hgo
    | go q =>
    refine ⟨1, Nat.le_refl _, .single ⟨_, mem_r hr hq, rfl, ?_, ?_⟩, ?_⟩
    · simp only [enc]; rw [bits_even, h1]
    · simp only [enc, fire, mv, h1]
    · intro c' ⟨ρ, hρ, hst, hs, _⟩
      have hne : 2 * x + 1 ≠ 2 * x := by omega
      simp only at hst hs
      rw [upd_ne _ _ hne, bits_odd] at hs
      rcases mem_conv hρ with ⟨r', _, q', _, rfl⟩ | ⟨r', hr', q', _, rfl⟩ | ⟨r', _, q', _, rfl⟩ |
        ⟨q', b, rfl⟩
      · cases hst
      · simp only [Tgt.go.injEq, BSt.r1.injEq] at hst
        obtain ⟨hp', h1'⟩ := hst
        have : code (g x) = code r'.s := Prod.ext h1' hs
        exact hh _ ⟨r', hr', hp'.symm ▸ rfl, H.hinj _ _ this, rfl⟩
      · cases hst
      · cases hst
  · have hpre : pre T code ⟨.go p, x, g⟩ = enc code ⟨.go p, x, g⟩ := by
      simp only [pre]; rw [if_neg ha]
    rw [hpre]
    refine ⟨0, Nat.zero_le _, .refl _, ?_⟩
    intro c' ⟨ρ, hρ, hst, hs, _⟩
    simp only [enc] at hst hs
    rw [bits_even] at hs
    rcases mem_conv hρ with ⟨r', hr', q', hq', rfl⟩ | ⟨r', _, q', _, rfl⟩ | ⟨r', _, q', _, rfl⟩ |
      ⟨q', b, rfl⟩
    · simp only [Tgt.go.injEq, BSt.r.injEq] at hst
      apply ha
      refine List.any_eq_true.mpr ⟨r', hr', ?_⟩
      simp [hst, hq', hs, Tgt.isGo]
    · cases hst
    · cases hst
    · cases hst

end Halt

/-! ## 4. 停止の 3 項の移送と決定性の保存 -/

section Main
variable [DecidableEq Q] {T : Machine Q P S} {code : S → Bool × Bool} {dir : Q → Dir} {qs : List Q}

/-- **停止の 3 項の移送**。T の実状態の配置 a から停止の 3 項が成り立つなら、T̃（決定的と仮定）も enc a から、
    停止配置を pre ∘ fin として成り立つ。 -/
theorem conv_simulates (H : Hyp T code dir qs) (hD : Deterministic (conv T code dir qs))
    (C : CTSH) (w : List Ch) (a : Cfg Q P S) (ha : ∃ q, a.st = .go q)
    (fin : List Ch → Nat → List Ch → Cfg Q P S)
    (hsim :
      (∀ n vf mf, CHaltsIn C n (w, 0) (vf, mf) → ∃ N rm, n ≤ N + 1 ∧ HaltsIn T N a (fin vf mf rm)) ∧
      (∀ N e, HaltsIn T N a e → ∃ n vf mf rm, CHaltsIn C n (w, 0) (vf, mf) ∧ e = fin vf mf rm)) :
    (∀ n vf mf, CHaltsIn C n (w, 0) (vf, mf) →
      ∃ N rm, n ≤ N + 1 ∧ HaltsIn (conv T code dir qs) N (enc code a) (pre T code (fin vf mf rm))) ∧
    (∀ N e, HaltsIn (conv T code dir qs) N (enc code a) e →
      ∃ n vf mf rm, CHaltsIn C n (w, 0) (vf, mf) ∧ e = pre T code (fin vf mf rm)) ∧
    ((∀ n e, ¬ CHaltsIn C n (w, 0) e) ↔
      (∀ N e, ¬ HaltsIn (conv T code dir qs) N (enc code a) e)) := by
  refine transfer3 hD (pre T code) (fun N e ⟨hs, hh⟩ => ?_)
    (fun _ N _ hb => ⟨4 * N, by omega, _, stepN_sim H hb⟩) C w fin hsim
  obtain ⟨q, hq⟩ := StepN.go_of_allGo H.hG hs ha
  obtain ⟨k, _, hk, hh'⟩ := pre_halted H hq hh
  exact ⟨4 * N + k, by omega, (stepN_sim H hs).trans hk, hh'⟩

omit [DecidableEq Q] in
/-- **決定性の保存**: T が決定的で符号が単射なら T̃ も決定的。 -/
theorem conv_det (hT : Deterministic T) (hinj : ∀ s t, code s = code t → s = t) :
    Deterministic (conv T code dir qs) := by
  intro ρ₁ h₁ ρ₂ h₂ hne hp hs
  rcases mem_conv h₁ with ⟨r₁, hr₁, q₁, hq₁, rfl⟩ | ⟨r₁, hr₁, q₁, hq₁, rfl⟩ | ⟨r₁, hr₁, q₁, hq₁, rfl⟩ |
      ⟨q₁, b₁, rfl⟩ <;>
    rcases mem_conv h₂ with ⟨r₂, hr₂, q₂, hq₂, rfl⟩ | ⟨r₂, hr₂, q₂, hq₂, rfl⟩ | ⟨r₂, hr₂, q₂, hq₂, rfl⟩ |
      ⟨q₂, b₂, rfl⟩ <;>
    simp only [BSt.r.injEq, BSt.r1.injEq, BSt.w.injEq, BSt.s.injEq, reduceCtorEq] at hp hs
  · exact hne (by rw [hp, hs])
  · obtain ⟨hp, h1⟩ := hp
    have hs' : r₁.s = r₂.s := hinj _ _ (Prod.ext h1 hs)
    by_cases e : r₁ = r₂
    · subst e; rw [hq₁] at hq₂; cases hq₂; exact hne rfl
    · exact hT r₁ hr₁ r₂ hr₂ e hp hs'
  · obtain ⟨hq, h1⟩ := hp
    exact hne (by rw [hq, h1])
  · exact hne (by rw [hp, hs])

end Main

end URTM.Conv54
