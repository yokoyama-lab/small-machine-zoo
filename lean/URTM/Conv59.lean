/-
  Morita 2017, Lemma 5.9（§5.3.5.1）: 零シフト規則の無い可逆 TM T を 1 方向更新の可逆 TM（1WU-RTM）T̂ に
  変換する。その一般の模倣証明。

  T̂ のテープの 1 マスに T の 2 マスを詰める: [s, t]（`pr s t`）、ヘッドを含む組は [[p, s], t]（`hp p s t`）、
  空白 s0（`bl`）。T̂ の状態は q_L（`L`）、q(s)（`q s`）、q(λ)（`lam`）、h(s)（`h s`）、q(p', u)（`qp p' u`）。

      δ̂1  : [q_L, s0, s0, +, q(s0)]
      δ̂2  : [q(s), [t, u], [s, t], +, q(u)]
      δ̂3,4: [q(s), [[p, t], u], [[p', s], t'], +, q(u) / h(u)]   ([p, t, t', −, p'] ∈ δ。T が (p', s) で止まるなら h(u))
      δ̂5  : [q(s), [[p, t], u], [s, t'], +, q(p', u)]            ([p, t, t', +, p'] ∈ δ)
      δ̂6,7: [q(p', u), [s, t], [[p', u], s], +, q(t) / h(t)]     (p' ∈ Q+。T が (p', u) で止まるなら h(t))
      δ̂8  : [q(s), s0, [s, s0], +, q(λ)]       δ̂9 : [q(λ), s0, s0, −, q_L]
      δ̂10 : [q_L, [s, t], [s, t], −, q_L]      δ̂11 : [q_L, [[p, s], t], [[p, s], t], −, q_L]
      δ̂12 : [h(s), [t, u], [s, t], +, h(u)]

  T̂ は位置 0 の空白から右へ 1 回掃くあいだに、T の 1 ステップを模倣しつつ T のテープ全体を 1 マス右へずらし
  （組の区切りが 1 つずれる）、右端に 1 組足し、q_L で位置 0 へ戻る。

  配置の対応 `encW a n c`: T の配置 c（状態 p、ヘッド x、テープ g）に対し、T̂ は q_L で位置 0（空白）を読み、
  位置 i = 1..n に T のマス (a + 2(i−1), a + 2(i−1) + 1) の組を置く（ヘッドの組は [[p, g x], g (x+1)]）。
  不変量 `Inv`: x − a が偶数、ヘッドの組の後にもう 1 組ある、組の外と最後のマスは空白。

  mathlib 非依存。未証明の穴・新規公理・native_decide を使わない。
-/
import URTM.SimLemmas
import URTM.Conv55

namespace URTM.Conv59

open URTM URTM.KState URTM.CTSH URTM.SimLemmas
open URTM.Conv55 (upd_eq upd_ne upd_upd upd_comm)

/-- T̂ の状態。 -/
inductive WSt (Q S : Type) where
  | L
  | q (s : S)
  | lam
  | h (s : S)
  | qp (p : Q) (s : S)
  deriving DecidableEq, Repr

/-- T̂ の記号。 -/
inductive WSym (Q S : Type) where
  | bl
  | pr (s t : S)
  | hp (p : Q) (s t : S)
  deriving DecidableEq, Repr

variable {Q P S : Type} [DecidableEq Q] [DecidableEq S]

/-- T が状態 p で記号 s を読む規則を持つか（持たなければ T はそこで止まる）。 -/
def has (T : Machine Q P S) (p : Q) (s : S) : Bool := T.any (fun r => r.p == p && r.s == s)

/-- δ̂3/δ̂4（r が左移動）または δ̂5（右移動）: 持ち越し s、ヘッドの組の右の記号 u。 -/
def rule35 (T : Machine Q P S) (r : Rule Q P S) (p' : Q) (s u : S) : Rule (WSt Q S) P (WSym Q S) :=
  if r.d = .L then
    ⟨.q s, .hp r.p r.s u, .hp p' s r.t, .R, .go (if has T p' s then .q u else .h u)⟩
  else ⟨.q s, .hp r.p r.s u, .pr s r.t, .R, .go (.qp p' u)⟩

theorem rule35_p (T : Machine Q P S) (r : Rule Q P S) (p' : Q) (s u : S) :
    (rule35 T r p' s u).p = .q s := by unfold rule35; split <;> rfl
theorem rule35_s (T : Machine Q P S) (r : Rule Q P S) (p' : Q) (s u : S) :
    (rule35 T r p' s u).s = .hp r.p r.s u := by unfold rule35; split <;> rfl

/-- T の規則 1 本から δ̂3/δ̂4/δ̂5 を、記号 s, u ごとに。 -/
def ruleRules (T : Machine Q P S) (ss : List S) (r : Rule Q P S) : List (Rule (WSt Q S) P (WSym Q S)) :=
  match r.q with
  | .go p' => ss.flatMap (fun s => ss.map (fun u => rule35 T r p' s u))
  | .halt _ => []

/-- **Lemma 5.9 の変換** T̂。`qp` は Q+ の状態（右移動で入る状態）の列挙、`qs` は T の状態の列挙。 -/
def conv (T : Machine Q P S) (s0 : S) (ss : List S) (qs qp : List Q) : Machine (WSt Q S) P (WSym Q S) :=
  [⟨.L, .bl, .bl, .R, .go (.q s0)⟩] ++
  ss.flatMap (fun s => ss.flatMap (fun t => ss.map (fun u => ⟨.q s, .pr t u, .pr s t, .R, .go (.q u)⟩))) ++
  T.flatMap (ruleRules T ss) ++
  qp.flatMap (fun p' => ss.flatMap (fun u => ss.flatMap (fun s => ss.map (fun t =>
    ⟨.qp p' u, .pr s t, .hp p' u s, .R, .go (if has T p' u then .q t else .h t)⟩)))) ++
  ss.map (fun s => ⟨.q s, .bl, .pr s s0, .R, .go .lam⟩) ++
  [⟨.lam, .bl, .bl, .L, .go .L⟩] ++
  ss.flatMap (fun s => ss.map (fun t => ⟨.L, .pr s t, .pr s t, .L, .go .L⟩)) ++
  qs.flatMap (fun p => ss.flatMap (fun s => ss.map (fun t => ⟨.L, .hp p s t, .hp p s t, .L, .go .L⟩))) ++
  ss.flatMap (fun s => ss.flatMap (fun t => ss.map (fun u => ⟨.h s, .pr t u, .pr s t, .R, .go (.h u)⟩)))

/-- T のテープ g（ヘッド x、状態 p）を、T̂ の位置 1..n に 2 マスずつ詰めたもの（位置 i は T の a + 2(i−1) から）。 -/
def pack (a : Int) (n : Nat) (p : Q) (x : Int) (g : Int → S) (i : Int) : WSym Q S :=
  if 1 ≤ i ∧ i ≤ n then
    if a + 2 * (i - 1) = x then .hp p (g x) (g (x + 1))
    else .pr (g (a + 2 * (i - 1))) (g (a + 2 * (i - 1) + 1))
  else .bl

/-- 掃引の途中のテープ: 位置 cut より左は新しい詰め方 F、cut 以降は古い詰め方 G。 -/
def mix {α : Type} (cut : Int) (F G : Int → α) (i : Int) : α := if i < cut then F i else G i

/-- 掃引の始まり（q_L が位置 0 の空白を読む）の配置。 -/
def encW (a : Int) (n : Nat) (p : Q) (x : Int) (g : Int → S) : Cfg (WSt Q S) P (WSym Q S) :=
  { st := .go .L, pos := 0, tape := pack a n p x g }

/-! ## 1. 詰め方の補題 -/

omit [DecidableEq Q] [DecidableEq S] in
theorem pack_out {a : Int} {n : Nat} {p : Q} {x : Int} {g : Int → S} {i : Int} (h : i < 1 ∨ n < i) :
    pack a n p x g i = .bl := by
  simp only [pack]; rw [if_neg (by omega)]

omit [DecidableEq Q] [DecidableEq S] in
theorem pack_pr {a : Int} {n : Nat} {p : Q} {x : Int} {g : Int → S} {i : Int} (h1 : 1 ≤ i) (h2 : i ≤ n)
    (hx : a + 2 * (i - 1) ≠ x) :
    pack a n p x g i = .pr (g (a + 2 * (i - 1))) (g (a + 2 * (i - 1) + 1)) := by
  simp only [pack]; rw [if_pos ⟨h1, h2⟩, if_neg hx]

omit [DecidableEq Q] [DecidableEq S] in
theorem pack_hp {a : Int} {n : Nat} {p : Q} {x : Int} {g : Int → S} {i : Int} (h1 : 1 ≤ i) (h2 : i ≤ n)
    (hx : a + 2 * (i - 1) = x) : pack a n p x g i = .hp p (g x) (g (x + 1)) := by
  simp only [pack]; rw [if_pos ⟨h1, h2⟩, if_pos hx]

omit [DecidableEq Q] [DecidableEq S] in
theorem mix_lt {α : Type} {cut i : Int} {F G : Int → α} (h : i < cut) : mix cut F G i = F i := by
  simp [mix, h]
omit [DecidableEq Q] [DecidableEq S] in
theorem mix_ge {α : Type} {cut i : Int} {F G : Int → α} (h : cut ≤ i) : mix cut F G i = G i := by
  simp [mix]; omega
omit [DecidableEq Q] [DecidableEq S] in
theorem mix_step {α : Type} (cut : Int) (F G : Int → α) :
    upd (mix cut F G) cut (F cut) = mix (cut + 1) F G := by
  funext i; simp only [upd, mix]
  by_cases h : i = cut
  · subst h; rw [if_pos rfl, if_pos (by omega)]
  · rw [if_neg h]; by_cases h' : i < cut
    · rw [if_pos h', if_pos (by omega)]
    · rw [if_neg h', if_neg (by omega)]

/-! ## 2. 規則の所属と掃引 -/

section Sweep
variable {T : Machine Q P S} {s0 : S} {ss : List S} {qs qp : List Q}

/-- conv の 9 つの部分のどれかに入る規則は conv に入る（リストの結合の位置で）。 -/
theorem mem_c1 : (⟨.L, .bl, .bl, .R, .go (.q s0)⟩ : Rule (WSt Q S) P (WSym Q S)) ∈ conv T s0 ss qs qp := by
  simp [conv]
theorem mem_c2 (hS : ∀ s, s ∈ ss) (s t u : S) :
    (⟨.q s, .pr t u, .pr s t, .R, .go (.q u)⟩ : Rule (WSt Q S) P (WSym Q S)) ∈ conv T s0 ss qs qp := by
  unfold conv; simp only [List.mem_append, List.mem_flatMap, List.mem_map]
  left; left; left; left; left; left; left; right
  exact ⟨s, hS s, t, hS t, u, hS u, rfl⟩
theorem mem_c12 (hS : ∀ s, s ∈ ss) (s t u : S) :
    (⟨.h s, .pr t u, .pr s t, .R, .go (.h u)⟩ : Rule (WSt Q S) P (WSym Q S)) ∈ conv T s0 ss qs qp := by
  unfold conv; simp only [List.mem_append, List.mem_flatMap, List.mem_map]
  right; exact ⟨s, hS s, t, hS t, u, hS u, rfl⟩
theorem mem_c35 (hS : ∀ s, s ∈ ss) {r : Rule Q P S} (hr : r ∈ T) {p' : Q} (hq : r.q = .go p') (s u : S) :
    rule35 T r p' s u ∈ conv T s0 ss qs qp := by
  unfold conv; simp only [List.mem_append, List.mem_flatMap, List.mem_map]
  left; left; left; left; left; left; right
  refine ⟨r, hr, ?_⟩
  simp only [ruleRules, hq, List.mem_flatMap, List.mem_map]
  exact ⟨s, hS s, u, hS u, rfl⟩
theorem mem_c67 (hS : ∀ s, s ∈ ss) {p' : Q} (hp : p' ∈ qp) (u s t : S) :
    (⟨.qp p' u, .pr s t, .hp p' u s, .R, .go (if has T p' u then .q t else .h t)⟩ :
      Rule (WSt Q S) P (WSym Q S)) ∈ conv T s0 ss qs qp := by
  unfold conv; simp only [List.mem_append, List.mem_flatMap, List.mem_map]
  left; left; left; left; left; right
  exact ⟨p', hp, u, hS u, s, hS s, t, hS t, rfl⟩
theorem mem_c8 (hS : ∀ s, s ∈ ss) (s : S) :
    (⟨.q s, .bl, .pr s s0, .R, .go .lam⟩ : Rule (WSt Q S) P (WSym Q S)) ∈ conv T s0 ss qs qp := by
  unfold conv; simp only [List.mem_append, List.mem_flatMap, List.mem_map]
  left; left; left; left; right
  exact ⟨s, hS s, rfl⟩
theorem mem_c9 : (⟨.lam, .bl, .bl, .L, .go .L⟩ : Rule (WSt Q S) P (WSym Q S)) ∈ conv T s0 ss qs qp := by
  unfold conv; simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
  left; left; left; right; trivial
theorem mem_c10 (hS : ∀ s, s ∈ ss) (s t : S) :
    (⟨.L, .pr s t, .pr s t, .L, .go .L⟩ : Rule (WSt Q S) P (WSym Q S)) ∈ conv T s0 ss qs qp := by
  unfold conv; simp only [List.mem_append, List.mem_flatMap, List.mem_map]
  left; left; right
  exact ⟨s, hS s, t, hS t, rfl⟩
theorem mem_c11 (hS : ∀ s, s ∈ ss) (hQ : ∀ q, q ∈ qs) (p : Q) (s t : S) :
    (⟨.L, .hp p s t, .hp p s t, .L, .go .L⟩ : Rule (WSt Q S) P (WSym Q S)) ∈ conv T s0 ss qs qp := by
  unfold conv; simp only [List.mem_append, List.mem_flatMap, List.mem_map]
  left; right
  exact ⟨p, hQ p, s, hS s, t, hS t, rfl⟩

/-- 右への掃引（δ̂2 または δ̂12）: 位置 i から k マス、古い組 [t, u] を [持ち越し, t] に書き換え、u を持ち越す。 -/
theorem sweepR (fq : S → WSt Q S)
    (hf : ∀ s t u : S, (⟨fq s, .pr t u, .pr s t, .R, .go (fq u)⟩ : Rule (WSt Q S) P (WSym Q S)) ∈
      conv T s0 ss qs qp)
    (G : Int → S) (a : Int) (F O : Int → WSym Q S) :
    ∀ (k : Nat) (i : Int), (∀ j, i ≤ j → j < i + k →
      O j = .pr (G (a + 2 * j - 2)) (G (a + 2 * j - 1)) ∧ F j = .pr (G (a + 2 * j - 3)) (G (a + 2 * j - 2))) →
    StepN (conv T s0 ss qs qp) k
      { st := .go (fq (G (a + 2 * i - 3))), pos := i, tape := mix i F O }
      { st := .go (fq (G (a + 2 * (i + k) - 3))), pos := i + k, tape := mix (i + k) F O } := by
  intro k
  induction k with
  | zero => intro i _; rw [show i + ((0 : Nat) : Int) = i by omega]; exact .refl _
  | succ k ih =>
    intro i hj
    obtain ⟨ho, hF⟩ := hj i (Int.le_refl _) (by omega)
    have s1 : Step (conv T s0 ss qs qp)
        { st := .go (fq (G (a + 2 * i - 3))), pos := i, tape := mix i F O }
        { st := .go (fq (G (a + 2 * (i + 1) - 3))), pos := i + 1, tape := mix (i + 1) F O } := by
      refine ⟨_, hf (G (a + 2 * i - 3)) (G (a + 2 * i - 2)) (G (a + 2 * i - 1)), rfl, ?_, ?_⟩
      · simp only; rw [mix_ge (Int.le_refl _), ho]
      · simp only [fire, mv]
        rw [show a + 2 * (i + 1) - 3 = a + 2 * i - 1 by omega, ← hF, mix_step]
    have := ih (i + 1) (fun j h1 h2 => hj j (by omega) (by omega))
    have := (StepN.single s1).trans this
    rw [show 1 + k = k + 1 by omega, show i + 1 + (k : Int) = i + ((k + 1 : Nat) : Int) by omega] at this
    exact this

/-- 左への戻り（δ̂10, δ̂11）: q_L が位置 k から空白でない組を左へ越えて位置 0（空白）まで。 -/
theorem sweepL (hS : ∀ s, s ∈ ss) (hQ : ∀ q, q ∈ qs) (F : Int → WSym Q S) :
    ∀ k : Nat, (∀ j : Int, 1 ≤ j → j ≤ k → F j ≠ .bl) →
    StepN (conv T s0 ss qs qp) k { st := .go .L, pos := k, tape := F } { st := .go .L, pos := 0, tape := F } := by
  intro k
  induction k with
  | zero => intro _; exact .refl _
  | succ k ih =>
    intro hF
    have hne := hF (k + 1) (by omega) (Int.le_refl _)
    have s1 : Step (conv T s0 ss qs qp) { st := .go .L, pos := ((k + 1 : Nat) : Int), tape := F }
        { st := .go .L, pos := k, tape := F } := by
      cases hw : F (k + 1) with
      | bl => exact absurd hw hne
      | pr s t =>
        refine ⟨_, mem_c10 hS s t, rfl, by simp only; push_cast; exact hw, ?_⟩
        simp only [fire, mv]; congr 1
        · push_cast; omega
        · push_cast; rw [← hw, Conv55.upd_self]
      | hp p s t =>
        refine ⟨_, mem_c11 hS hQ p s t, rfl, by simp only; push_cast; exact hw, ?_⟩
        simp only [fire, mv]; congr 1
        · push_cast; omega
        · push_cast; rw [← hw, Conv55.upd_self]
    have := (StepN.single s1).trans (ih (fun j h1 h2 => hF j h1 (by omega)))
    rwa [show 1 + k = k + 1 by omega] at this

end Sweep

/-! ## 3. 1 回の掃引で T の 1 ステップ -/

omit [DecidableEq Q] [DecidableEq S] in
theorem pack_pr' {a : Int} {n : Nat} {p : Q} {x : Int} {g : Int → S} {i : Int} (h1 : 1 ≤ i) (h2 : i ≤ n)
    (hx : a + 2 * i - 2 ≠ x) : pack a n p x g i = .pr (g (a + 2 * i - 2)) (g (a + 2 * i - 1)) := by
  rw [pack_pr h1 h2 (by omega)]; congr 2 <;> omega

/-- 不変量: x − a は偶数、ヘッドの組の後にもう 1 組、組の外と最後のマスは空白。 -/
structure Inv (s0 : S) (a : Int) (n : Nat) (x : Int) (g : Int → S) : Prop where
  even : (x - a) % 2 = 0
  lo : a ≤ x
  hi : x + 4 ≤ a + 2 * n
  out : ∀ j, (j < a ∨ a + 2 * n ≤ j) → g j = s0
  last : g (a + 2 * n - 1) = s0

/-- T が止まったことを検出した掃引の終わり: h(s0) が右端の次の空白を読んで止まる。 -/
def haltW (s0 : S) (a : Int) (n : Nat) (p : Q) (x : Int) (g : Int → S) : Cfg (WSt Q S) P (WSym Q S) :=
  { st := .go (.h s0), pos := n + 1, tape := pack a n p x g }

section Step
variable {T : Machine Q P S} {s0 : S} {ss : List S} {qs qp : List Q}

/-- 掃引の前半: δ̂1 と δ̂2 で位置 1..ih−1 を書き換え、ヘッドの組の位置 ih に q(g (x−1)) で来る。 -/
theorem prefix_sweep (hS : ∀ s, s ∈ ss) {a : Int} {n : Nat} {p : Q} {x : Int} {g : Int → S}
    (hI : Inv s0 a n x g) (F : Int → WSym Q S) (hF0 : ∀ j, j < 1 → F j = .bl)
    (hF : ∀ j, 1 ≤ j → j < (x - a) / 2 + 1 → F j = .pr (g (a + 2 * j - 3)) (g (a + 2 * j - 2))) :
    StepN (conv T s0 ss qs qp) (1 + ((x - a) / 2).toNat) (encW a n p x g)
      { st := .go (.q (g (x - 1))), pos := (x - a) / 2 + 1, tape := mix ((x - a) / 2 + 1) F (pack a n p x g) } := by
  have hlo := hI.lo
  have hhi := hI.hi
  have hev := hI.even
  have hx : a + 2 * ((x - a) / 2) = x := by omega
  have s1 : Step (conv T s0 ss qs qp) (encW a n p x g)
      { st := .go (.q (g (a + 2 * 1 - 3))), pos := 1, tape := mix 1 F (pack a n p x g) } := by
    refine ⟨_, mem_c1, rfl, ?_, ?_⟩
    · simp only [encW]; exact pack_out (by omega)
    · simp only [encW, fire, mv]
      congr 1
      · rw [hI.out (a + 2 * 1 - 3) (by omega)]
      · funext i; simp only [upd, mix]
        by_cases h : i = 0
        · subst h; simp [hF0 0 (by omega)]
        · rw [if_neg h]; by_cases h' : i < 1
          · rw [if_pos h', hF0 i h', pack_out (by omega)]
          · rw [if_neg h']
  have s2 := sweepR (T := T) (s0 := s0) (ss := ss) (qs := qs) (qp := qp) WSt.q (mem_c2 hS) g a F
    (pack a n p x g) ((x - a) / 2).toNat 1 (by
      intro j h1 h2
      refine ⟨pack_pr' h1 (by omega) (by omega), hF j h1 (by omega)⟩)
  have := (StepN.single s1).trans s2
  rw [show (1 : Int) + (((x - a) / 2).toNat : Int) = (x - a) / 2 + 1 by omega,
    show a + 2 * ((x - a) / 2 + 1) - 3 = x - 1 by omega] at this
  exact this

/-- 掃引の後半（q のまま）: 位置 i0..n を δ̂2 で書き換え、δ̂8 で右端に [s0, s0] を足し、δ̂9 で折り返し、
    q_L で位置 0 へ戻る。 -/
theorem suffix_q (hS : ∀ s, s ∈ ss) (hQ : ∀ q, q ∈ qs) {a : Int} {n : Nat} {g : Int → S}
    (O F : Int → WSym Q S) (i0 : Int) (_h0 : 1 ≤ i0) (h1 : i0 ≤ n + 1)
    (hmid : ∀ j, i0 ≤ j → j < n + 1 →
      O j = .pr (g (a + 2 * j - 2)) (g (a + 2 * j - 1)) ∧ F j = .pr (g (a + 2 * j - 3)) (g (a + 2 * j - 2)))
    (hlast : g (a + 2 * n - 1) = s0) (hFn : F (n + 1) = .pr s0 s0)
    (hOout : ∀ j : Int, (n : Int) + 1 ≤ j → O j = .bl) (hFout : ∀ j : Int, (n : Int) + 2 ≤ j → F j = .bl)
    (hFne : ∀ j : Int, 1 ≤ j → j ≤ (n + 1 : Nat) → F j ≠ .bl) (_hF0 : F 0 = .bl) :
    ∃ k, StepN (conv T s0 ss qs qp) (k + 1)
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
  refine ⟨(n + 1 - i0).toNat + 1 + 1 + n, ?_⟩
  have := s1.trans ((StepN.single s2).trans ((StepN.single s3).trans s4))
  rwa [show (n + 1 - i0).toNat + (1 + (1 + (n + 1))) = (n + 1 - i0).toNat + 1 + 1 + n + 1 by omega] at this

/-- 掃引の後半（h、T が止まったことを検出した後）: 位置 i0..n を δ̂12 で書き換え、右端の次の空白で止まる。 -/
theorem suffix_h (hS : ∀ s, s ∈ ss) {a : Int} {n : Nat} {g : Int → S}
    (O F : Int → WSym Q S) (i0 : Int) (h1 : i0 ≤ n + 1)
    (hmid : ∀ j, i0 ≤ j → j < n + 1 →
      O j = .pr (g (a + 2 * j - 2)) (g (a + 2 * j - 1)) ∧ F j = .pr (g (a + 2 * j - 3)) (g (a + 2 * j - 2)))
    (hlast : g (a + 2 * n - 1) = s0) :
    ∃ k, StepN (conv T s0 ss qs qp) k
      { st := .go (.h (g (a + 2 * i0 - 3))), pos := i0, tape := mix i0 F O }
      { st := .go (.h s0), pos := n + 1, tape := mix (n + 1) F O } := by
  have s1 := sweepR (T := T) (s0 := s0) (ss := ss) (qs := qs) (qp := qp) WSt.h (mem_c12 hS) g a F O
    (n + 1 - i0).toNat i0 (fun j h1 h2 => hmid j h1 (by omega))
  rw [show i0 + ((n + 1 - i0).toNat : Int) = n + 1 by omega, show a + 2 * ((n : Int) + 1) - 3 = a + 2 * n - 1 by omega,
    hlast] at s1
  exact ⟨_, s1⟩

end Step

section Step2
variable {T : Machine Q P S} {s0 : S} {ss : List S} {qs qp : List Q}

omit [DecidableEq Q] [DecidableEq S] in
theorem inv_step {a : Int} {n : Nat} {x : Int} {g : Int → S} (hI : Inv s0 a n x g) (t : S) (x' : Int)
    (hx' : x' = x + 1 ∨ x' = x - 1) : Inv s0 (a - 1) (n + 1) x' (upd g x t) := by
  have hlo := hI.lo; have hhi := hI.hi; have hev := hI.even
  refine ⟨by omega, by omega, by push_cast; omega, fun j hj => ?_, ?_⟩
  · rw [upd_ne _ _ (by push_cast at hj; omega)]; exact hI.out j (by push_cast at hj; omega)
  · push_cast
    rw [upd_ne _ _ (by omega)]; exact hI.out _ (by omega)

omit [DecidableEq Q] [DecidableEq S] in
/-- 掃引の途中で止まった配置のテープは、新しい詰め方を n 組で打ち切ったもの。 -/
theorem mix_trunc {a : Int} {n : Nat} {p : Q} {x : Int} {g : Int → S} (O : Int → WSym Q S)
    (hO : ∀ j : Int, (n : Int) + 1 ≤ j → O j = .bl) :
    mix ((n : Int) + 1) (pack a (n + 1) p x g) O = pack a n p x g := by
  funext i; simp only [mix]
  by_cases h : i < (n : Int) + 1
  · rw [if_pos h]; unfold pack
    by_cases h1 : 1 ≤ i
    · have e1 : 1 ≤ i ∧ i ≤ ((n + 1 : Nat) : Int) := ⟨h1, by push_cast; omega⟩
      have e2 : 1 ≤ i ∧ i ≤ (n : Int) := ⟨h1, by omega⟩
      rw [if_pos e1, if_pos e2]
    · rw [if_neg (by omega), if_neg (by omega)]
  · rw [if_neg h, hO i (by omega), pack_out (by omega)]

/-- **1 回の掃引で T の 1 ステップ**。T の規則 r = [p, g x, t, d, p'] による c → c'（ヘッドは x' = x + mv d）について、
    T̂ は encW a n c から 1 ステップ以上で、c' で T が止まらなければ encW (a−1) (n+1) c' へ、止まるなら haltW (a−1) n c' へ。 -/
theorem step_sim (hS : ∀ s, s ∈ ss) (hQ : ∀ q, q ∈ qs)
    (hqp : ∀ r ∈ T, ∀ p', r.q = .go p' → r.d = .R → p' ∈ qp)
    {a : Int} {n : Nat} {p : Q} {x : Int} {g : Int → S} (hI : Inv s0 a n x g)
    {r : Rule Q P S} (hr : r ∈ T) (hp : r.p = p) (hs : g x = r.s) {p' : Q} (hq : r.q = .go p')
    (x' : Int) (hx' : (r.d = .R ∧ x' = x + 1) ∨ (r.d = .L ∧ x' = x - 1)) :
    (has T p' (upd g x r.t x') = true →
      ∃ k, StepN (conv T s0 ss qs qp) (k + 1) (encW a n p x g) (encW (a - 1) (n + 1) p' x' (upd g x r.t))) ∧
    (has T p' (upd g x r.t x') = false →
      ∃ k, StepN (conv T s0 ss qs qp) (k + 1) (encW a n p x g) (haltW s0 (a - 1) n p' x' (upd g x r.t))) := by
  have hlo := hI.lo; have hhi := hI.hi; have hev := hI.even
  have hx : a + 2 * ((x - a) / 2) = x := by omega
  have hxx : x' = x + 1 ∨ x' = x - 1 := by rcases hx' with ⟨_, h⟩ | ⟨_, h⟩ <;> simp [h]
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
  have fin : ∀ (i0 : Int), (x - a) / 2 + 2 ≤ i0 → i0 ≤ (n : Int) + 1 →
      (∀ j, i0 ≤ j → j < (n : Int) + 1 →
        pack (a - 1) (n + 1) p' x' (upd g x r.t) j = .pr (g (a + 2 * j - 3)) (g (a + 2 * j - 2))) →
      ∀ k₀, StepN (conv T s0 ss qs qp) (k₀ + 1) (encW a n p x g)
        { st := .go ((if has T p' (upd g x r.t x') then WSt.q else WSt.h) (g (a + 2 * i0 - 3))),
          pos := i0, tape := mix i0 (pack (a - 1) (n + 1) p' x' (upd g x r.t)) (pack a n p x g) } →
      (has T p' (upd g x r.t x') = true →
        ∃ k, StepN (conv T s0 ss qs qp) (k + 1) (encW a n p x g) (encW (a - 1) (n + 1) p' x' (upd g x r.t))) ∧
      (has T p' (upd g x r.t x') = false →
        ∃ k, StepN (conv T s0 ss qs qp) (k + 1) (encW a n p x g) (haltW s0 (a - 1) n p' x' (upd g x r.t))) := by
    intro i0 hi0 hi1 hF k₀ h₀
    have hmid : ∀ j, i0 ≤ j → j < (n : Int) + 1 →
        pack a n p x g j = .pr (g (a + 2 * j - 2)) (g (a + 2 * j - 1)) ∧
        pack (a - 1) (n + 1) p' x' (upd g x r.t) j = .pr (g (a + 2 * j - 3)) (g (a + 2 * j - 2)) :=
      fun j h1 h2 => ⟨hOpr j (by omega) (by omega) (by omega), hF j h1 h2⟩
    refine ⟨fun hh => ?_, fun hh => ?_⟩
    · rw [hh, if_pos rfl] at h₀
      obtain ⟨k, hk⟩ := suffix_q (T := T) (s0 := s0) (ss := ss) (qs := qs) (qp := qp) hS hQ
        (pack a n p x g) _ i0 (by omega) hi1 hmid hlast hFn hOout hFout hFne (hF0 0 (by omega))
      exact ⟨k₀ + 1 + k, by have := h₀.trans hk; rwa [show k₀ + 1 + (k + 1) = k₀ + 1 + k + 1 by omega] at this⟩
    · rw [hh, if_neg (by simp)] at h₀
      obtain ⟨k, hk⟩ := suffix_h (T := T) (s0 := s0) (ss := ss) (qs := qs) (qp := qp) hS
        (pack a n p x g) _ i0 hi1 hmid hlast
      refine ⟨k₀ + k, ?_⟩
      have := h₀.trans hk
      rw [show k₀ + 1 + k = k₀ + k + 1 by omega] at this
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
    refine fin ((x - a) / 2 + 1 + 1 + 1) (by omega) (by omega) (fun j h1 h2 =>
      hFpr j (by omega) (by omega) (by omega) (by omega) (by omega)) (((x - a) / 2).toNat + 2) ?_
    rwa [show 1 + ((x - a) / 2).toNat + (1 + 1) = ((x - a) / 2).toNat + 2 + 1 by omega] at this
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
    refine fin ((x - a) / 2 + 1 + 1) (by omega) (by omega) (fun j h1 h2 =>
      hFpr j (by omega) (by omega) (by omega) (by omega) (by omega)) (((x - a) / 2).toNat + 1) ?_
    rwa [show 1 + ((x - a) / 2).toNat + 1 = ((x - a) / 2).toNat + 1 + 1 by omega] at this

end Step2

/-! ## 4. 規則の分類、停止、決定性 -/

section Spec
variable {T : Machine Q P S} {s0 : S} {ss : List S} {qs qp : List Q}

theorem mem_conv {ρ : Rule (WSt Q S) P (WSym Q S)} (h : ρ ∈ conv T s0 ss qs qp) :
    ρ = ⟨.L, .bl, .bl, .R, .go (.q s0)⟩ ∨
    (∃ s t u, ρ = ⟨.q s, .pr t u, .pr s t, .R, .go (.q u)⟩) ∨
    (∃ r ∈ T, ∃ p', r.q = .go p' ∧ ∃ s u, ρ = rule35 T r p' s u) ∨
    (∃ p' u s t, ρ = ⟨.qp p' u, .pr s t, .hp p' u s, .R, .go (if has T p' u then .q t else .h t)⟩) ∨
    (∃ s, ρ = ⟨.q s, .bl, .pr s s0, .R, .go .lam⟩) ∨
    ρ = ⟨.lam, .bl, .bl, .L, .go .L⟩ ∨
    (∃ s t, ρ = ⟨.L, .pr s t, .pr s t, .L, .go .L⟩) ∨
    (∃ p s t, ρ = ⟨.L, .hp p s t, .hp p s t, .L, .go .L⟩) ∨
    (∃ s t u, ρ = ⟨.h s, .pr t u, .pr s t, .R, .go (.h u)⟩) := by
  unfold conv at h
  simp only [List.mem_append, List.mem_flatMap, List.mem_map, List.mem_cons, List.not_mem_nil,
    or_false] at h
  rcases h with (((((((h | ⟨s, _, t, _, u, _, h⟩) | ⟨r, hr, h⟩) | ⟨p', _, u, _, s, _, t, _, h⟩) | ⟨s, _, h⟩) | h) |
    ⟨s, _, t, _, h⟩) | ⟨p, _, s, _, t, _, h⟩) | ⟨s, _, t, _, u, _, h⟩
  · exact .inl h
  · exact .inr (.inl ⟨s, t, u, h.symm⟩)
  · simp only [ruleRules] at h
    split at h
    · rename_i p' hq
      simp only [List.mem_flatMap, List.mem_map] at h
      obtain ⟨s, _, u, _, h⟩ := h
      exact .inr (.inr (.inl ⟨r, hr, p', hq, s, u, h.symm⟩))
    · simp at h
  · exact .inr (.inr (.inr (.inl ⟨p', u, s, t, h.symm⟩)))
  · exact .inr (.inr (.inr (.inr (.inl ⟨s, h.symm⟩))))
  · exact .inr (.inr (.inr (.inr (.inr (.inl h)))))
  · exact .inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨s, t, h.symm⟩))))))
  · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨p, s, t, h.symm⟩)))))))
  · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr ⟨s, t, u, h.symm⟩)))))))

/-- 掃引の終わりに h(s0) で止まった配置は止まっている。 -/
theorem haltW_halted (a : Int) (n : Nat) (p : Q) (x : Int) (g : Int → S) :
    Halted (conv T s0 ss qs qp) (haltW s0 a n p x g) := by
  intro c' ⟨ρ, hρ, hst, hs, _⟩
  simp only [haltW] at hst hs
  rw [pack_out (by omega)] at hs
  rcases mem_conv hρ with rfl | ⟨_, _, _, rfl⟩ | ⟨r, _, p', _, _, _, rfl⟩ | ⟨_, _, _, _, rfl⟩ | ⟨_, rfl⟩ | rfl |
    ⟨_, _, rfl⟩ | ⟨_, _, _, rfl⟩ | ⟨_, _, _, rfl⟩
  · cases hst
  · cases hs
  · rw [rule35_s] at hs; cases hs
  · cases hs
  · cases hst
  · cases hst
  · cases hs
  · cases hs
  · cases hs

theorem has_iff (T : Machine Q P S) (p : Q) (s : S) : has T p s = true ↔ ∃ r ∈ T, r.p = p ∧ r.s = s := by
  simp [has, List.any_eq_true]

/-- T が最初の配置で止まる場合: T̂ は前半の掃引でヘッドの組まで来て、そこで止まる。 -/
def immW (a : Int) (n : Nat) (p : Q) (x : Int) (g : Int → S) : Cfg (WSt Q S) P (WSym Q S) :=
  { st := .go (.q (g (x - 1))), pos := (x - a) / 2 + 1,
    tape := mix ((x - a) / 2 + 1) (pack (a - 1) n p x g) (pack a n p x g) }

theorem imm_sim (hS : ∀ s, s ∈ ss) {a : Int} {n : Nat} {p : Q} {x : Int} {g : Int → S} (hI : Inv s0 a n x g)
    (hh : has T p (g x) = false) :
    ∃ k, StepN (conv T s0 ss qs qp) k (encW a n p x g) (immW a n p x g) ∧
      Halted (conv T s0 ss qs qp) (immW a n p x g) := by
  have hlo := hI.lo; have hhi := hI.hi; have hev := hI.even
  refine ⟨_, prefix_sweep (T := T) (s0 := s0) (ss := ss) (qs := qs) (qp := qp) hS (p := p) hI _
    (fun j h => pack_out (by omega)) (fun j h1 h2 => ?_), ?_⟩
  · rw [pack_pr' h1 (by omega) (by omega)]; congr 2 <;> omega
  · intro c' ⟨ρ, hρ, hst, hs, _⟩
    simp only [immW] at hst hs
    rw [mix_ge (Int.le_refl _), pack_hp (by omega) (by omega) (by omega)] at hs
    rcases mem_conv hρ with rfl | ⟨_, _, _, rfl⟩ | ⟨r, hr, p', _, _, _, rfl⟩ | ⟨_, _, _, _, rfl⟩ | ⟨_, rfl⟩ | rfl |
      ⟨_, _, rfl⟩ | ⟨_, _, _, rfl⟩ | ⟨_, _, _, rfl⟩
    · cases hst
    · cases hs
    · rw [rule35_s] at hs
      simp only [WSym.hp.injEq] at hs
      have : has T p (g x) = true := (has_iff T p (g x)).mpr ⟨r, hr, hs.1.symm, hs.2.1.symm⟩
      rw [hh] at this; cases this
    · cases hst
    · cases hs
    · cases hst
    · cases hst
    · cases hst
    · cases hst

/-- **決定性の保存**: T が決定的なら T̂ も決定的。 -/
theorem conv_det (hT : Deterministic T) : Deterministic (conv T s0 ss qs qp) := by
  intro ρ₁ h₁ ρ₂ h₂ hne hp hs
  rcases mem_conv h₁ with rfl | ⟨a₁, b₁, c₁, rfl⟩ | ⟨r₁, hr₁, p₁, hq₁, s₁, u₁, rfl⟩ | ⟨a₁, b₁, c₁, d₁, rfl⟩ |
    ⟨a₁, rfl⟩ | rfl | ⟨a₁, b₁, rfl⟩ | ⟨a₁, b₁, c₁, rfl⟩ | ⟨a₁, b₁, c₁, rfl⟩ <;>
  rcases mem_conv h₂ with rfl | ⟨a₂, b₂, c₂, rfl⟩ | ⟨r₂, hr₂, p₂, hq₂, s₂, u₂, rfl⟩ | ⟨a₂, b₂, c₂, d₂, rfl⟩ |
    ⟨a₂, rfl⟩ | rfl | ⟨a₂, b₂, rfl⟩ | ⟨a₂, b₂, c₂, rfl⟩ | ⟨a₂, b₂, c₂, rfl⟩ <;>
  simp only [rule35_p, rule35_s] at hp hs <;>
  first
  | exact hne rfl
  | (cases hp; done)
  | (cases hs; done)
  | skip
  -- 残りは同じ族どうし
  all_goals first
    | (simp only [WSt.q.injEq, WSt.h.injEq, WSt.qp.injEq, WSym.pr.injEq, WSym.hp.injEq] at hp hs
       first
       | (obtain ⟨rfl, rfl⟩ := hs; subst hp; exact hne rfl)
       | (obtain ⟨rfl, rfl⟩ := hp; obtain ⟨rfl, rfl⟩ := hs; exact hne rfl)
       | (obtain ⟨rfl, rfl, rfl⟩ := hs; exact hne rfl)
       | (subst hp; obtain ⟨hp', hs', rfl⟩ := hs
          have e : r₁ = r₂ := Classical.byContradiction fun e => hT r₁ hr₁ r₂ hr₂ e hp' hs'
          subst e; rw [hq₁] at hq₂; cases hq₂; exact hne rfl))

end Spec

/-! ## 5. 計算過程の模倣と停止の 3 項の移送 -/

section Run
variable {T : Machine Q P S} {s0 : S} {ss : List S} {qs qp : List Q}

/-- 仮定のまとめ。 -/
structure Hyp (T : Machine Q P S) (s0 : S) (ss : List S) (qs qp : List Q) : Prop where
  hS : ∀ s, s ∈ ss
  hQ : ∀ q, q ∈ qs
  /-- 規則はどれも実状態へ入り、左右どちらかへ動く（停止規則・0 シフトが無い）。 -/
  hG : ∀ r ∈ T, r.q.isGo = true ∧ r.d ≠ .Z
  /-- 右移動で入る状態は qp に列挙されている（原典の Q+）。 -/
  hqp : ∀ r ∈ T, ∀ p', r.q = .go p' → r.d = .R → p' ∈ qp

/-- T の配置 c を、k 回掃いた後の T̂ の配置に（組の始まり a0 − k、組の数 n0 + k）。 -/
def W (a0 : Int) (n0 : Nat) (k : Nat) (c : Cfg Q P S) : Cfg (WSt Q S) P (WSym Q S) :=
  match c.st with
  | .go p => encW (a0 - k) (n0 + k) p c.pos c.tape
  | .halt h => { st := .halt h, pos := 0, tape := fun _ => .bl }

/-- T が N ステップで止まった配置 e に対応する T̂ の停止配置（N = 0 なら前半の掃引の途中、そうでなければ h(s0)）。 -/
def E (s0 : S) (a0 : Int) (n0 : Nat) (N : Nat) (e : Cfg Q P S) : Cfg (WSt Q S) P (WSym Q S) :=
  match e.st with
  | .go p => if N = 0 then immW a0 n0 p e.pos e.tape else haltW s0 (a0 - N) (n0 + N - 1) p e.pos e.tape
  | .halt h => { st := .halt h, pos := 0, tape := fun _ => .bl }

/-- **計算過程の模倣**: T が c0 から N ステップで c に達し、c で規則が適用できるなら（あるいは N = 0）、
    T̂ は W 0 c0 から N ステップ以上で W N c に達し、不変量も保たれる。 -/
theorem run_sim (H : Hyp T s0 ss qs qp) {a0 : Int} {n0 : Nat} {c0 : Cfg Q P S} {p0 : Q} (hc0 : c0.st = .go p0)
    (hI : Inv s0 a0 n0 c0.pos c0.tape) :
    ∀ N {c : Cfg Q P S}, StepN T N c0 c →
      (∃ p, c.st = .go p ∧ Inv s0 (a0 - N) (n0 + N) c.pos c.tape) ∧
      (∀ p, c.st = .go p → (N = 0 ∨ has T p (c.tape c.pos) = true) →
        ∃ M, N ≤ M ∧ StepN (conv T s0 ss qs qp) M (W a0 n0 0 c0) (W a0 n0 N c)) := by
  intro N
  induction N with
  | zero =>
    intro c h
    cases h
    refine ⟨⟨p0, hc0, by simpa using hI⟩, fun p hp _ => ⟨0, Nat.le_refl _, ?_⟩⟩
    exact .refl _
  | succ N ih =>
    intro c h
    obtain ⟨c₁, h₁, r, hr, hst, hs, rfl⟩ := StepN.last h
    obtain ⟨⟨p₁, hp₁, hI₁⟩, hrun⟩ := ih h₁
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
    have hI' : Inv s0 (a0 - ((N + 1 : Nat) : Int)) (n0 + (N + 1)) (c₁.pos + mv r.d) (upd c₁.tape c₁.pos r.t) := by
      have := inv_step hI₁ r.t (c₁.pos + mv r.d) (by rcases hdir with ⟨_, h⟩ | ⟨_, h⟩ <;> simp [h])
      push_cast; rwa [show a0 - (N : Int) - 1 = a0 - ((N : Int) + 1) by omega,
        show n0 + N + 1 = n0 + (N + 1) by omega] at this
    have hr' : r.p = p₁ := by rw [hp₁] at hst; injection hst with h; exact h.symm
    refine ⟨⟨p', by simp [fire, hq], by simpa [fire] using hI'⟩, fun p hp hh => ?_⟩
    have hp' : p = p' := by simp [fire, hq] at hp; exact hp.symm
    subst hp'
    have hh' : has T p (upd c₁.tape c₁.pos r.t (c₁.pos + mv r.d)) = true := by
      rcases hh with h0 | h0
      · omega
      · simpa [fire] using h0
    obtain ⟨M₁, hM₁, hs₁⟩ := hrun p₁ hp₁ (.inr ((has_iff T p₁ _).mpr ⟨r, hr, hr', hs.symm⟩))
    have hstep := (step_sim (s0 := s0) (ss := ss) (qs := qs) (qp := qp) H.hS H.hQ H.hqp hI₁ hr hr' hs hq
      (c₁.pos + mv r.d) hdir).1 hh'
    obtain ⟨k, hk⟩ := hstep
    refine ⟨M₁ + (k + 1), by omega, ?_⟩
    have hW : W a0 n0 N c₁ = encW (a0 - N) (n0 + N) p₁ c₁.pos c₁.tape := by simp [W, hp₁]
    rw [hW] at hs₁
    have := hs₁.trans hk
    have hW' : W a0 n0 (N + 1) (fire r c₁) =
        encW (a0 - N - 1) (n0 + N + 1) p (c₁.pos + mv r.d) (upd c₁.tape c₁.pos r.t) := by
      simp only [W, fire, hq]
      rw [show a0 - ((N + 1 : Nat) : Int) = a0 - (N : Int) - 1 by push_cast; omega,
        show n0 + (N + 1) = n0 + N + 1 by omega]
    rw [hW']; exact this

/-- T が N ステップで止まるなら、T̂ も止まり、停止配置は E N e。 -/
theorem halts_sim (H : Hyp T s0 ss qs qp) {a0 : Int} {n0 : Nat} {c0 : Cfg Q P S} {p0 : Q} (hc0 : c0.st = .go p0)
    (hI : Inv s0 a0 n0 c0.pos c0.tape) {N : Nat} {e : Cfg Q P S} (h : HaltsIn T N c0 e) :
    ∃ M, N ≤ M ∧ HaltsIn (conv T s0 ss qs qp) M (W a0 n0 0 c0) (E s0 a0 n0 N e) := by
  obtain ⟨hs, hh⟩ := h
  have hnot : ∀ p, e.st = .go p → has T p (e.tape e.pos) = false := by
    intro p hp
    cases h' : has T p (e.tape e.pos) with
    | false => rfl
    | true =>
      obtain ⟨r, hr, hrp, hrs⟩ := (has_iff T p _).mp h'
      exact absurd ⟨r, hr, by rw [hp, hrp], hrs.symm, rfl⟩ (hh (fire r e))
  cases N with
  | zero =>
    cases hs
    have hh0 := hnot p0 hc0
    obtain ⟨k, hk, hH⟩ := imm_sim (T := T) (s0 := s0) (qs := qs) (qp := qp) H.hS hI hh0
    have hW : W a0 n0 0 c0 = encW a0 n0 p0 c0.pos c0.tape := by simp [W, hc0]
    have hE : E s0 a0 n0 0 c0 = immW a0 n0 p0 c0.pos c0.tape := by simp [E, hc0]
    refine ⟨k, Nat.zero_le _, ?_, ?_⟩
    · rw [hW, hE]; exact hk
    · rw [hE]; exact hH
  | succ N =>
    obtain ⟨c₁, h₁, r, hr, hst, hsr, rfl⟩ := StepN.last hs
    obtain ⟨⟨p₁, hp₁, hI₁⟩, hrun⟩ := run_sim H hc0 hI N h₁
    have hgo := H.hG r hr
    obtain ⟨p', hq⟩ : ∃ p', r.q = .go p' := by
      cases hq : r.q with
      | go q => exact ⟨q, rfl⟩
      | halt _ => rw [hq] at hgo; cases hgo.1
    have hr' : r.p = p₁ := by rw [hp₁] at hst; injection hst with h; exact h.symm
    obtain ⟨M₁, hM₁, hs₁⟩ := hrun p₁ hp₁ (.inr ((has_iff T p₁ _).mpr ⟨r, hr, hr', hsr.symm⟩))
    have hne := hnot p' (by simp [fire, hq])
    simp only [fire] at hne
    have hdir : (r.d = .R ∧ c₁.pos + mv r.d = c₁.pos + 1) ∨ (r.d = .L ∧ c₁.pos + mv r.d = c₁.pos - 1) := by
      cases hd : r.d with
      | L => right; simp [mv]; omega
      | Z => exact absurd hd hgo.2
      | R => left; simp [mv]
    obtain ⟨k, hk⟩ := (step_sim (s0 := s0) (ss := ss) (qs := qs) (qp := qp) H.hS H.hQ H.hqp hI₁ hr hr'
      hsr hq (c₁.pos + mv r.d) hdir).2 hne
    refine ⟨M₁ + (k + 1), by omega, ?_, ?_⟩
    · have hW : W a0 n0 N c₁ = encW (a0 - N) (n0 + N) p₁ c₁.pos c₁.tape := by simp [W, hp₁]
      rw [hW] at hs₁
      have := hs₁.trans hk
      simp only [E, fire, hq, Nat.add_one_ne_zero, if_false]
      rw [show a0 - ((N + 1 : Nat) : Int) = a0 - (N : Int) - 1 by push_cast; omega,
        show n0 + (N + 1) - 1 = n0 + N by omega]
      exact this
    · simp only [E, fire, hq, Nat.add_one_ne_zero, if_false]
      exact haltW_halted _ _ _ _ _

/-- **停止の 3 項の移送**（Conv510.conv_simulates に渡す形）。T̂ は決定的と仮定。停止配置は T のステップ数 N に依る。 -/
theorem conv_simulates {α : Type} (H : Hyp T s0 ss qs qp) (hD : Deterministic (conv T s0 ss qs qp))
    {a0 : Int} {n0 : Nat} (Halts : α → Prop) (a : Cfg Q P S) {p0 : Q} (ha : a.st = .go p0)
    (hI : Inv s0 a0 n0 a.pos a.tape) (fin : α → Cfg Q P S)
    (hsim :
      (∀ x, Halts x → ∃ N, HaltsIn T N a (fin x)) ∧
      (∀ N e, HaltsIn T N a e → ∃ x, Halts x ∧ e = fin x)) :
    (∀ y : α × Nat, (Halts y.1 ∧ ∃ N', HaltsIn T y.2 a (fin y.1) ∧ N' = y.2) →
      ∃ M, HaltsIn (conv T s0 ss qs qp) M (W a0 n0 0 a) (E s0 a0 n0 y.2 (fin y.1))) ∧
    (∀ M e, HaltsIn (conv T s0 ss qs qp) M (W a0 n0 0 a) e →
      ∃ y : α × Nat, (Halts y.1 ∧ ∃ N', HaltsIn T y.2 a (fin y.1) ∧ N' = y.2) ∧
        e = E s0 a0 n0 y.2 (fin y.1)) := by
  have run : (∀ n e, ¬ HaltsIn T n a e) → ∀ N b, StepN T N a b →
      ∃ M, N ≤ M ∧ ∃ b', StepN (conv T s0 ss qs qp) M (W a0 n0 0 a) b' := by
    intro hn N b hb
    obtain ⟨⟨p, hp, _⟩, hrun⟩ := run_sim H ha hI N hb
    have hhas : has T p (b.tape b.pos) = true := by
      cases hc : has T p (b.tape b.pos) with
      | true => rfl
      | false =>
        refine absurd ⟨hb, fun c' ⟨r, hr, hst, hs, _⟩ => ?_⟩ (hn _ _)
        have := (has_iff T p _).mpr ⟨r, hr, by rw [hp] at hst; injection hst with h; exact h.symm, hs.symm⟩
        rw [hc] at this; cases this
    obtain ⟨M', hM', hs⟩ := hrun p hp (.inr hhas)
    exact ⟨M', hM', _, hs⟩
  refine ⟨fun ⟨x, N⟩ ⟨_, _, hN, _⟩ => ?_, fun M e he => ?_⟩
  · obtain ⟨M, _, hM⟩ := halts_sim H ha hI hN
    exact ⟨M, hM⟩
  · obtain ⟨n, e₀, h₀, rfl⟩ := back_of_fwd hD (E s0 a0 n0)
      (fun _ _ h => let ⟨M, _, hM⟩ := halts_sim H ha hI h; ⟨M, hM⟩) run M e he
    obtain ⟨x, hx, rfl⟩ := hsim.2 n e₀ h₀
    exact ⟨(x, n), ⟨hx, n, h₀, rfl⟩, rfl⟩

end Run

/-! ## 6. 規則の引き当て -/

section Lookup
variable {T : Machine Q P S} {s0 : S} {ss : List S} {qs qp : List Q}

/-- T̂ の規則を (状態, 記号) から引く。 -/
def hatLookup (T : Machine Q P S) (s0 : S) (qp : List Q) : WSt Q S → WSym Q S → Option (Rule (WSt Q S) P (WSym Q S))
  | .L, .bl => some ⟨.L, .bl, .bl, .R, .go (.q s0)⟩
  | .L, .pr s t => some ⟨.L, .pr s t, .pr s t, .L, .go .L⟩
  | .L, .hp p s t => some ⟨.L, .hp p s t, .hp p s t, .L, .go .L⟩
  | .q s, .pr t u => some ⟨.q s, .pr t u, .pr s t, .R, .go (.q u)⟩
  | .q s, .hp p t u =>
    match T.find? (fun r => r.p == p && r.s == t) with
    | some r => match r.q with
      | .go p' => some (rule35 T r p' s u)
      | .halt _ => none
    | none => none
  | .q s, .bl => some ⟨.q s, .bl, .pr s s0, .R, .go .lam⟩
  | .lam, .bl => some ⟨.lam, .bl, .bl, .L, .go .L⟩
  | .h s, .pr t u => some ⟨.h s, .pr t u, .pr s t, .R, .go (.h u)⟩
  | .qp p' u, .pr s t =>
    if p' ∈ qp then some ⟨.qp p' u, .pr s t, .hp p' u s, .R, .go (if has T p' u then .q t else .h t)⟩ else none
  | _, _ => none

theorem hatLookup_sound (hS : ∀ s, s ∈ ss) (hQ : ∀ q, q ∈ qs) {p : WSt Q S} {w : WSym Q S}
    {ρ : Rule (WSt Q S) P (WSym Q S)} (h : hatLookup T s0 qp p w = some ρ) : ρ ∈ conv T s0 ss qs qp := by
  match p, w with
  | .L, .bl => simp only [hatLookup] at h; cases h; exact mem_c1
  | .L, .pr s t => simp only [hatLookup] at h; cases h; exact mem_c10 hS s t
  | .L, .hp p s t => simp only [hatLookup] at h; cases h; exact mem_c11 hS hQ p s t
  | .q s, .pr t u => simp only [hatLookup] at h; cases h; exact mem_c2 hS s t u
  | .q s, .hp p t u =>
    simp only [hatLookup] at h
    split at h
    · rename_i r hr
      split at h
      · rename_i p' hq
        cases h
        exact mem_c35 hS (List.mem_of_find?_eq_some hr) hq s u
      · cases h
    · cases h
  | .q s, .bl => simp only [hatLookup] at h; cases h; exact mem_c8 hS s
  | .lam, .bl => simp only [hatLookup] at h; cases h; exact mem_c9
  | .h s, .pr t u => simp only [hatLookup] at h; cases h; exact mem_c12 hS s t u
  | .qp p' u, .pr s t =>
    simp only [hatLookup] at h
    split at h
    · cases h; rename_i hp; exact mem_c67 hS hp u s t
    · cases h
  | .lam, .pr _ _ => simp [hatLookup] at h
  | .lam, .hp _ _ _ => simp [hatLookup] at h
  | .h _, .bl => simp [hatLookup] at h
  | .h _, .hp _ _ _ => simp [hatLookup] at h
  | .qp _ _, .bl => simp [hatLookup] at h
  | .qp _ _, .hp _ _ _ => simp [hatLookup] at h

end Lookup

end URTM.Conv59
