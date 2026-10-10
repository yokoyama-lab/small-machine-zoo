/-
  2 状態 RTM の停止問題の決定可能性 その 4: セルの時計と、半直線の中での停止の上界。**手書き**。

    * `clock` : **セルの時計**。セル x（出発時のヘッドより右）の i 回目の訪問時の
      (向き, 記号) は、(R, 初期記号) から写像 `clk π`（規則を当てて向きを反転）を i 回
      当てたもの。訪問の合間はセルに触れず、去った側から戻るしかないことによる
      （nonexistence.md の補題 C「各セルは固定時計」の機械証明）
    * `inside_halt_bound` : 空白半直線 [k,∞) の中で停止するなら、[k,∞) への入場は
      2·nsym + 1 回以下（すべての空白セルは同じ時計を持ち、それが未定義に当たるので、
      先頭セル k の訪問回数は鳩の巣で抑えられる）
-/
import URTM.TSDDepth
import URTM.Pigeon

namespace URTM.TwoState

/-- 向きの反転。 -/
def flipD : Dir → Dir
  | Dir.L => Dir.R
  | Dir.Z => Dir.Z
  | Dir.R => Dir.L

/-- 時計の 1 歩: 訪問時の (向き, 記号) から次の訪問時の (向き, 記号) へ。 -/
def clk (π : Rule) (q : Dir × Nat) : Option (Dir × Nat) :=
  (π q.1 q.2).map (fun r => (flipD r.2, r.1))

/-- 部分関数の軌道。 -/
def oorb {α : Type} (G : α → Option α) (a : α) : Nat → Option α
  | 0 => some a
  | n + 1 => (oorb G a n).bind G

theorem oorb_none_mono {α : Type} (G : α → Option α) (a : α) :
    ∀ (n m : Nat), oorb G a n = none → oorb G a (n + m) = none := by
  intro n m
  induction m with
  | zero => intro h; exact h
  | succ m ih =>
    intro h
    show (oorb G a (n + m)).bind G = none
    rw [ih h]; rfl

theorem oorb_shift_eq {α : Type} (G : α → Option α) (a : α) (i j : Nat)
    (h : oorb G a i = oorb G a j) : ∀ r, oorb G a (i + r) = oorb G a (j + r) := by
  intro r
  induction r with
  | zero => exact h
  | succ r ih =>
    show (oorb G a (i + r)).bind G = (oorb G a (j + r)).bind G
    rw [ih]

/-- 軌道が一度重複し、そこまで定義されていれば、以後ずっと定義されている。 -/
theorem oorb_total_of_repeat {α : Type} (G : α → Option α) (a : α) (i j : Nat) (hij : i < j)
    (h : oorb G a i = oorb G a j) (hdef : ∀ m, m ≤ j → oorb G a m ≠ none) :
    ∀ m, oorb G a m ≠ none := by
  intro m
  induction m using Nat.strongRecOn with
  | _ m ih =>
    by_cases hm : m ≤ j
    · exact hdef m hm
    · have e1 : m = j + (m - j) := by omega
      have e2 := oorb_shift_eq G a i j h (m - j)
      rw [e1, ← e2]
      exact ih (i + (m - j)) (by omega)

/-- 記号が有界で規則が閉じている。 -/
def Closed (π : Rule) (nsym : Nat) : Prop :=
  ∀ d s v d', s < nsym → π d s = some (v, d') → v < nsym

section Clock
variable {π : Rule} {c : Conf2} {T : Nat}

/-- 時刻 t までのセル x の訪問回数。 -/
def Vis (π : Rule) (c : Conf2) (x : Int) : Nat → Nat
  | 0 => 0
  | t + 1 => Vis π c x t + if P π c t = x then 1 else 0

theorem Vis_succ_of (π : Rule) (c : Conf2) (x : Int) (t : Nat) (h : P π c t = x) :
    Vis π c x (t + 1) = Vis π c x t + 1 := by simp [Vis, h]

theorem Vis_succ_not (π : Rule) (c : Conf2) (x : Int) (t : Nat) (h : ¬ P π c t = x) :
    Vis π c x (t + 1) = Vis π c x t := by simp [Vis, h]

theorem Vis_const (π : Rule) (c : Conf2) (x : Int) :
    ∀ (t n : Nat), (∀ u, t ≤ u → u < t + n → P π c u ≠ x) → Vis π c x (t + n) = Vis π c x t := by
  intro t n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro h
    have e : t + (n + 1) = (t + n) + 1 := by omega
    rw [e, Vis_succ_not π c x _ (h (t + n) (by omega) (by omega))]
    exact ih (fun u h1 h2 => h u h1 (by omega))

theorem Vis_mono (π : Rule) (c : Conf2) (x : Int) :
    ∀ (t n : Nat), Vis π c x t ≤ Vis π c x (t + n) := by
  intro t n
  induction n with
  | zero => exact Nat.le_refl _
  | succ n ih =>
    have e : t + (n + 1) = (t + n) + 1 := by omega
    rw [e]
    by_cases h : P π c (t + n) = x
    · rw [Vis_succ_of π c x _ h]; omega
    · rw [Vis_succ_not π c x _ h]; exact ih

/-- セル x に来ない間、ヘッドは x の同じ側に留まる。 -/
theorem HaltRun.same_side (hZ : NoZ π) (hR : HaltRun π c T) (x : Int) :
    ∀ (t₁ n : Nat), t₁ + n ≤ T → (∀ u, t₁ ≤ u → u ≤ t₁ + n → P π c u ≠ x) →
      (P π c t₁ < x → P π c (t₁ + n) < x) ∧ (x < P π c t₁ → x < P π c (t₁ + n)) := by
  intro t₁ n
  induction n with
  | zero => intro _ _; exact ⟨id, id⟩
  | succ n ih =>
    intro h hne
    obtain ⟨ih1, ih2⟩ := ih (by omega) (fun u h1 h2 => hne u h1 (by omega))
    have hm := hR.move1 hZ (t₁ + n) (by omega)
    have hn1 := hne (t₁ + n + 1) (by omega) (by omega)
    have e : t₁ + (n + 1) = t₁ + n + 1 := by omega
    rw [e]
    constructor
    · intro hlt; have := ih1 hlt; omega
    · intro hgt; have := ih2 hgt; omega

/-- **セルの時計**。 -/
theorem HaltRun.clock (hZ : NoZ π) (hR : HaltRun π c T) (x : Int) (hx : c.pos < x) :
    ∀ (N t : Nat), t < N → t ≤ T → P π c t = x →
      oorb (clk π) (Dir.R, c.tape x) (Vis π c x t) = some ((tr π c t).dir, (tr π c t).tape x) := by
  intro N
  induction N with
  | zero => intro t ht; omega
  | succ N ih =>
    intro t htN htT hPt
    have ht0 : 0 < t := by
      rcases Nat.eq_zero_or_pos t with h | h
      · rw [h] at hPt; exact absurd hPt (by show c.pos ≠ x; omega)
      · exact h
    by_cases hv : Vis π c x t = 0
    · -- 最初の訪問: 左から来る。セルはまだ触られていない
      rw [hv]
      have hnv : ∀ u, u < t → P π c u ≠ x := by
        intro u hu he
        have := Vis_mono π c x (u + 1) (t - (u + 1))
        rw [show u + 1 + (t - (u + 1)) = t by omega, Vis_succ_of π c x u he] at this
        omega
      have hside := (hR.same_side hZ x 0 (t - 1) (by omega)
        (fun u _ h2 => hnv u (by omega))).1 (by show c.pos < x; exact hx)
      rw [show 0 + (t - 1) = t - 1 by omega] at hside
      obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
      rw [show t' + 1 - 1 = t' by omega] at hside
      rcases hR.stepMove hZ t' (by omega) with ⟨hp, hd⟩ | ⟨hp, hd⟩
      · have htape := hR.cell_frozen x 0 (t' + 1) (by omega) (fun u _ h2 => hnv u (by omega))
        rw [Nat.zero_add] at htape
        rw [hd, htape]; rfl
      · omega
    · -- 直前の訪問 t'
      obtain ⟨u₀, hu₀a, hu₀b, hu₀c⟩ : ∃ u, u < t ∧ P π c u = x ∧ True := by
        refine Classical.byContradiction fun hn => hv ?_
        have := Vis_const π c x 0 t (fun u _ h2 he => hn ⟨u, by omega, he, trivial⟩)
        rw [Nat.zero_add] at this; rw [this]; rfl
      obtain ⟨t', ht'a, ht'b, ht'c, ht'd⟩ :=
        exists_last (fun u => P π c u = x) (t - 1 - u₀) u₀ hu₀b
      have ht't : t' < t := by omega
      have hnv : ∀ u, t' < u → u < t → P π c u ≠ x := fun u h1 h2 => ht'd u h1 (by omega)
      have IH := ih t' (by omega) (by omega) ht'c
      have hVis : Vis π c x t = Vis π c x t' + 1 := by
        have e : t = (t' + 1) + (t - (t' + 1)) := by omega
        rw [e, Vis_const π c x (t' + 1) _ (fun u h1 h2 => hnv u (by omega) (by omega)),
          Vis_succ_of π c x t' ht'c]
      rw [hVis]
      show (oorb (clk π) (Dir.R, c.tape x) (Vis π c x t')).bind (clk π) = _
      rw [IH]
      -- 1 歩目の中身
      have hst := hR.step t' (by omega)
      obtain ⟨v, d', hr, htp, hps, hdr⟩ := step2_some π hst
      have hread : (tr π c t').tape (tr π c t').pos = (tr π c t').tape x := by
        show (tr π c t').tape (P π c t') = _; rw [ht'c]
      rw [hread] at hr
      have hne1 : t' + 1 ≠ t := by
        intro h
        have := hR.move1 hZ t' (by omega)
        rw [h] at this; omega
      have htape : (tr π c t).tape x = v := by
        have e : t = (t' + 1) + (t - (t' + 1)) := by omega
        rw [e, hR.cell_frozen x (t' + 1) (t - (t' + 1)) (by omega)
          (fun u h1 h2 => hnv u (by omega) (by omega)), htp]
        show write (tr π c t').tape (tr π c t').pos v x = v
        rw [show (tr π c t').pos = x from ht'c]; exact write_at _ _ _
      have hz := hZ _ _ _ _ hr
      show (clk π ((tr π c t').dir, (tr π c t').tape x)) = _
      simp only [clk, hr, Option.map]
      rw [htape]
      -- 戻ってくる向き
      have hside := hR.same_side hZ x (t' + 1) (t - 1 - (t' + 1)) (by omega)
        (fun u h1 h2 => hnv u (by omega) (by omega))
      rw [show t' + 1 + (t - 1 - (t' + 1)) = t - 1 by omega] at hside
      obtain ⟨tm, htm⟩ : ∃ tm, t = tm + 1 := ⟨t - 1, by omega⟩
      rw [htm, show tm + 1 - 1 = tm by omega] at hside
      rw [htm] at hPt ⊢
      cases d' with
      | Z => exact absurd rfl hz
      | R =>
        have hp1 : P π c (t' + 1) = x + 1 := by show (tr π c (t' + 1)).pos = _; rw [hps, ← ht'c]; rfl
        have := hside.2 (by omega)
        rcases hR.stepMove hZ tm (by omega) with ⟨hp, hd⟩ | ⟨hp, hd⟩
        · omega
        · rw [hd]; rfl
      | L =>
        have hp1 : P π c (t' + 1) = x - 1 := by show (tr π c (t' + 1)).pos = _; rw [hps, ← ht'c]; rfl
        have := hside.1 (by omega)
        rcases hR.stepMove hZ tm (by omega) with ⟨hp, hd⟩ | ⟨hp, hd⟩
        · rw [hd]; rfl
        · omega

/-! ## 記号の有界性と、半直線の中での停止の上界 -/

theorem HaltRun.tape_lt (hR : HaltRun π c T) {nsym : Nat} (hcl : Closed π nsym)
    (hinit : ∀ x, c.tape x < nsym) : ∀ t, t ≤ T → ∀ x, (tr π c t).tape x < nsym := by
  intro t
  induction t with
  | zero => intro _ x; exact hinit x
  | succ t ih =>
    intro ht x
    obtain ⟨v, d', hr, htp, _, _⟩ := step2_some π (hR.step t (by omega))
    rw [htp]
    by_cases hx : x = (tr π c t).pos
    · rw [hx, write_at]
      exact hcl _ _ _ _ (ih (by omega) _) hr
    · rw [write_off _ _ _ hx]; exact ih (by omega) x

/-- 時計の状態の番号（向きは L か R）。 -/
def qcode (q : Dir × Nat) : Nat := 2 * q.2 + (match q.1 with | Dir.R => 1 | _ => 0)

def QValid (nsym : Nat) (q : Dir × Nat) : Prop := q.1 ≠ Dir.Z ∧ q.2 < nsym

theorem qcode_lt {nsym : Nat} {q : Dir × Nat} (h : QValid nsym q) : qcode q < 2 * nsym := by
  obtain ⟨d, s⟩ := q
  obtain ⟨_, hs⟩ := h
  cases d <;> simp [qcode] at * <;> omega

theorem qcode_inj {nsym : Nat} {q₁ q₂ : Dir × Nat} (h₁ : QValid nsym q₁) (h₂ : QValid nsym q₂)
    (h : qcode q₁ = qcode q₂) : q₁ = q₂ := by
  obtain ⟨d₁, s₁⟩ := q₁
  obtain ⟨d₂, s₂⟩ := q₂
  obtain ⟨hz₁, _⟩ := h₁
  obtain ⟨hz₂, _⟩ := h₂
  cases d₁ <;> cases d₂ <;> simp [qcode] at h hz₁ hz₂ ⊢ <;> omega

theorem oorb_valid {π : Rule} (hZ : NoZ π) {nsym : Nat} (hcl : Closed π nsym) (q₀ : Dir × Nat)
    (h₀ : QValid nsym q₀) : ∀ m q, oorb (clk π) q₀ m = some q → QValid nsym q := by
  intro m
  induction m with
  | zero => intro q h; have : q₀ = q := Option.some.inj h; rw [← this]; exact h₀
  | succ m ih =>
    intro q h
    show QValid nsym q
    change (oorb (clk π) q₀ m).bind (clk π) = some q at h
    cases hm : oorb (clk π) q₀ m with
    | none => rw [hm] at h; exact absurd h (by simp)
    | some p =>
      rw [hm] at h
      have hp := ih p hm
      change (π p.1 p.2).map (fun r => (flipD r.2, r.1)) = some q at h
      cases hr : π p.1 p.2 with
      | none => rw [hr] at h; exact absurd h (by simp)
      | some r =>
        rw [hr] at h
        have hq : (flipD r.2, r.1) = q := Option.some.inj h
        rw [← hq]
        obtain ⟨v, d'⟩ := r
        refine ⟨?_, hcl _ _ _ _ hp.2 hr⟩
        have := hZ _ _ _ _ hr
        cases d' <;> simp [flipD] at this ⊢

theorem Ent_le_Vis (π : Rule) (c : Conf2) (k : Int) :
    ∀ t, Ent π c k t ≤ Vis π c k (t + 1) := by
  intro t
  induction t with
  | zero => exact Nat.zero_le _
  | succ t ih =>
    by_cases hE : EntStep π c k t
    · rw [Ent_succ_of π c k t hE, Vis_succ_of π c k (t + 1) hE.2]; omega
    · rw [Ent_succ_not π c k t hE]
      have := Vis_mono π c k (t + 1) 1; omega

/-- **半直線の中で停止するなら、入場は 2·nsym + 1 回以下**。 -/
theorem HaltRun.inside_halt_bound (hZ : NoZ π) (hR : HaltRun π c T) {nsym : Nat}
    (hcl : Closed π nsym) (hinit : ∀ x, c.tape x < nsym) (k : Int)
    (hblank : ∀ x, k ≤ x → c.tape x = 0) (h0 : c.pos < k) (hin : k ≤ P π c T) :
    Ent π c k T ≤ 2 * nsym + 1 := by
  have h0sym : 0 < nsym := by have := hinit k; rw [hblank k (Int.le_refl _)] at this; exact this
  have hval0 : QValid nsym (Dir.R, 0) := ⟨by simp, h0sym⟩
  -- 停止したセル y の時計は未定義に当たる
  have hy := hR.clock hZ (P π c T) (by omega) (T + 1) T (by omega) (Nat.le_refl _) rfl
  rw [hblank _ hin] at hy
  have hundef : oorb (clk π) (Dir.R, 0) (Vis π c (P π c T) T + 1) = none := by
    show (oorb (clk π) (Dir.R, 0) (Vis π c (P π c T) T)).bind (clk π) = none
    rw [hy]
    show (π (tr π c T).dir ((tr π c T).tape (P π c T))).map _ = none
    have := hR.halt
    unfold step2 at this
    cases hr : π (tr π c T).dir ((tr π c T).tape (tr π c T).pos) with
    | none => rfl
    | some r => rw [hr] at this; exact absurd this (by simp)
  -- 先頭セル k の訪問回数は 2·nsym 以下
  have hVk : Vis π c k T ≤ 2 * nsym := by
    refine Classical.byContradiction fun hbig => ?_
    have hbig' : 2 * nsym + 1 ≤ Vis π c k T := by omega
    -- 最後の訪問
    obtain ⟨u₀, hu₀a, hu₀b⟩ : ∃ u, u < T ∧ P π c u = k := by
      refine Classical.byContradiction fun hn => ?_
      have := Vis_const π c k 0 T (fun u _ h2 he => hn ⟨u, by omega, he⟩)
      rw [Nat.zero_add] at this
      have : Vis π c k 0 = 0 := rfl
      omega
    obtain ⟨u, hua, hub, huc, hud⟩ := exists_last (fun u => P π c u = k) (T - 1 - u₀) u₀ hu₀b
    have huT : u < T := by omega
    have hVu : Vis π c k T = Vis π c k u + 1 := by
      have e : T = (u + 1) + (T - (u + 1)) := by omega
      rw [e, Vis_const π c k (u + 1) _ (fun w h1 h2 => hud w (by omega) (by omega)),
        Vis_succ_of π c k u huc]
    have hcu := hR.clock hZ k h0 (u + 1) u (by omega) (by omega) huc
    rw [hblank k (Int.le_refl _)] at hcu
    have hdefT : oorb (clk π) (Dir.R, 0) (Vis π c k T) ≠ none := by
      rw [hVu]
      show (oorb (clk π) (Dir.R, 0) (Vis π c k u)).bind (clk π) ≠ none
      rw [hcu]
      have hst := hR.step u huT
      unfold step2 at hst
      have hread : (tr π c u).tape (tr π c u).pos = (tr π c u).tape k := by
        show (tr π c u).tape (P π c u) = _; rw [huc]
      rw [hread] at hst
      show (π (tr π c u).dir ((tr π c u).tape k)).map _ ≠ none
      cases hr : π (tr π c u).dir ((tr π c u).tape k) with
      | none => rw [hr] at hst; exact absurd hst (by simp)
      | some r => simp
    have hdef : ∀ m, m ≤ 2 * nsym → oorb (clk π) (Dir.R, 0) m ≠ none := by
      intro m hm hn
      have := oorb_none_mono (clk π) (Dir.R, 0) m (Vis π c k T - m) hn
      rw [show m + (Vis π c k T - m) = Vis π c k T by omega] at this
      exact hdefT this
    have hcodes : ∀ i, i ≤ 2 * nsym →
        qcode ((oorb (clk π) (Dir.R, 0) i).getD (Dir.R, 0)) < 2 * nsym := by
      intro i hi
      cases hq : oorb (clk π) (Dir.R, 0) i with
      | none => exact absurd hq (hdef i hi)
      | some q => exact qcode_lt (oorb_valid hZ hcl _ hval0 i q hq)
    obtain ⟨i, j, hij, hjN, hq⟩ := pigeon (2 * nsym)
      (fun i => qcode ((oorb (clk π) (Dir.R, 0) i).getD (Dir.R, 0))) hcodes
    have heq : oorb (clk π) (Dir.R, 0) i = oorb (clk π) (Dir.R, 0) j := by
      cases hqi : oorb (clk π) (Dir.R, 0) i with
      | none => exact absurd hqi (hdef i (by omega))
      | some qi =>
        cases hqj : oorb (clk π) (Dir.R, 0) j with
        | none => exact absurd hqj (hdef j hjN)
        | some qj =>
          simp only [hqi, hqj, Option.getD] at hq
          rw [qcode_inj (oorb_valid hZ hcl _ hval0 i qi hqi) (oorb_valid hZ hcl _ hval0 j qj hqj) hq]
    have htot := oorb_total_of_repeat (clk π) (Dir.R, 0) i j hij heq
      (fun m hm => hdef m (by omega))
    exact htot _ hundef
  have h1 := Ent_le_Vis π c k T
  have h2 : Vis π c k (T + 1) ≤ Vis π c k T + 1 := by
    by_cases h : P π c T = k
    · rw [Vis_succ_of π c k T h]; omega
    · rw [Vis_succ_not π c k T h]; omega
  omega

end Clock

end URTM.TwoState
