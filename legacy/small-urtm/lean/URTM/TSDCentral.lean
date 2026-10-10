/-
  2 状態 RTM の停止問題の決定可能性 その 7: 中央の有限領域（docs/10 の補題 D）。**手書き**。

  初期配置の非空白部分とヘッドを含む窓 [a,b] を取る。窓の外は両側とも空白の半直線。
    * `stepZ` : 窓の外へ出る 1 歩を「端で向きを反転して戻る」に置き換えた有限状態の機械
      （半直線からの退場は、補題 4.1 により「戻ってきた」という事実しか運ばない）
    * `sim`   : 実行の中で窓に居る時刻の列は `stepZ` の軌道をたどり、右（左）の半直線への
      入場回数は軌道上の「右（左）で反転した回数」に等しい
    * `central_bound` : 停止する実行では、両側の半直線への入場回数は
      `NB = csize·(2·nsym + 3) + 1` 以下。窓の状態は鳩の巣で周期に入り、周期の中で
      半直線へ出る回数は `inside_halt_bound` に抑えられる
-/
import URTM.TSDCode

namespace URTM.TwoState

/-- 窓 [a,b] の中の 1 歩。窓から出る 1 歩は、その場で向きを反転して戻ったことにする。 -/
def stepZ (π : Rule) (a b : Int) (z : Conf2) : Option Conf2 :=
  match π z.dir (z.tape z.pos) with
  | none => none
  | some (v, d') =>
    if a ≤ move d' z.pos ∧ move d' z.pos ≤ b then some ⟨write z.tape z.pos v, move d' z.pos, d'⟩
    else some ⟨write z.tape z.pos v, z.pos, flipD d'⟩

def reflR (π : Rule) (b : Int) (z : Conf2) : Nat :=
  match π z.dir (z.tape z.pos) with
  | none => 0
  | some (_, d') => if b < move d' z.pos then 1 else 0

def reflL (π : Rule) (a : Int) (z : Conf2) : Nat :=
  match π z.dir (z.tape z.pos) with
  | none => 0
  | some (_, d') => if move d' z.pos < a then 1 else 0

def zorb (π : Rule) (a b : Int) (c : Conf2) : Nat → Option Conf2 := oorb (stepZ π a b) c

def RefR (π : Rule) (a b : Int) (c : Conf2) : Nat → Nat
  | 0 => 0
  | n + 1 => RefR π a b c n + (match zorb π a b c n with | some z => reflR π b z | none => 0)

def RefL (π : Rule) (a b : Int) (c : Conf2) : Nat → Nat
  | 0 => 0
  | n + 1 => RefL π a b c n + (match zorb π a b c n with | some z => reflL π a z | none => 0)

theorem reflR_le (π : Rule) (b : Int) (z : Conf2) : reflR π b z ≤ 1 := by
  unfold reflR; split
  · omega
  · split <;> omega

theorem reflL_le (π : Rule) (a : Int) (z : Conf2) : reflL π a z ≤ 1 := by
  unfold reflL; split
  · omega
  · split <;> omega

theorem RefR_le (π : Rule) (a b : Int) (c : Conf2) : ∀ n, RefR π a b c n ≤ n := by
  intro n
  induction n with
  | zero => exact Nat.le_refl _
  | succ n ih =>
    show RefR π a b c n + _ ≤ n + 1
    split
    · have := reflR_le π b ‹_›; omega
    · omega

theorem RefL_le (π : Rule) (a b : Int) (c : Conf2) : ∀ n, RefL π a b c n ≤ n := by
  intro n
  induction n with
  | zero => exact Nat.le_refl _
  | succ n ih =>
    show RefL π a b c n + _ ≤ n + 1
    split
    · have := reflL_le π a ‹_›; omega
    · omega

theorem RefR_mono (π : Rule) (a b : Int) (c : Conf2) :
    ∀ (m n : Nat), RefR π a b c m ≤ RefR π a b c (m + n) := by
  intro m n
  induction n with
  | zero => exact Nat.le_refl _
  | succ n ih =>
    show RefR π a b c m ≤ RefR π a b c (m + n) + _
    omega

theorem RefL_mono (π : Rule) (a b : Int) (c : Conf2) :
    ∀ (m n : Nat), RefL π a b c m ≤ RefL π a b c (m + n) := by
  intro m n
  induction n with
  | zero => exact Nat.le_refl _
  | succ n ih =>
    show RefL π a b c m ≤ RefL π a b c (m + n) + _
    omega

/-- 周期の各コピーで右へ反転していれば、反転の回数はコピーの数以上。 -/
theorem RefR_ge (π : Rule) (a b : Int) (c : Conf2) (lam : Nat) (hlam : 1 ≤ lam) :
    ∀ (Q m : Nat), Q * lam ≤ m →
      (∀ q, 1 ≤ q → q ≤ Q → ∃ z, zorb π a b c (m - q * lam) = some z ∧ reflR π b z = 1) →
      Q ≤ RefR π a b c m := by
  intro Q
  induction Q with
  | zero => intro _ _ _; exact Nat.zero_le _
  | succ Q ih =>
    intro m hm h
    obtain ⟨z, hz, hr⟩ := h 1 (Nat.le_refl _) (by omega)
    rw [Nat.one_mul] at hz
    have ih' := ih (m - lam) (by rw [Nat.succ_mul] at hm; omega) (fun q h1 h2 => by
      have := h (q + 1) (by omega) (by omega)
      rw [show m - (q + 1) * lam = m - lam - q * lam by rw [Nat.succ_mul]; omega] at this
      exact this)
    have h1 : RefR π a b c (m - lam + 1) = RefR π a b c (m - lam) + 1 := by
      show RefR π a b c (m - lam) + _ = _
      rw [hz]; simp only; rw [hr]
    have hml : lam ≤ m := by have h' : (Q + 1) * lam = Q * lam + lam := Nat.succ_mul Q lam; omega
    have h2 := RefR_mono π a b c (m - lam + 1) (m - (m - lam + 1))
    rw [show m - lam + 1 + (m - (m - lam + 1)) = m by omega] at h2
    omega

theorem RefL_ge (π : Rule) (a b : Int) (c : Conf2) (lam : Nat) (hlam : 1 ≤ lam) :
    ∀ (Q m : Nat), Q * lam ≤ m →
      (∀ q, 1 ≤ q → q ≤ Q → ∃ z, zorb π a b c (m - q * lam) = some z ∧ reflL π a z = 1) →
      Q ≤ RefL π a b c m := by
  intro Q
  induction Q with
  | zero => intro _ _ _; exact Nat.zero_le _
  | succ Q ih =>
    intro m hm h
    obtain ⟨z, hz, hr⟩ := h 1 (Nat.le_refl _) (by omega)
    rw [Nat.one_mul] at hz
    have ih' := ih (m - lam) (by rw [Nat.succ_mul] at hm; omega) (fun q h1 h2 => by
      have := h (q + 1) (by omega) (by omega)
      rw [show m - (q + 1) * lam = m - lam - q * lam by rw [Nat.succ_mul]; omega] at this
      exact this)
    have h1 : RefL π a b c (m - lam + 1) = RefL π a b c (m - lam) + 1 := by
      show RefL π a b c (m - lam) + _ = _
      rw [hz]; simp only; rw [hr]
    have hml : lam ≤ m := by have h' : (Q + 1) * lam = Q * lam + lam := Nat.succ_mul Q lam; omega
    have h2 := RefL_mono π a b c (m - lam + 1) (m - (m - lam + 1))
    rw [show m - lam + 1 + (m - (m - lam + 1)) = m by omega] at h2
    omega

/-- 窓 [a,b] に居る回数。 -/
def Cnt (π : Rule) (c : Conf2) (a b : Int) : Nat → Nat
  | 0 => 0
  | t + 1 => Cnt π c a b t + if a ≤ P π c t ∧ P π c t ≤ b then 1 else 0

theorem Cnt_const (π : Rule) (c : Conf2) (a b : Int) :
    ∀ (t n : Nat), (∀ u, t ≤ u → u < t + n → ¬ (a ≤ P π c u ∧ P π c u ≤ b)) →
      Cnt π c a b (t + n) = Cnt π c a b t := by
  intro t n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro h
    have e : t + (n + 1) = (t + n) + 1 := by omega
    rw [e]
    show Cnt π c a b (t + n) + _ = _
    rw [if_neg (h (t + n) (by omega) (by omega))]
    exact ih (fun u h1 h2 => h u h1 (by omega))

theorem EntL_const (π : Rule) (c : Conf2) (a : Int) :
    ∀ (t n : Nat), (∀ u, t ≤ u → u < t + n → ¬ LStep π c a u) →
      EntL π c a (t + n) = EntL π c a t := by
  intro t n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro h
    have e : t + (n + 1) = (t + n) + 1 := by omega
    rw [e]
    show EntL π c a (t + n) + _ = _
    rw [if_neg (h (t + n) (by omega) (by omega))]
    exact ih (fun u h1 h2 => h u h1 (by omega))

section Central
variable {π : Rule} {c : Conf2} {T : Nat}

/-- 窓の外に居る間は、窓のどちら側かが変わらない。 -/
theorem HaltRun.outside_right (hZ : NoZ π) (hR : HaltRun π c T) (a b : Int) (hab : a ≤ b) :
    ∀ (t₁ n : Nat), t₁ + n ≤ T → b < P π c t₁ →
      (∀ u, t₁ ≤ u → u ≤ t₁ + n → ¬ (a ≤ P π c u ∧ P π c u ≤ b)) → b < P π c (t₁ + n) := by
  intro t₁ n
  induction n with
  | zero => intro _ h _; exact h
  | succ n ih =>
    intro hT h hout
    have h1 := ih (by omega) h (fun u h1 h2 => hout u h1 (by omega))
    have hm := hR.move1 hZ (t₁ + n) (by omega)
    have ho := hout (t₁ + n + 1) (by omega) (by omega)
    rw [show t₁ + (n + 1) = t₁ + n + 1 by omega]
    omega

theorem HaltRun.outside_left (hZ : NoZ π) (hR : HaltRun π c T) (a b : Int) (hab : a ≤ b) :
    ∀ (t₁ n : Nat), t₁ + n ≤ T → P π c t₁ < a →
      (∀ u, t₁ ≤ u → u ≤ t₁ + n → ¬ (a ≤ P π c u ∧ P π c u ≤ b)) → P π c (t₁ + n) < a := by
  intro t₁ n
  induction n with
  | zero => intro _ h _; exact h
  | succ n ih =>
    intro hT h hout
    have h1 := ih (by omega) h (fun u h1 h2 => hout u h1 (by omega))
    have hm := hR.move1 hZ (t₁ + n) (by omega)
    have ho := hout (t₁ + n + 1) (by omega) (by omega)
    rw [show t₁ + (n + 1) = t₁ + n + 1 by omega]
    omega

/-- 窓の配置が実行の配置を写している。 -/
def SimZ (π : Rule) (c : Conf2) (a b : Int) (z : Conf2) (t : Nat) : Prop :=
  z.pos = P π c t ∧ z.dir = (tr π c t).dir ∧ ∀ x, a ≤ x → x ≤ b → z.tape x = (tr π c t).tape x

/-- **窓の機械は実行をたどる**。 -/
theorem HaltRun.sim (hZ : NoZ π) (hR : HaltRun π c T) (a b : Int) (hab : a ≤ b)
    (ha : a ≤ c.pos) (hb : c.pos ≤ b) :
    ∀ (N t : Nat), t < N → t ≤ T → (a ≤ P π c t ∧ P π c t ≤ b) →
      ∃ z, zorb π a b c (Cnt π c a b t) = some z ∧ SimZ π c a b z t ∧
        Ent π c (b + 1) t = RefR π a b c (Cnt π c a b t) ∧
        EntL π c a t = RefL π a b c (Cnt π c a b t) := by
  intro N
  induction N with
  | zero => intro t ht; omega
  | succ N ih =>
    intro t htN htT hin
    rcases Nat.eq_zero_or_pos t with h0 | hpos
    · subst h0
      exact ⟨c, rfl, ⟨rfl, rfl, fun _ _ _ => rfl⟩, rfl, rfl⟩
    -- 直前の窓の時刻 t'
    have hc0 : a ≤ P π c 0 ∧ P π c 0 ≤ b := ⟨ha, hb⟩
    obtain ⟨t', ht'a, ht'b, ht'c, ht'd⟩ :=
      exists_last (fun u => a ≤ P π c u ∧ P π c u ≤ b) (t - 1) 0 hc0
    rw [Nat.zero_add] at ht'b ht'd
    have hno : ∀ u, t' < u → u < t → ¬ (a ≤ P π c u ∧ P π c u ≤ b) :=
      fun u h1 h2 => ht'd u h1 (by omega)
    have ht't : t' < t := by omega
    obtain ⟨z', hz'1, ⟨hz'p, hz'd, hz't⟩, hE', hL'⟩ := ih t' (by omega) (by omega) ht'c
    have hCnt : Cnt π c a b t = Cnt π c a b t' + 1 := by
      have e : t = (t' + 1) + (t - (t' + 1)) := by omega
      rw [e, Cnt_const π c a b (t' + 1) _ (fun u h1 h2 => hno u (by omega) (by omega))]
      show Cnt π c a b t' + _ = _
      rw [if_pos ht'c]
    -- 実行の 1 歩
    have hst := hR.step t' (by omega)
    obtain ⟨v, d', hr, htp, hps, hdr⟩ := step2_some π hst
    have hread : z'.tape z'.pos = (tr π c t').tape (tr π c t').pos := by
      rw [hz'p]; exact hz't _ ht'c.1 ht'c.2
    have hrz : π z'.dir (z'.tape z'.pos) = some (v, d') := by rw [hread, hz'd]; exact hr
    have hz := hZ _ _ _ _ hr
    have hstepZ : zorb π a b c (Cnt π c a b t) = stepZ π a b z' := by
      rw [hCnt]; show (zorb π a b c (Cnt π c a b t')).bind (stepZ π a b) = _; rw [hz'1]; rfl
    have hRR : RefR π a b c (Cnt π c a b t) = RefR π a b c (Cnt π c a b t') + reflR π b z' := by
      rw [hCnt]; show RefR π a b c _ + _ = _; rw [hz'1]
    have hLL : RefL π a b c (Cnt π c a b t) = RefL π a b c (Cnt π c a b t') + reflL π a z' := by
      rw [hCnt]; show RefL π a b c _ + _ = _; rw [hz'1]
    have hmv : move d' z'.pos = P π c (t' + 1) := by
      rw [hz'p]; show _ = (tr π c (t' + 1)).pos; rw [hps]
    rw [hstepZ, hRR, hLL]
    unfold stepZ reflR reflL
    rw [hrz]
    simp only
    by_cases hwin : a ≤ move d' z'.pos ∧ move d' z'.pos ≤ b
    · -- 窓の中の 1 歩: t = t'+1
      rw [if_pos hwin]
      have hin1 : a ≤ P π c (t' + 1) ∧ P π c (t' + 1) ≤ b := by rw [← hmv]; exact hwin
      have htt : t = t' + 1 := by
        refine Classical.byContradiction fun hne => hno (t' + 1) (by omega) (by omega) hin1
      subst htt
      have hnr : ¬ b < move d' z'.pos := by omega
      have hnl : ¬ move d' z'.pos < a := by omega
      rw [if_neg hnr, if_neg hnl]
      refine ⟨_, rfl, ⟨hmv, by rw [hdr], ?_⟩, ?_, ?_⟩
      · intro x hx1 hx2
        show write z'.tape z'.pos v x = (tr π c (t' + 1)).tape x
        rw [htp]; unfold write; rw [hz'p]
        show (if x = P π c t' then v else z'.tape x) = (if x = P π c t' then v else _)
        rw [hz't x hx1 hx2]
      · rw [Ent_succ_not π c (b + 1) t' (fun h => by have := h.2; omega), hE']; rfl
      · show EntL π c a t' + (if LStep π c a t' then 1 else 0) = _
        rw [if_neg (fun h => by have := h.2; omega), hL']
    · rw [if_neg hwin]
      have hout1 : ¬ (a ≤ P π c (t' + 1) ∧ P π c (t' + 1) ≤ b) := by rw [← hmv]; exact hwin
      have ht1 : t' + 1 < t := by
        rcases Nat.lt_or_ge (t' + 1) t with h | h
        · exact h
        · have : t = t' + 1 := by omega
          rw [this] at hin; exact absurd hin hout1
      have hmove := hR.stepMove hZ t' (by omega)
      by_cases hright : b < move d' z'.pos
      · -- 右の半直線へ出て、戻ってきた
        rw [if_pos hright]
        have hnl : ¬ move d' z'.pos < a := by omega
        rw [if_neg hnl]
        have hp' : P π c t' = b := by rcases hmove with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
        have hp1 : P π c (t' + 1) = b + 1 := by rcases hmove with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
        have hdR : d' = Dir.R := by
          rcases hmove with ⟨h, hd⟩ | ⟨h, _⟩
          · rw [← hd, hdr]
          · omega
        have hgt : ∀ u, t' + 1 ≤ u → u ≤ t - 1 → b < P π c u := by
          intro u h1 h2
          have := hR.outside_right hZ a b hab (t' + 1) (u - (t' + 1)) (by omega) (by omega)
            (fun w w1 w2 => hno w (by omega) (by omega))
          rwa [show t' + 1 + (u - (t' + 1)) = u by omega] at this
        obtain ⟨tm, rfl⟩ : ∃ tm, t = tm + 1 := ⟨t - 1, by omega⟩
        have hgm := hgt tm (by omega) (by omega)
        have hmv2 := hR.stepMove hZ tm (by omega)
        have hpt : P π c (tm + 1) = b := by rcases hmv2 with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
        have hdt : (tr π c (tm + 1)).dir = Dir.L := by
          rcases hmv2 with ⟨h, _⟩ | ⟨_, hd⟩
          · omega
          · exact hd
        refine ⟨_, rfl, ⟨by rw [hz'p, hp', hpt], by rw [hdt, hdR]; rfl, ?_⟩, ?_, ?_⟩
        · intro x hx1 hx2
          have hfz := hR.frozen_left b (t' + 1) (tm + 1) (by omega) htT
            (fun u h1 h2 => hgt u h1 (by omega)) x hx2
          rw [hfz, htp]
          show write z'.tape z'.pos v x = write (tr π c t').tape (tr π c t').pos v x
          unfold write; rw [hz'p]
          show (if x = P π c t' then v else z'.tape x) = (if x = P π c t' then v else _)
          rw [hz't x hx1 hx2]
        · -- 右の入場回数は 1 増える
          have e : tm + 1 = (t' + 1) + (tm - t') := by omega
          rw [e, Ent_const π c (b + 1) (t' + 1) _ (fun u h1 h2 hs => by
            have := hgt u h1 (by omega); have := hs.1; omega),
            Ent_succ_of π c (b + 1) t' ⟨by omega, by omega⟩, hE']
        · have e : tm + 1 = (t' + 1) + (tm - t') := by omega
          rw [e, EntL_const π c a (t' + 1) _ (fun u h1 h2 hs => by
            have := hgt u h1 (by omega); have := hs.1; omega)]
          show EntL π c a t' + (if LStep π c a t' then 1 else 0) = _
          rw [if_neg (fun h => by have := h.2; omega), hL']
      · -- 左の半直線へ出て、戻ってきた
        rw [if_neg hright]
        have hleft : move d' z'.pos < a := by omega
        rw [if_pos hleft]
        have hp' : P π c t' = a := by rcases hmove with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
        have hp1 : P π c (t' + 1) = a - 1 := by rcases hmove with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
        have hdL : d' = Dir.L := by
          rcases hmove with ⟨h, _⟩ | ⟨h, hd⟩
          · omega
          · rw [← hd, hdr]
        have hlt : ∀ u, t' + 1 ≤ u → u ≤ t - 1 → P π c u < a := by
          intro u h1 h2
          have := hR.outside_left hZ a b hab (t' + 1) (u - (t' + 1)) (by omega) (by omega)
            (fun w w1 w2 => hno w (by omega) (by omega))
          rwa [show t' + 1 + (u - (t' + 1)) = u by omega] at this
        obtain ⟨tm, rfl⟩ : ∃ tm, t = tm + 1 := ⟨t - 1, by omega⟩
        have hgm := hlt tm (by omega) (by omega)
        have hmv2 := hR.stepMove hZ tm (by omega)
        have hpt : P π c (tm + 1) = a := by rcases hmv2 with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
        have hdt : (tr π c (tm + 1)).dir = Dir.R := by
          rcases hmv2 with ⟨_, hd⟩ | ⟨h, _⟩
          · exact hd
          · omega
        refine ⟨_, rfl, ⟨by rw [hz'p, hp', hpt], by rw [hdt, hdL]; rfl, ?_⟩, ?_, ?_⟩
        · intro x hx1 hx2
          have hfz := hR.frozen_right a (t' + 1) (tm + 1) (by omega) htT
            (fun u h1 h2 => hlt u h1 (by omega)) x hx1
          rw [hfz, htp]
          show write z'.tape z'.pos v x = write (tr π c t').tape (tr π c t').pos v x
          unfold write; rw [hz'p]
          show (if x = P π c t' then v else z'.tape x) = (if x = P π c t' then v else _)
          rw [hz't x hx1 hx2]
        · have e : tm + 1 = (t' + 1) + (tm - t') := by omega
          rw [e, Ent_const π c (b + 1) (t' + 1) _ (fun u h1 h2 hs => by
            have := hlt u h1 (by omega); have := hs.1; omega)]
          rw [Ent_succ_not π c (b + 1) t' (fun h => by have := h.2; omega), hE']; rfl
        · have e : tm + 1 = (t' + 1) + (tm - t') := by omega
          rw [e, EntL_const π c a (t' + 1) _ (fun u h1 h2 hs => by
            have := hlt u h1 (by omega); have := hs.1; omega)]
          show EntL π c a t' + (if LStep π c a t' then 1 else 0) = _
          rw [if_pos ⟨hp', hp1⟩, hL']

end Central

end URTM.TwoState
