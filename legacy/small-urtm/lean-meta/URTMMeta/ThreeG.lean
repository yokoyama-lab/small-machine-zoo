/-
  3 状態 2 記号の URTM（段階 2e の 3）: **群 D のうち「右へ動いて入る吸収的な状態」の 16 類**（192 表）。**手書き**。

  ある状態 z について（`AbsorbR`）: z から出る規則はどれも z へ入り、z へ入る規則は右へ、それ以外の状態へ入る規則は左へ動く。
  すると実行は 2 段しかない: z に入るまでは毎歩左へ（`lphase`）、z に入ってからは z のまま毎歩右へ（`z_after`）。
  * 左の段: 窓の左端 a を越えると、読むマスは初めて訪れる空白なので、次の状態は今の状態だけで決まる（`dl`）。
    z でない状態は高々 2 つなので、a − 1, a − 2, a − 3 での状態のうち 2 つは等しく、以後は周期 2 で繰り返す（`period2`）。
    よって止まる実行では、左の段は a − 3 より先へは進まない。
  * 右の段: 窓の右端 b を越えると、読むマスは初めて訪れる空白。b + 1 で規則があれば以後も同じ規則で止まらない。
  まとめて、止まるなら 2(b − a) + 8 歩以内に止まる（`halts_iff_boundG`）。左の証明書も右の要約も使わない。
  検査 `grpG es D`（Bool）: 表か鏡像の表で、ある z について `absorbR`。主定理 `no_three_two_URTM_G`（`isExcG = isExcF && !grpG`）。
  例外は高々 384 表。
-/
import URTMMeta.ThreeF

namespace URTM.Meta
open URTM URTM.TwoState URTM.Three

/-- 状態 z は吸収的: z から出る規則は z へ入る。z へ入る規則は右へ、他へ入る規則は左へ動く。 -/
structure AbsorbR (tbl : List Quint) (z : Nat) : Prop where
  hz : ∀ ρ ∈ tbl, ρ.p = z → ρ.q = z
  hR : ∀ ρ ∈ tbl, ρ.q = z → ρ.d = Dir.R
  hL : ∀ ρ ∈ tbl, ρ.q ≠ z → ρ.d = Dir.L
  hz3 : z < 3

/-- 空白を読んだときの次の状態（規則が無ければ 0。使うのは規則があるときだけ）。 -/
def dl (tbl : List Quint) (s : Nat) : Nat := ((find? tbl s 0).map Quint.q).getD 0

theorem qstep_ne_none_of {tbl : List Quint} {d : QConf} {s : Nat} {ρ : Quint} (hs : d.tape d.pos = s)
    (h : find? tbl d.st s = some ρ) : qstep tbl d ≠ none := by
  simp [qstep, hs, h]

section absorb
variable {tbl : List Quint} {z : Nat} (A : AbsorbR tbl z) {c : QConf} {T : Nat} (hR : QHaltRun tbl c T)
include A hR

theorem stepG {t : Nat} (ht : t < T) : ∃ ρ ∈ tbl, ρ.p = (qtr tbl c t).st ∧
    find? tbl (qtr tbl c t).st ((qtr tbl c t).tape (qtr tbl c t).pos) = some ρ ∧
    qtr tbl c (t + 1) = ⟨ρ.q, move ρ.d (qtr tbl c t).pos, write (qtr tbl c t).tape (qtr tbl c t).pos ρ.t⟩ := by
  obtain ⟨ρ, hρ, hf, e1⟩ := qstep_some (hR.step t ht)
  exact ⟨ρ, hρ, (find?_spec hf).2.1, hf, e1⟩

theorem z_succ {t : Nat} (ht : t < T) (h : (qtr tbl c t).st = z) :
    (qtr tbl c (t + 1)).st = z ∧ (qtr tbl c (t + 1)).pos = (qtr tbl c t).pos + 1 := by
  obtain ⟨ρ, hρ, hp, -, e1⟩ := stepG A hR ht
  have hq := A.hz ρ hρ (hp.trans h)
  have hd := A.hR ρ hρ hq
  rw [e1, hd]; exact ⟨hq, rfl⟩

/-- **右の段**: z に入ってからは z のまま毎歩右へ。 -/
theorem z_after {t : Nat} (h : (qtr tbl c t).st = z) :
    ∀ n, t + n ≤ T → (qtr tbl c (t + n)).st = z ∧ (qtr tbl c (t + n)).pos = (qtr tbl c t).pos + n
  | 0, _ => ⟨h, by simp⟩
  | n + 1, hn => by
    obtain ⟨h1, h2⟩ := z_after h n (by omega)
    obtain ⟨h3, h4⟩ := z_succ A hR (t := t + n) (by omega) h1
    refine ⟨h3, ?_⟩
    rw [show t + (n + 1) = t + n + 1 by omega, h4, h2]; push_cast; omega

/-- **左の段**: z に居ない時刻までは、ずっと z に居らず、毎歩左へ。 -/
theorem lphase : ∀ t, t ≤ T → (qtr tbl c t).st ≠ z →
    (∀ u, u ≤ t → (qtr tbl c u).st ≠ z) ∧ (qtr tbl c t).pos = c.pos - t
  | 0, _, h => ⟨fun u hu => by rw [show u = 0 by omega]; exact h,
      by show c.pos = c.pos - ((0 : Nat) : Int); simp⟩
  | t + 1, ht, h => by
    have hprev : (qtr tbl c t).st ≠ z := fun h' => h (z_succ A hR (by omega) h').1
    obtain ⟨h1, h2⟩ := lphase t (by omega) hprev
    obtain ⟨ρ, hρ, -, -, e1⟩ := stepG A hR (t := t) (by omega)
    have hq : ρ.q ≠ z := by rw [e1] at h; exact h
    have hd := A.hL ρ hρ hq
    refine ⟨fun u hu => ?_, ?_⟩
    · rcases Nat.lt_or_ge u (t + 1) with hu' | hu'
      · exact h1 u (by omega)
      · obtain rfl : u = t + 1 := by omega
        exact h
    · rw [e1, hd]
      show (qtr tbl c t).pos - 1 = c.pos - ((t + 1 : Nat) : Int)
      rw [h2]; push_cast; omega

/-- 左の段で窓の左端より左のマスは、初めて訪れる空白。 -/
theorem read_fresh_left {a : Int} (hz : ∀ x, x < a → c.tape x = 0) {v : Nat} (hv : v ≤ T)
    (h : (qtr tbl c v).st ≠ z) (hpos : c.pos - v < a) :
    (qtr tbl c v).tape (qtr tbl c v).pos = 0 := by
  obtain ⟨h1, h2⟩ := lphase A hR v hv h
  rw [h2]
  have := hR.cell_frozen (c.pos - v) 0 v (by omega) (fun u _ hu he => by
    have hst := h1 u (by omega)
    have := (lphase A hR u (by omega) hst).2
    unfold QP at he; omega)
  rw [Nat.zero_add] at this
  rw [this]; exact hz _ hpos

/-- 右の段で窓の右端より右のマスは、初めて訪れる空白。 -/
theorem read_fresh_right {b : Int} (hzr : ∀ x, b < x → c.tape x = 0) (hcb : c.pos ≤ b) {t1 v : Nat}
    (hv : v ≤ T) (ht1v : t1 ≤ v) (hst1 : (qtr tbl c t1).st = z) (hne : ∀ u, u < t1 → (qtr tbl c u).st ≠ z)
    (hpv : b < (qtr tbl c v).pos) : (qtr tbl c v).tape (qtr tbl c v).pos = 0 := by
  have hv2 := (z_after A hR hst1 (v - t1) (by omega)).2
  rw [show t1 + (v - t1) = v by omega] at hv2
  have := hR.cell_frozen ((qtr tbl c v).pos) 0 v (by omega) (fun u _ hu he => by
    unfold QP at he
    rcases Nat.lt_or_ge u t1 with hut | hut
    · have := (lphase A hR u (by omega) (hne u hut)).2
      omega
    · have hu2 := (z_after A hR hst1 (u - t1) (by omega)).2
      rw [show t1 + (u - t1) = u by omega] at hu2
      omega)
  rw [Nat.zero_add] at this
  rw [this]; exact hzr _ hpv

theorem st_succ_blank {u : Nat} (hu : u < T) (h0 : (qtr tbl c u).tape (qtr tbl c u).pos = 0) :
    (qtr tbl c (u + 1)).st = dl tbl (qtr tbl c u).st ∧ ∃ ρ, find? tbl (qtr tbl c u).st 0 = some ρ := by
  obtain ⟨ρ, -, -, hf, e1⟩ := stepG A hR hu
  rw [h0] at hf
  refine ⟨?_, ρ, hf⟩
  rw [e1]; unfold dl; rw [hf]; rfl

/-- **左の段は窓の左端を越えると周期 2 で繰り返す**。 -/
theorem period2 {a : Int} (hz : ∀ x, x < a → c.tape x = 0) (hsrc : Src3 tbl) (u0 : Nat)
    (hu0 : c.pos - u0 = a - 1) {M : Nat} (hM : M ≤ T) (hne : ∀ u, u < M → (qtr tbl c u).st ≠ z) :
    ∀ k, u0 + 3 + k ≤ M → (qtr tbl c (u0 + 3 + k)).st = (qtr tbl c (u0 + 1 + k)).st := by
  have hb : ∀ u, u0 ≤ u → u < M → (qtr tbl c (u + 1)).st = dl tbl (qtr tbl c u).st := fun u h1 h2 =>
    (st_succ_blank A hR (by omega) (read_fresh_left A hR hz (by omega) (hne u h2) (by omega))).1
  have hlt : ∀ u, u < M → (qtr tbl c u).st < 3 := fun u hu => hR.st_lt hsrc u (by omega)
  intro k
  induction k with
  | zero =>
    intro hk
    have e1 := hb u0 le_rfl (by omega)
    have e2 := hb (u0 + 1) (by omega) (by omega)
    have e3 := hb (u0 + 2) (by omega) (by omega)
    have l0 := hlt u0 (by omega)
    have l1 := hlt (u0 + 1) (by omega)
    have l2 := hlt (u0 + 2) (by omega)
    have n0 := hne u0 (by omega)
    have n1 := hne (u0 + 1) (by omega)
    have n2 := hne (u0 + 2) (by omega)
    rw [show u0 + 3 + 0 = u0 + 2 + 1 by omega, e3, show u0 + 1 + 0 = u0 + 1 by omega]
    have hc : (qtr tbl c u0).st = (qtr tbl c (u0 + 2)).st ∨ (qtr tbl c u0).st = (qtr tbl c (u0 + 1)).st ∨
        (qtr tbl c (u0 + 1)).st = (qtr tbl c (u0 + 2)).st := by have := A.hz3; omega
    rcases hc with h | h | h
    · rw [← h]; exact e1.symm
    · have h21 : (qtr tbl c (u0 + 2)).st = (qtr tbl c (u0 + 1)).st := by
        rw [e2, show dl tbl (qtr tbl c (u0 + 1)).st = dl tbl (qtr tbl c u0).st by rw [h]]; exact e1.symm
      rw [h21, show dl tbl (qtr tbl c (u0 + 1)).st = dl tbl (qtr tbl c u0).st by rw [h]]; exact e1.symm
    · rw [← h, ← e2]; exact h.symm
  | succ k ih =>
    intro hk
    have ih' := ih (by omega)
    rw [show u0 + 3 + (k + 1) = u0 + 3 + k + 1 by omega, hb (u0 + 3 + k) (by omega) (by omega), ih',
      show u0 + 1 + (k + 1) = u0 + 1 + k + 1 by omega, hb (u0 + 1 + k) (by omega) (by omega)]

/-- **止まる実行の歩数**: 2(b − a) + 7 以下。 -/
theorem halt_bound_G {a b : Int} (hsrc : Src3 tbl) (ha : a ≤ c.pos) (hb : c.pos ≤ b)
    (hz : ∀ x, (x < a ∨ b < x) → c.tape x = 0) : T + 1 ≤ 2 * (b - a).toNat + 8 := by
  have hzl : ∀ x, x < a → c.tape x = 0 := fun x hx => hz x (Or.inl hx)
  have hzr : ∀ x, b < x → c.tape x = 0 := fun x hx => hz x (Or.inr hx)
  obtain ⟨u0, hu0⟩ : ∃ u0 : Nat, (u0 : Int) = c.pos - a + 1 := ⟨(c.pos - a + 1).toNat, by omega⟩
  have hu0' : c.pos - u0 = a - 1 := by omega
  have hdead := qstep_qtr_T hR
  by_cases hT : (qtr tbl c T).st = z
  · classical
    have hex : ∃ t, (qtr tbl c t).st = z := ⟨T, hT⟩
    have hst1 : (qtr tbl c (Nat.find hex)).st = z := Nat.find_spec hex
    have hT1 : Nat.find hex ≤ T := Nat.find_min' hex hT
    have hne : ∀ u, u < Nat.find hex → (qtr tbl c u).st ≠ z := fun u hu => Nat.find_min hex hu
    -- 左の段は短い
    have ht1b : Nat.find hex ≤ u0 + 2 := by
      by_contra hc
      have := period2 A hR hzl hsrc u0 hu0' hT1 hne (Nat.find hex - (u0 + 3)) (by omega)
      rw [show u0 + 3 + (Nat.find hex - (u0 + 3)) = Nat.find hex by omega] at this
      rw [this] at hst1
      exact hne _ (by omega) hst1
    -- z に入った位置
    have hp1 : c.pos - Nat.find hex ≤ (qtr tbl c (Nat.find hex)).pos ∧
        (qtr tbl c (Nat.find hex)).pos ≤ c.pos + 1 := by
      rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | h0
      · rw [h0]; show c.pos - ((0 : Nat) : Int) ≤ c.pos ∧ c.pos ≤ c.pos + 1; omega
      · have hpre := (lphase A hR (Nat.find hex - 1) (by omega) (hne _ (by omega))).2
        obtain ⟨ρ, hρ, -, -, e1⟩ := stepG A hR (t := Nat.find hex - 1) (by omega)
        rw [show Nat.find hex - 1 + 1 = Nat.find hex by omega] at e1
        have hq : ρ.q = z := by rw [e1] at hst1; exact hst1
        have hd := A.hR ρ hρ hq
        rw [e1, hd]
        show c.pos - (Nat.find hex : Int) ≤ (qtr tbl c (Nat.find hex - 1)).pos + 1 ∧
          (qtr tbl c (Nat.find hex - 1)).pos + 1 ≤ c.pos + 1
        rw [hpre]; omega
    -- 右の段: b + 1 に着いた時刻で止まっていなければ、以後も止まらない
    obtain ⟨n, hn⟩ : ∃ n : Nat, (n : Int) = b + 1 - (qtr tbl c (Nat.find hex)).pos :=
      ⟨(b + 1 - (qtr tbl c (Nat.find hex)).pos).toNat, by omega⟩
    have hTn : T ≤ Nat.find hex + n := by
      by_contra hc
      have hs := z_after A hR hst1 n (by omega)
      have hsT := z_after A hR hst1 (T - Nat.find hex) (by omega)
      rw [show Nat.find hex + (T - Nat.find hex) = T by omega] at hsT
      have r1 := read_fresh_right A hR hzr hb (v := Nat.find hex + n) (by omega) (by omega) hst1 hne
        (by rw [hs.2]; omega)
      obtain ⟨ρ, hf⟩ := (st_succ_blank A hR (by omega) r1).2
      rw [hs.1] at hf
      have rT := read_fresh_right A hR hzr hb (v := T) le_rfl hT1 hst1 hne (by rw [hsT.2]; omega)
      exact qstep_ne_none_of rT (by rw [hsT.1]; exact hf) hdead
    omega
  · -- 左の段のまま止まった
    have hall := (lphase A hR T le_rfl hT).1
    have hT3 : T ≤ u0 + 2 := by
      by_contra hc
      have := period2 A hR hzl hsrc u0 hu0' (M := T) le_rfl (fun u _ => hall u (by omega))
        (T - (u0 + 3)) (by omega)
      rw [show u0 + 3 + (T - (u0 + 3)) = T by omega, show u0 + 1 + (T - (u0 + 3)) = T - 2 by omega] at this
      have r2 := read_fresh_left A hR hzl (v := T - 2) (by omega) (hall _ (by omega)) (by omega)
      obtain ⟨ρ, hf⟩ := (st_succ_blank A hR (by omega) r2).2
      have rT := read_fresh_left A hR hzl (v := T) le_rfl hT (by omega)
      exact qstep_ne_none_of rT (by rw [this]; exact hf) hdead
    omega

end absorb

/-- 止まる実行の歩数の上界（窓 [a, b]）。 -/
def boundG (a b : Int) : Nat := 2 * (b - a).toNat + 8

/-- **有界停止（吸収的な状態）**。 -/
theorem halts_iff_boundG {tbl : List Quint} {z : Nat} (hsrc : Src3 tbl) (A : AbsorbR tbl z)
    (c : QConf) (a b : Int) (ha : a ≤ c.pos) (hb : c.pos ≤ b) (hz : ∀ x, (x < a ∨ b < x) → c.tape x = 0) :
    QHalts tbl c ↔ qrun tbl (boundG a b) c = none := by
  constructor
  · intro hH
    obtain ⟨T, hR⟩ := qhalts_haltRun hH
    exact qrun_none_mono tbl c (T + 1) _ hR.dead (halt_bound_G A hR hsrc ha hb hz)
  · intro h; exact ⟨_, h⟩

/-! ### Bool の検査 -/

def absorbR (tbl : List Quint) (z : Nat) : Bool :=
  tbl.all fun ρ => decide (ρ.p = z → ρ.q = z) && decide (ρ.q = z → ρ.d = Dir.R) &&
    decide (ρ.q ≠ z → ρ.d = Dir.L)

theorem absorbR_spec {tbl : List Quint} {z : Nat} (hz3 : z < 3) (h : absorbR tbl z = true) : AbsorbR tbl z := by
  unfold absorbR at h
  rw [List.all_eq_true] at h
  refine ⟨fun ρ hρ => ?_, fun ρ hρ => ?_, fun ρ hρ => ?_, hz3⟩
  · have := h ρ hρ
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact this.1.1
  · have := h ρ hρ
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact this.1.2
  · have := h ρ hρ
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact this.2

/-- **群 D の「吸収的な状態」16 類の検査**: 表か、その鏡像に、吸収的で右へ動いて入る状態がある。 -/
def grpG (es : List Nat) (D : List Dir) : Bool :=
  (List.range 3).any (absorbR (URTM.Three.realize es D)) ||
    (List.range 3).any (absorbR (mirTbl (URTM.Three.realize es D)))

/-- 段階 2e の 3 の例外: `isExcF` の表のうち、この 16 類に当たらない表。 -/
def isExcG (es : List Nat) (D : List Dir) : Bool := isExcF es D && !grpG es D

theorem sideG_bound {tbl : List Quint} (hsrc : Src3 tbl) (h : (List.range 3).any (absorbR tbl) = true) :
    ∀ (c : QConf) (a b : Int), a ≤ c.pos → c.pos ≤ b →
      (∀ x, (x < a ∨ b < x) → c.tape x = 0) → (QHalts tbl c ↔ qrun tbl (boundG a b) c = none) := by
  obtain ⟨z, hz3, hz⟩ := List.any_eq_true.mp h
  exact fun c a b ha hb hz' => halts_iff_boundG hsrc (absorbR_spec (List.mem_range.mp hz3) hz) c a b ha hb hz'

theorem sideG_mir_bound {tbl : List Quint} (hsrc : Src3 tbl)
    (h : (List.range 3).any (absorbR (mirTbl tbl)) = true) :
    ∀ (c : QConf) (a b : Int), a ≤ c.pos → c.pos ≤ b →
      (∀ x, (x < a ∨ b < x) → c.tape x = 0) → (QHalts tbl c ↔ qrun tbl (boundG a b) c = none) := by
  rw [mirTbl_eq] at h
  have hb := sideG_bound (src3_mir hsrc) h
  intro c a b ha hb' hz
  have := hb (mirQ c) (-b) (-a) (by show -b ≤ -c.pos; omega) (by show -c.pos ≤ -a; omega)
    (fun x hx => by show c.tape (-x) = 0; exact hz (-x) (by omega))
  rw [QHalts_mir, qrun_mir] at this
  have e : boundG (-b) (-a) = boundG a b := by
    unfold boundG; rw [show -a - -b = b - a by omega]
  rw [e] at this
  rw [this]
  cases qrun tbl (boundG a b) c <;> simp

/-- 窓の幅で書いた上界。 -/
def bndG (w : Nat) : Nat := 2 * w + 8

theorem bndG_primrec : Primrec bndG :=
  (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id) (Primrec.const 8)).of_eq
    fun w => rfl

theorem boundG_eq (m n : Nat) : boundG (-(m : Int)) (n : Int) = bndG (m + n) := by
  unfold boundG bndG
  rw [show ((n : Int) - -(m : Int)).toNat = m + n by omega]

section
variable {tbl : List Quint} {q₀ q₁ q₂ sg : Nat}

/-- **16 類の有界停止**（任意の表の正規形）。 -/
theorem okG_bound (H : RTM32 tbl q₀ q₁ q₂ sg)
    (hok : grpG (absCodes q₀ q₁ q₂ sg tbl) (absDirs q₀ q₁ q₂ tbl) = true) :
    ∀ (c : QConf) (m n : ℕ), -(m : ℤ) ≤ c.pos → c.pos ≤ (n : ℤ) →
      (∀ x, (x < -(m : ℤ) ∨ (n : ℤ) < x) → c.tape x = 0) → (∀ x, c.tape x < 2) →
      (QHalts (normT (tbl := tbl) (q₀ := q₀) (q₁ := q₁) (q₂ := q₂) (σ := sg)) c ↔
        qrun (normT (tbl := tbl) (q₀ := q₀) (q₁ := q₁) (q₂ := q₂) (σ := sg)) (bndG (m + n)) c = none) := by
  have hsrc := realize_src3 (absCodes q₀ q₁ q₂ sg tbl) (absDirs q₀ q₁ q₂ tbl)
  unfold grpG at hok
  have hb : ∀ (c : QConf) (a b : Int), a ≤ c.pos → c.pos ≤ b →
      (∀ x, (x < a ∨ b < x) → c.tape x = 0) →
      (QHalts (URTM.Three.realize (absCodes q₀ q₁ q₂ sg tbl) (absDirs q₀ q₁ q₂ tbl)) c ↔
        qrun (URTM.Three.realize (absCodes q₀ q₁ q₂ sg tbl) (absDirs q₀ q₁ q₂ tbl)) (boundG a b) c = none) := by
    rcases Bool.or_eq_true_iff.mp hok with h | h
    · exact sideG_bound hsrc h
    · exact sideG_mir_bound hsrc h
  intro c m n ha hb' hz _
  rw [← boundG_eq]
  exact hb c _ _ ha hb' hz

/-- **3 状態 2 記号の RTM の停止問題は、U の ID の上で計算可能**（`isExcG` の表を除く）。 -/
theorem three_halting_computable_G (H : RTM32 tbl q₀ q₁ q₂ sg)
    (hne : isExcG (absCodes q₀ q₁ q₂ sg tbl) (absDirs q₀ q₁ q₂ tbl) = false) :
    ∃ f : ZID → Bool, Computable f ∧
      ∀ z, (∀ a ∈ z.2.1 ++ z.2.2, a = 0 ∨ a ∈ [sg]) → (ZHalts tbl z ↔ f z = true) := by
  cases hF : isExcF (absCodes q₀ q₁ q₂ sg tbl) (absDirs q₀ q₁ q₂ tbl) with
  | false => exact three_halting_computable_F H hF
  | true =>
    have hG : grpG (absCodes q₀ q₁ q₂ sg tbl) (absDirs q₀ q₁ q₂ tbl) = true := by
      unfold isExcG at hne; rw [hF] at hne; simpa using hne
    exact halting_computable_of_bound H bndG_primrec (okG_bound H hG)

/-- **定理（段階 2e の 3）: `isExcG` の表を除き、3 状態 2 記号の URTM は存在しない**（Morita Def. 7.1、
    U の記号集合 {0, sg} の上の ID への符号化）。 -/
theorem no_three_two_URTM_G (H : RTM32 tbl q₀ q₁ q₂ sg)
    (hne : isExcG (absCodes q₀ q₁ q₂ sg tbl) (absDirs q₀ q₁ q₂ tbl) = false) :
    ¬ IsUTM_MoritaOver tbl [sg] :=
  not_UTM_of_halting_computable (three_halting_computable_G H hne)

end

/-! ### 残る例外の数

段階 2e の 2 の例外の上界 576 表（`excFKeys`）のうち、`grpG` に当たる 192 表（16 類）の鍵を一覧 `g192Keys` に書き、
それらが `grpG` に当たることを kernel で確かめる。残る例外はその外の 384 表に**含まれる**（上界）。 -/

/-- `grpG` に当たる 192 表の鍵（Python で生成。下の `g192_grpG` が kernel で検査する）。 -/
def g192Keys : List Nat := [
  244315, 247065, 287533, 290767, 292139, 292194, 292237, 292433, 292531, 292782, 292825, 297137,
  297486, 299881, 301939, 304689, 307629, 308603, 308658, 309191, 309344, 309393, 309540, 309638,
  311543, 311892, 316694, 318752, 328693, 331100, 345157, 347564, 708481, 711771, 722887, 727689,
  728578, 732457, 732471, 732487, 732489, 732493, 732499, 733354, 733378, 734899, 737293, 740583,
  742095, 742984, 749271, 749295, 750147, 750154, 750182, 750183, 750184, 750188, 752588, 754982,
  792523, 795806, 809323, 812606, 953273, 953567, 953665, 953721, 953763, 953837, 953851, 953855,
  953857, 953859, 953865, 953959, 954187, 954199, 954309, 954645, 1025359, 1025702, 1025882, 1025894,
  1025947, 1025996, 1026094, 1026136, 1026211, 1026218, 1026232, 1026235, 1026236, 1026238, 1026388, 1026724,
  2129763, 2130057, 2130155, 2130211, 2130253, 2130327, 2130341, 2130345, 2130347, 2130349, 2130355, 2130449,
  2130677, 2130689, 2130799, 2131135, 2201849, 2202192, 2202372, 2202384, 2202437, 2202486, 2202584, 2202626,
  2202701, 2202708, 2202722, 2202725, 2202726, 2202728, 2202878, 2203214, 2355567, 2358857, 2369973, 2374775,
  2375664, 2379543, 2379557, 2379573, 2379575, 2379579, 2379585, 2380440, 2380464, 2381985, 2384379, 2387669,
  2389181, 2390070, 2396357, 2396381, 2397233, 2397240, 2397268, 2397269, 2397270, 2397274, 2399674, 2402068,
  2439609, 2442892, 2456409, 2459692, 2832593, 2835343, 2875811, 2879045, 2880417, 2880472, 2880515, 2880711,
  2880809, 2881060, 2881103, 2885415, 2885764, 2888159, 2890217, 2892967, 2895907, 2896881, 2896936, 2897469,
  2897622, 2897671, 2897818, 2897916, 2899821, 2900170, 2904972, 2907030, 2916971, 2919378, 2933435, 2935842
]

theorem g192_grpG : g192Keys.all (fun k => grpG (unkey k).1 (unkey k).2) = true := by decide +kernel

theorem g192_sub : g192Keys.all (fun k => excFKeys.contains k) = true := by decide +kernel

/-- 段階 2e の 3 の例外の鍵（の上界）。 -/
def excGKeys : List Nat := excFKeys.filter fun k => !g192Keys.contains k

/-- **段階 2e の 3 の例外の表（の上界）の一覧**。 -/
def excGTables : List (List Nat × List Dir) := excGKeys.map unkey

/-- **主定理の仮定が外れる表は一覧に載る**（符号 6 つ・向き 3 つの表について）。 -/
theorem mem_excGTables {es : List Nat} {D : List Dir} (h : ValidKey es D) (hx : isExcG es D = true) :
    (es, D) ∈ excGTables := by
  unfold isExcG at hx
  obtain ⟨hF, hG⟩ := Bool.and_eq_true_iff.mp hx
  obtain ⟨k, hk, he⟩ := List.mem_map.mp (mem_excFTables h hF)
  refine List.mem_map.mpr ⟨k, List.mem_filter.mpr ⟨hk, ?_⟩, he⟩
  cases hc : g192Keys.contains k
  · rfl
  · exfalso
    have := List.all_eq_true.mp g192_grpG k (List.contains_iff_mem.mp hc)
    rw [he] at this
    simp only [this, Bool.not_true] at hG
    exact Bool.false_ne_true hG

/-- **段階 2e の 3 の例外は高々 384 表**（576 − 192。kernel の評価）。 -/
theorem excGKeys_length : excGKeys.length = 384 := by decide +kernel

theorem excGTables_length : excGTables.length = 384 := by
  unfold excGTables; rw [List.length_map, excGKeys_length]

end URTM.Meta
