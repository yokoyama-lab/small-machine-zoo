/-
  3 状態 2 記号の URTM（段階 2e の 7）: **群 D のうち、入る状態が 2 つで右のセルが「period-doubling 型」の 4 類**
  （class 16, 17, 24, 25、48 表）。**手書き**。

  向き: 開いている側を右にそろえる。右へ動いて入る状態は r1, r2（要求）、訪問はいつも z で戻る。**セルの規則**（`CellP`）:
  (r1,0) → (1, L, z)、(r1,1) → (f', R, r2)、(r2,1) → (f', R, r1)、(z,f') → (0, L, z)、(r2,0) は規則無し（止まる）。
  セルは「中身 0 に r1 なら中身 1 にして戻る、r2 なら止まる。中身 1 なら中身 0 にして、要求を入れ替えて右へ送る」変換器。
  空白から始まるカスケードが受け付け続ける要求の列はただ 1 つで、period-doubling 列 p（`pdw`: p_{2i} = r1、p_{2i+1} = p_i の入れ替え）。
  訪問 n の要求が p_n なら z で戻り、そうでなければ止まる（`cellP_visit`）。
  訪問は z でしか戻らないので、窓は右から情報を受け取らない: 訪問の始まりの (窓のテープ, 入る状態) の列は 1 文字の自動機械の軌道で、
  前周期 a と周期 q の和は状態の数以下（鳩の巣）。p は周期的でなく、周期 q = 2^s·r（r 奇数）なら n+1 ≡ 2^{s+1} (mod 2^{s+2}) の n で
  p_n ≠ p_{n+q}（`pdw_break`）。よって止まるなら訪問は a + 5q 回未満、ヘッドは b + 5·|状態| 以下（`right_boundK`）。
-/
import URTMMeta.ThreeJ
import Mathlib.Tactic.Ring

namespace URTM.Meta
open URTM URTM.TwoState URTM.Three

/-! ### セルの規則 -/

/-- 右側の period-doubling 型のセルの規則（上の説明）。 -/
structure CellP (tbl : List Quint) (z r1 r2 f' : Nat) : Prop where
  hP1 : find? tbl r1 0 = some ⟨r1, 0, 1, Dir.L, z⟩
  hP2 : find? tbl r1 1 = some ⟨r1, 1, f', Dir.R, r2⟩
  hP3 : find? tbl r2 1 = some ⟨r2, 1, f', Dir.R, r1⟩
  hP4 : find? tbl z f' = some ⟨z, f', 0, Dir.L, z⟩
  hP5 : find? tbl r2 0 = none
  hent : ∀ ρ ∈ tbl, ρ.d = Dir.R → ρ.q = r1 ∨ ρ.q = r2

/-! ### period-doubling 列 -/

/-- 受け付け続ける要求の列（true は r1、false は r2）: p_{2i} = true、p_{2i+1} = ¬ p_i。 -/
def pdw (n : Nat) : Bool :=
  if n % 2 = 0 then true else !pdw (n / 2)
termination_by n
decreasing_by omega

theorem pdw_even {n : Nat} (h : n % 2 = 0) : pdw n = true := by
  rw [pdw, if_pos h]

theorem pdw_odd {n : Nat} (h : n % 2 = 1) : pdw n = !pdw (n / 2) := by
  rw [pdw, if_neg (by omega)]

/-- **p は周期的でない**: n + 1 = 2^{s+1}(2j+1)、r が奇数なら p_n ≠ p_{n + 2^s r}。 -/
theorem pdw_break : ∀ s N j r, N + 1 = 2 ^ (s + 1) * (2 * j + 1) → r % 2 = 1 → pdw N ≠ pdw (N + 2 ^ s * r)
  | 0, N, j, r, hN, hr => by
    simp only [Nat.zero_add, pow_one, pow_zero, Nat.one_mul] at hN ⊢
    rw [pdw_odd (by omega), pdw_even (show (N / 2) % 2 = 0 by omega), pdw_even (by omega)]
    decide
  | s + 1, N, j, r, hN, hr => by
    obtain ⟨X, hX⟩ : ∃ X, X = 2 ^ (s + 1) * (2 * j + 1) := ⟨_, rfl⟩
    obtain ⟨Y, hY⟩ : ∃ Y, Y = 2 ^ s * r := ⟨_, rfl⟩
    have hX1 : 1 ≤ X := by rw [hX]; exact Nat.mul_pos (Nat.two_pow_pos _) (by omega)
    have e1 : 2 ^ (s + 1 + 1) * (2 * j + 1) = 2 * X := by rw [hX, pow_succ]; ring
    have e2 : 2 ^ (s + 1) * r = 2 * Y := by rw [hY, pow_succ]; ring
    rw [e1] at hN
    rw [e2, pdw_odd (n := N) (by omega), pdw_odd (n := N + 2 * Y) (by omega)]
    have ih := pdw_break s (N / 2) j r (by rw [← hX]; omega) hr
    rw [← hY] at ih
    rw [show (N + 2 * Y) / 2 = N / 2 + Y by omega]
    intro h
    exact ih (by simpa using h)

/-- 2 進分解: 1 以上の q は 2^s · (奇数)。 -/
theorem two_pow_mul_odd : ∀ q, 1 ≤ q → ∃ s r, r % 2 = 1 ∧ q = 2 ^ s * r := by
  intro q
  induction q using Nat.strong_induction_on with
  | _ q ih =>
  intro hq
  rcases Nat.mod_two_eq_zero_or_one q with h | h
  · obtain ⟨s, r, hr, he⟩ := ih (q / 2) (by omega) (by omega)
    refine ⟨s + 1, r, hr, ?_⟩
    rw [pow_succ, Nat.mul_assoc, Nat.mul_comm 2 r, ← Nat.mul_assoc, ← he]; omega
  · exact ⟨0, q, h, by simp⟩

/-- **どの長さ 4q の区間にも、周期 q の破れがある**。 -/
theorem pdw_break_in (a q : Nat) (hq : 1 ≤ q) : ∃ x, a ≤ x ∧ x < a + 4 * q ∧ pdw x ≠ pdw (x + q) := by
  obtain ⟨s, r, hr1, hqr⟩ := two_pow_mul_odd q hq
  obtain ⟨P, hP⟩ : ∃ P, P = 2 ^ s := ⟨_, rfl⟩
  have hP1 : 1 ≤ P := by rw [hP]; exact Nat.one_le_two_pow
  have hPq : P ≤ q := by rw [hqr, ← hP]; exact Nat.le_mul_of_pos_right _ (by omega)
  have eH : ∀ j, 2 ^ (s + 1) * (2 * j + 1) = 4 * P * j + 2 * P := by
    intro j; rw [pow_succ, ← hP]; ring
  obtain ⟨j0, ρ, hρ, ha⟩ : ∃ j0 ρ, ρ < 4 * P ∧ a = 4 * P * j0 + ρ :=
    ⟨a / (4 * P), a % (4 * P), Nat.mod_lt _ (by omega), (Nat.div_add_mod a (4 * P)).symm⟩
  have hq' : q = P * r := by rw [hqr, hP]
  by_cases hρH : ρ + 1 ≤ 2 * P
  · refine ⟨4 * P * j0 + 2 * P - 1, by omega, by omega, ?_⟩
    have := pdw_break s (4 * P * j0 + 2 * P - 1) j0 r (by rw [eH]; omega) hr1
    rwa [← hP, ← hq'] at this
  · refine ⟨4 * P * (j0 + 1) + 2 * P - 1, ?_, ?_, ?_⟩
    · rw [Nat.mul_add]; omega
    · rw [Nat.mul_add]; omega
    · have := pdw_break s (4 * P * (j0 + 1) + 2 * P - 1) (j0 + 1) r (by rw [eH]; omega) hr1
      rwa [← hP, ← hq'] at this

/-! ### 訪問 -/

/-- 要求の状態（true は r1、false は r2）。 -/
def sP (r1 r2 : Nat) (s : Bool) : Nat := if s then r1 else r2

/-- n 回の要求（p の先頭 n 個）のあとの右の中身（セル k の記号）。 -/
def pcP : Nat → Nat → Nat
  | n, 0 => n % 2
  | n, k + 1 => pcP (n / 2) k

theorem pcP_zero : ∀ k, pcP 0 k = 0
  | 0 => rfl
  | k + 1 => pcP_zero k

theorem qstep_none_of_find {tbl : List Quint} {c : QConf} (h : find? tbl c.st (c.tape c.pos) = none) :
    qstep tbl c = none := by
  unfold qstep; rw [h]

section visitP
variable {tbl : List Quint} {z r1 r2 f' : Nat} (H : CellP tbl z r1 r2 f')
include H

theorem CellP.fwd (s : Bool) : find? tbl (sP r1 r2 s) 1 = some ⟨sP r1 r2 s, 1, f', Dir.R, sP r1 r2 (!s)⟩ := by
  cases s
  · exact H.hP3
  · exact H.hP2

/-- **カスケードの訪問**: 右の中身が `pcP n` のとき、要求 s で b+1 に入った訪問は、s = p_n なら z で b に戻り中身は `pcP (n+1)`、
    s ≠ p_n なら止まる。訪問中（止まるまで）のヘッドは b+1 から b+1+n。 -/
theorem cellP_visit : ∀ n (b : Int) (t : Int → Nat), rpart b t = pcP n → ∀ s : Bool,
    ∃ k, (∀ i, i < k → ∀ d, qrun tbl i ⟨sP r1 r2 s, b + 1, t⟩ = some d → b + 1 ≤ d.pos ∧ d.pos ≤ b + 1 + n) ∧
      (s = pdw n → ∃ t', qrun tbl k ⟨sP r1 r2 s, b + 1, t⟩ = some ⟨z, b, t'⟩ ∧
        (∀ x, x ≤ b → t' x = t x) ∧ rpart b t' = pcP (n + 1)) ∧
      (s ≠ pdw n → qrun tbl k ⟨sP r1 r2 s, b + 1, t⟩ = none) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro b t ht s
  have hx0 : t (b + 1) = n % 2 := by
    have := congrFun ht 0; simpa [rpart, pcP] using this
  have hpos0 : ∀ d, qrun tbl 0 ⟨sP r1 r2 s, b + 1, t⟩ = some d → b + 1 ≤ d.pos ∧ d.pos ≤ b + 1 + n := by
    intro d hd; simp only [qrun, Option.some.injEq] at hd; subst hd; simp only; omega
  rcases Nat.mod_two_eq_zero_or_one n with hev | hod
  · -- 中身 0
    have hp := pdw_even hev
    cases s with
    | false =>
      -- r2 は止まる
      refine ⟨1, fun i hi d hd => by obtain rfl : i = 0 := (by omega); exact hpos0 d hd, fun h => by
        rw [hp] at h; exact absurd h (by decide), fun _ => ?_⟩
      rw [qrun_succ_none tbl 0 (qstep_none_of_find (by simp only; rw [hx0, hev]; exact H.hP5))]
    | true =>
      refine ⟨1, fun i hi d hd => by obtain rfl : i = 0 := (by omega); exact hpos0 d hd, fun _ => ?_,
        fun h => absurd hp.symm h⟩
      refine ⟨write t (b + 1) 1, ?_, fun x hx' => write_off _ _ _ (by omega), ?_⟩
      · rw [qrun_succ_some tbl 0 (qstep_of_find (by simp only; rw [hx0, hev]; exact H.hP1))]
        show some (⟨z, move Dir.L (b + 1), write t (b + 1) 1⟩ : QConf) = some (⟨z, b, write t (b + 1) 1⟩ : QConf)
        simp [move]
      · funext k
        cases k with
        | zero =>
          show write t (b + 1) 1 (b + 1 + ((0 : Nat) : Int)) = pcP (n + 1) 0
          simp only [pcP, write]; simp; omega
        | succ k =>
          show write t (b + 1) 1 (b + 1 + ((k + 1 : Nat) : Int)) = pcP (n + 1) (k + 1)
          rw [write_off _ _ _ (by omega)]
          have := congrFun ht (k + 1)
          simp only [rpart] at this
          rw [this]
          show pcP (n / 2) k = pcP ((n + 1) / 2) k
          rw [show (n + 1) / 2 = n / 2 by omega]
  · -- 中身 1: 要求を入れ替えて右へ送る
    have hp := pdw_odd hod
    have hm : n / 2 < n := by omega
    have hs1 : qstep tbl ⟨sP r1 r2 s, b + 1, t⟩ = some ⟨sP r1 r2 (!s), b + 1 + 1, write t (b + 1) f'⟩ := by
      rw [qstep_of_find (by simp only; rw [hx0, hod]; exact H.fwd s)]; rfl
    have e1 : qrun tbl 1 ⟨sP r1 r2 s, b + 1, t⟩ = some ⟨sP r1 r2 (!s), b + 1 + 1, write t (b + 1) f'⟩ := by
      rw [qrun_succ_some tbl 0 hs1]; rfl
    have hr1 : rpart (b + 1) (write t (b + 1) f') = pcP (n / 2) := by
      funext k
      show write t (b + 1) f' (b + 1 + 1 + k) = _
      rw [write_off _ _ _ (by omega)]
      have := congrFun ht (k + 1)
      simp only [rpart] at this
      rw [show b + 1 + 1 + (k : Int) = b + 1 + ((k + 1 : Nat) : Int) by push_cast; omega, this]
      rfl
    obtain ⟨k1, hpos1, hret1, hhalt1⟩ := ih (n / 2) hm (b + 1) _ hr1 (!s)
    have hiff : s = pdw n ↔ (!s) = pdw (n / 2) := by
      rw [hp]; cases s <;> cases pdw (n / 2) <;> decide
    by_cases hs : s = pdw n
    · obtain ⟨t2, hrun1, hag1, hr2⟩ := hret1 (hiff.mp hs)
      have ht2 : t2 (b + 1) = f' := by rw [hag1 _ le_rfl]; simp [write]
      have hs2 : qstep tbl ⟨z, b + 1, t2⟩ = some ⟨z, b, write t2 (b + 1) 0⟩ := by
        rw [qstep_of_find (by simp only; rw [ht2]; exact H.hP4)]
        show some (⟨z, b + 1 - 1, _⟩ : QConf) = _
        rw [show b + 1 - 1 = b by omega]
      have e2 : qrun tbl 1 ⟨z, b + 1, t2⟩ = some ⟨z, b, write t2 (b + 1) 0⟩ := by
        rw [qrun_succ_some tbl 0 hs2]; rfl
      refine ⟨1 + (k1 + 1), ?_, fun _ => ⟨write t2 (b + 1) 0, ?_, ?_, ?_⟩, fun h => absurd hs h⟩
      · intro i hi d hd
        rcases Nat.eq_zero_or_pos i with h0 | hpos
        · subst h0; exact hpos0 d hd
        · obtain ⟨i', rfl⟩ : ∃ i', i = 1 + i' := ⟨i - 1, by omega⟩
          rw [qrun_add, e1, Option.bind_some] at hd
          rcases Nat.lt_or_ge i' k1 with hlt | hge
          · have := hpos1 i' hlt d hd; constructor <;> omega
          · obtain rfl : i' = k1 := by omega
            rw [hrun1] at hd
            simp only [Option.some.injEq] at hd
            subst hd; simp only; omega
      · rw [qrun_add, e1, Option.bind_some, qrun_add, hrun1, Option.bind_some, e2]
      · intro x hxb
        rw [write_off _ _ _ (by omega), hag1 x (by omega), write_off _ _ _ (by omega)]
      · funext k
        cases k with
        | zero =>
          show write t2 (b + 1) 0 (b + 1 + ((0 : Nat) : Int)) = pcP (n + 1) 0
          simp only [pcP, write]; simp; omega
        | succ k =>
          show write t2 (b + 1) 0 (b + 1 + ((k + 1 : Nat) : Int)) = pcP (n + 1) (k + 1)
          rw [write_off _ _ _ (by omega)]
          have := congrFun hr2 k
          simp only [rpart] at this
          rw [show b + 1 + ((k + 1 : Nat) : Int) = b + 1 + 1 + (k : Int) by push_cast; omega, this]
          show pcP (n / 2 + 1) k = pcP ((n + 1) / 2) k
          rw [show (n + 1) / 2 = n / 2 + 1 by omega]
    · have hh := hhalt1 (fun h => hs (hiff.mpr h))
      refine ⟨1 + k1, ?_, fun h => absurd h hs, fun _ => ?_⟩
      · intro i hi d hd
        rcases Nat.eq_zero_or_pos i with h0 | hpos
        · subst h0; exact hpos0 d hd
        · obtain ⟨i', rfl⟩ : ∃ i', i = 1 + i' := ⟨i - 1, by omega⟩
          rw [qrun_add, e1, Option.bind_some] at hd
          have := hpos1 i' (by omega) d hd; constructor <;> omega
      · rw [qrun_add, e1, Option.bind_some, hh]

end visitP

/-! ### 窓の自動機械（入る状態つき、文字は z の 1 つだけ） -/

/-- 自動機械の状態: none = 止まった、some none = 使わない、some (some (τ, s)) = 訪問の始まりの窓のテープと入る状態（s = true は r1）。 -/
abbrev WK (lo b : Int) := Option (Option ((Fin (wW lo b) → Bool) × Bool))

/-- 出来事の結果（入る状態つき）。 -/
def wresK (r1 : Nat) (lo b : Int) : Option QConf → WK lo b
  | none => none
  | some d' => some (some (wenc lo b d'.tape, decide (d'.st = r1)))

open Classical in
/-- 窓の中の段（入る状態つき）。 -/
noncomputable def phaseK (tbl : List Quint) (r1 : Nat) (lo b : Int) (d : QConf) : WK lo b :=
  if hE : ∃ t, wev tbl b d t then wresK r1 lo b (qrun tbl (Nat.find hE + 1) d) else some none

/-- 自動機械の遷移: 訪問はいつも z で戻るので、次の段は窓のテープだけで決まる。 -/
noncomputable def wdeltaK (tbl : List Quint) (r1 z : Nat) (lo b : Int) : WK lo b → WK lo b
  | none => none
  | some none => some none
  | some (some (τ, _)) => phaseK tbl r1 lo b ⟨z, b, wdec lo b τ⟩

/-- **段の結果は切り詰めで決まる**（`phase_cut` の写し）。 -/
theorem phaseK_cut {tbl : List Quint} {b : Int} {r1 : Nat} {lo : Int} {d d' : QConf} (hc : cut b d = cut b d')
    (hp : d.pos ≤ b) : phaseK tbl r1 lo b d = phaseK tbl r1 lo b d' := by
  classical
  have hp' : d'.pos ≤ b := by obtain ⟨-, hpp, -⟩ := cut_eq b hc; rw [← hpp]; exact hp
  have hiff : (∃ t, wev tbl b d t) ↔ (∃ t, wev tbl b d' t) := by
    constructor
    · intro hE
      refine ⟨Nat.find hE, (wev_cut (tbl := tbl) hc hp _ (fun s hs => Nat.find_min hE hs)).mp (Nat.find_spec hE)⟩
    · intro hE
      refine ⟨Nat.find hE, (wev_cut (tbl := tbl) hc.symm hp' _ (fun s hs => Nat.find_min hE hs)).mp (Nat.find_spec hE)⟩
  unfold phaseK
  by_cases hE : ∃ t, wev tbl b d t
  · have hE' := hiff.mp hE
    rw [dif_pos hE, dif_pos hE']
    have hfind : Nat.find hE' = Nat.find hE := by
      rw [Nat.find_eq_iff]
      refine ⟨(wev_cut (tbl := tbl) hc hp _ (fun s hs => Nat.find_min hE hs)).mp (Nat.find_spec hE),
        fun s hs h' => Nat.find_min hE hs ?_⟩
      exact (wev_cut (tbl := tbl) hc hp s (fun r hr => Nat.find_min hE (by omega))).mpr h'
    rw [hfind]
    obtain ⟨e, e', h1, h2, hce, hpe⟩ := run_cut (tbl := tbl) hc hp (Nat.find hE) (fun s hs => Nat.find_min hE hs)
    have hq1 : qrun tbl (Nat.find hE + 1) d = qstep tbl e := by rw [qrun_succ_right, h1]; rfl
    have hq2 : qrun tbl (Nat.find hE + 1) d' = qstep tbl e' := by rw [qrun_succ_right, h2]; rfl
    rw [hq1, hq2]
    obtain ⟨hn, hs⟩ := step_cut (tbl := tbl) hce hpe
    cases he1 : qstep tbl e with
    | none => rw [hn.mp he1]
    | some e1 =>
      obtain ⟨e1', he1', hc1⟩ := hs e1 he1
      rw [he1']
      obtain ⟨hst, -, htp⟩ := cut_eq b hc1
      show some (some (wenc lo b e1.tape, decide (e1.st = r1))) = some (some (wenc lo b e1'.tape, decide (e1'.st = r1)))
      rw [hst]
      congr 3; funext i
      unfold wenc
      have hi := i.isLt
      unfold wW at hi
      rw [htp _ (by omega)]
  · rw [dif_neg hE, dif_neg (fun h => hE (hiff.mpr h))]

/-! ### 実行との対応 -/

section chainK
variable {tbl : List Quint} {z r1 r2 f' : Nat} (H : CellP tbl z r1 r2 f')
  {c0 : QConf} {T : Nat} (hR : QHaltRun tbl c0 T) {lo b : Int}
  (hzero : ∀ t, t ≤ T → ∀ x, x < lo → (qtr tbl c0 t).tape x = 0)
  (h2 : ∀ t, t ≤ T → ∀ x, (qtr tbl c0 t).tape x < 2)
include H hR hzero h2

/-- **実行と自動機械の対応**: 時刻 t0 に b 以下に居て右の中身が `pcP n` なら、ある V について、自動機械の軌道の先頭 V 個は
    どれも「入る状態が p_{n+i}」の訪問の始まりで（それらの訪問は z で戻る）、以後のヘッドは b+1+n+V 以下。 -/
theorem run_chainK : ∀ m t0 n, T - t0 = m → t0 ≤ T → (qtr tbl c0 t0).pos ≤ b →
    rpart b (qtr tbl c0 t0).tape = pcP n →
    ∃ V, (∀ i, i < V → ∃ τ, (wdeltaK tbl r1 z lo b)^[i] (phaseK tbl r1 lo b (qtr tbl c0 t0)) =
        some (some (τ, pdw (n + i)))) ∧
      ∀ t, t0 ≤ t → t ≤ T → (qtr tbl c0 t).pos ≤ b + 1 + n + V := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro t0 n hm ht0 hb0 hrp
  classical
  have hrun : ∀ s, t0 + s ≤ T → qrun tbl s (qtr tbl c0 t0) = some (qtr tbl c0 (t0 + s)) :=
    fun s hs => hR.run_mid t0 s hs
  have hdead : ∀ s, T < t0 + s → qrun tbl s (qtr tbl c0 t0) = none := by
    intro s hs
    exact qrun_none_mono tbl _ (T + 1 - t0) s (hR.run_from t0 ht0) (by omega)
  have hE : ∃ t, wev tbl b (qtr tbl c0 t0) t :=
    ⟨T - t0, by unfold wev; rw [hdead _ (by omega)]; trivial⟩
  obtain ⟨ts, hts⟩ : ∃ ts, ts = Nat.find hE := ⟨_, rfl⟩
  have hno : ∀ s, s < ts → ¬ wev tbl b (qtr tbl c0 t0) s := fun s hs => Nat.find_min hE (hts ▸ hs)
  have hbelow : ∀ s, s ≤ ts → t0 + s ≤ T ∧ (qtr tbl c0 (t0 + s)).pos ≤ b := by
    intro s hs
    rcases Nat.eq_zero_or_pos s with h0 | hpos
    · subst h0; exact ⟨by omega, hb0⟩
    · have h' := hno (s - 1) (by omega)
      unfold wev at h'
      rw [show s - 1 + 1 = s by omega] at h'
      by_cases hsT : t0 + s ≤ T
      · rw [hrun s hsT] at h'; exact ⟨hsT, by simp only at h'; omega⟩
      · rw [hdead s (by omega)] at h'; exact absurd trivial h'
  have hev : wev tbl b (qtr tbl c0 t0) ts := hts ▸ Nat.find_spec hE
  unfold wev at hev
  have hph : phaseK tbl r1 lo b (qtr tbl c0 t0) = wresK r1 lo b (qrun tbl (ts + 1) (qtr tbl c0 t0)) := by
    unfold phaseK; rw [dif_pos hE, ← hts]
  obtain ⟨hts1, hbts⟩ := hbelow ts le_rfl
  have hwin : ∀ t, t0 ≤ t → t ≤ t0 + ts → (qtr tbl c0 t).pos ≤ b := by
    intro t h1 h2'
    have := (hbelow (t - t0) (by omega)).2
    rwa [show t0 + (t - t0) = t by omega] at this
  by_cases hT : t0 + ts + 1 ≤ T
  · -- 訪問が始まる
    rw [hrun (ts + 1) (by omega)] at hev hph
    obtain ⟨t1, ht1⟩ : ∃ t1, t1 = t0 + ts := ⟨_, rfl⟩
    have ht1' : t0 + (ts + 1) = t1 + 1 := by omega
    rw [ht1'] at hev hph
    obtain ⟨ρ, hρ, _, e1⟩ := qstep_some (hR.step t1 (by omega))
    have hd : ρ.d = Dir.R := by
      cases hrd : ρ.d with
      | L => rw [e1, hrd] at hev; simp [move] at hev; have := hwin t1 (by omega) (by omega); omega
      | Z => rw [e1, hrd] at hev; simp [move] at hev; have := hwin t1 (by omega) (by omega); omega
      | R => rfl
    have hpos1 : (qtr tbl c0 (t1 + 1)).pos = b + 1 := by
      have hb1 := hwin t1 (by omega) (by omega)
      have := hev; rw [e1, hd] at this ⊢; simp [move] at this ⊢; omega
    have hst1 : (qtr tbl c0 (t1 + 1)).st = r1 ∨ (qtr tbl c0 (t1 + 1)).st = r2 := by
      rw [e1]; exact H.hent ρ hρ hd
    obtain ⟨s, hs_def⟩ : ∃ s : Bool, s = decide ((qtr tbl c0 (t1 + 1)).st = r1) := ⟨_, rfl⟩
    have hsP : (qtr tbl c0 (t1 + 1)).st = sP r1 r2 s := by
      by_cases h : (qtr tbl c0 (t1 + 1)).st = r1
      · have : s = true := by rw [hs_def]; exact decide_eq_true h
        rw [this]; exact h
      · have : s = false := by rw [hs_def]; exact decide_eq_false h
        rw [this]; exact hst1.resolve_left h
    have hq1 : qtr tbl c0 (t1 + 1) = ⟨sP r1 r2 s, b + 1, (qtr tbl c0 (t1 + 1)).tape⟩ := by
      rw [← hsP, ← hpos1]
    have hphs : phaseK tbl r1 lo b (qtr tbl c0 t0) = some (some (wenc lo b (qtr tbl c0 (t1 + 1)).tape, s)) := by
      rw [hph, hs_def]; rfl
    have hrp1 : rpart b (qtr tbl c0 (t1 + 1)).tape = pcP n := by
      have := rpart_const hR b (t0 := t0) (ts + 1) (by omega) (fun u h1 h2' => hwin u h1 (by omega))
      rw [ht1'] at this; rw [this]; exact hrp
    obtain ⟨k, hvpos, hret, hhalt⟩ := cellP_visit H n b _ hrp1 s
    have hvpos' : ∀ t, t1 + 1 ≤ t → t < t1 + 1 + k → t ≤ T → (qtr tbl c0 t).pos ≤ b + 1 + n := by
      intro t h1 h2' h3
      have hr1 : qrun tbl (t - (t1 + 1)) ⟨sP r1 r2 s, b + 1, (qtr tbl c0 (t1 + 1)).tape⟩ = some (qtr tbl c0 t) := by
        rw [← hq1, hR.run_at (by omega)]; congr 1; congr 1; omega
      exact (hvpos (t - (t1 + 1)) (by omega) _ hr1).2
    by_cases hs : s = pdw n
    · obtain ⟨t', hvis, hag, hr'⟩ := hret hs
      rw [← hq1] at hvis
      obtain ⟨hkT, hq2⟩ := qtr_of_run hR (by omega) hvis
      obtain ⟨V', hV1, hV3⟩ := ih (T - (t1 + 1 + k)) (by omega) (t1 + 1 + k) (n + 1) rfl hkT
        (by rw [hq2]) (by rw [hq2]; exact hr')
      have hstep : wdeltaK tbl r1 z lo b (phaseK tbl r1 lo b (qtr tbl c0 t0)) =
          phaseK tbl r1 lo b (qtr tbl c0 (t1 + 1 + k)) := by
        rw [hphs]
        show phaseK tbl r1 lo b ⟨z, b, wdec lo b (wenc lo b (qtr tbl c0 (t1 + 1)).tape)⟩ = _
        apply phaseK_cut _ (le_refl b)
        rw [hq2]
        refine cut_eq_of (c₁ := ⟨z, b, wdec lo b (wenc lo b (qtr tbl c0 (t1 + 1)).tape)⟩)
          (c₂ := ⟨z, b, t'⟩) b rfl rfl ?_
        intro x hx
        show wdec lo b (wenc lo b (qtr tbl c0 (t1 + 1)).tape) x = t' x
        rw [hag x hx]
        by_cases hxl : lo ≤ x
        · exact wdec_wenc (h2 (t1 + 1) (by omega)) hxl hx
        · rw [wdec_out (by omega), hzero (t1 + 1) (by omega) x (by omega)]
      refine ⟨V' + 1, ?_, ?_⟩
      · intro i hi
        rcases Nat.eq_zero_or_pos i with h0 | hpos
        · subst h0
          exact ⟨wenc lo b (qtr tbl c0 (t1 + 1)).tape, by rw [Function.iterate_zero_apply, hphs, hs]; rfl⟩
        · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
          rw [Function.iterate_succ_apply, hstep]
          obtain ⟨τ, hτ⟩ := hV1 i' (by omega)
          exact ⟨τ, by rw [hτ, show n + 1 + i' = n + (i' + 1) by omega]⟩
      · intro t htt0 htT
        by_cases hA : t ≤ t1
        · have := hwin t htt0 (by omega); omega
        · by_cases hB : t < t1 + 1 + k
          · have := hvpos' t (by omega) hB htT; omega
          · have := hV3 t (by omega) htT
            push_cast at this ⊢; omega
    · -- 右で止まる
      have hnone := hhalt hs
      rw [← hq1] at hnone
      refine ⟨0, fun i hi => absurd hi (by omega), ?_⟩
      intro t htt0 htT
      by_cases hA : t ≤ t1
      · have := hwin t htt0 (by omega); omega
      · have hlt : t < t1 + 1 + k := by
          by_contra hge
          have := qrun_none_mono tbl _ k (t - (t1 + 1)) hnone (by omega)
          rw [hR.run_at (by omega)] at this; cases this
        have := hvpos' t (by omega) hlt htT; omega
  · -- 窓の中で止まる
    refine ⟨0, fun i hi => absurd hi (by omega), ?_⟩
    intro t htt0 htT
    have := hwin t htt0 (by omega); omega

end chainK

/-! ### 右側の有界性 -/

/-- 窓の自動機械の状態の数（窓の幅 W）。 -/
def cardK (W : Nat) : Nat := 2 ^ W * 2 + 2

theorem card_WK (lo b : Int) : Fintype.card (WK lo b) = cardK (wW lo b) := by
  simp only [WK, Fintype.card_option, Fintype.card_prod, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin, cardK]

section rboundK
variable {tbl : List Quint} {z r1 r2 f' : Nat} (H : CellP tbl z r1 r2 f')
  {c0 : QConf} {T : Nat} (hR : QHaltRun tbl c0 T) {lo b : Int}
  (hzero : ∀ t, t ≤ T → ∀ x, x < lo → (qtr tbl c0 t).tape x = 0)
  (h2 : ∀ t, t ≤ T → ∀ x, (qtr tbl c0 t).tape x < 2)
include H hR hzero h2

/-- **右側の有界性（period-doubling 型のセル）**: 初め b より右が空白なら、止まる実行のヘッドは b + 5·cardK W 以下。
    自動機械の軌道は前周期 a・周期 q（a + q ≤ 状態の数）で繰り返し、戻った訪問の入る状態は p に沿うので、
    p の周期の破れ（`pdw_break_in`）から戻った訪問は a + 5q 回未満。 -/
theorem right_boundK (hb : c0.pos ≤ b) (hz : ∀ x, b < x → c0.tape x = 0) :
    ∀ t, t ≤ T → (qtr tbl c0 t).pos ≤ b + ((5 * cardK (wW lo b) : Nat) : Int) := by
  classical
  have hrp : rpart b (qtr tbl c0 0).tape = pcP 0 := by
    funext k
    show c0.tape (b + 1 + (k : Int)) = pcP 0 k
    rw [pcP_zero, hz _ (by omega)]
  obtain ⟨V, hV1, hV3⟩ := run_chainK H hR hzero h2 (T - 0) 0 0 rfl (Nat.zero_le _) hb hrp
  obtain ⟨x, y, hxy, hfxy⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun i : Fin (Fintype.card (WK lo b) + 1) => (wdeltaK tbl r1 z lo b)^[i.val] (phaseK tbl r1 lo b (qtr tbl c0 0)))
    (by rw [Fintype.card_fin]; omega)
  obtain ⟨i, j, hij, hjC, hpe⟩ : ∃ i j, i < j ∧ j ≤ Fintype.card (WK lo b) ∧
      (wdeltaK tbl r1 z lo b)^[i] (phaseK tbl r1 lo b (qtr tbl c0 0)) =
        (wdeltaK tbl r1 z lo b)^[j] (phaseK tbl r1 lo b (qtr tbl c0 0)) := by
    rcases Nat.lt_or_gt_of_ne (fun e => hxy (Fin.ext e)) with hl | hl
    · exact ⟨x.val, y.val, hl, by omega, hfxy⟩
    · exact ⟨y.val, x.val, hl, by omega, hfxy.symm⟩
  have hper : ∀ t, (wdeltaK tbl r1 z lo b)^[i + t] (phaseK tbl r1 lo b (qtr tbl c0 0)) =
      (wdeltaK tbl r1 z lo b)^[j + t] (phaseK tbl r1 lo b (qtr tbl c0 0)) := by
    intro t
    rw [Nat.add_comm i t, Nat.add_comm j t, Function.iterate_add_apply, Function.iterate_add_apply, hpe]
  have hVb : V < i + 5 * (j - i) := by
    by_contra hge
    obtain ⟨x, hx1, hx2, hne⟩ := pdw_break_in i (j - i) (by omega)
    obtain ⟨τ1, h1⟩ := hV1 x (by omega)
    obtain ⟨τ2, h2'⟩ := hV1 (x + (j - i)) (by omega)
    have e := hper (x - i)
    rw [show i + (x - i) = x by omega, show j + (x - i) = x + (j - i) by omega] at e
    rw [← e, h1] at h2'
    simp only [Nat.zero_add, Option.some.injEq, Prod.mk.injEq] at h2'
    exact hne h2'.2
  rw [card_WK] at hjC
  intro t ht
  have := hV3 t (Nat.zero_le _) ht
  have hV5 : V < 5 * cardK (wW lo b) := by omega
  omega

end rboundK

/-- 右の上界（窓 [a − ML, b] の自動機械の状態の数で決まる）。 -/
def mrK (ML : Nat) (a b : Int) : Nat := 5 * cardK ((b - a + ML + 1).toNat)

/-- **有界停止**（右が period-doubling 型のセル、左が段階 1 の証明書）。 -/
theorem halts_iff_boundK {tbl : List Quint} (hsrc : Src3 tbl) (hcl : QClosed tbl 2) (hdir : DirConsistent tbl)
    {z r1 r2 f' : Nat} (H : CellP tbl z r1 r2 f')
    {CL : List (List Nat)} {ML : Nat} (hLc : closedR (mirTbl tbl) CL ML = true)
    (c : QConf) (a b : Int) (ha : a ≤ c.pos) (hb : c.pos ≤ b)
    (hz : ∀ x, (x < a ∨ b < x) → c.tape x = 0) (h2 : ∀ x, c.tape x < 2) :
    QHalts tbl c ↔ qrun tbl (bound3 (mrK ML a b) ML a b) c = none := by
  constructor
  · intro hH
    obtain ⟨T, hR⟩ := qhalts_haltRun hH
    have hl := left_bound hR hdir hLc a ha (fun x hx => hz x (Or.inl hx))
    have hzero : ∀ t, t ≤ T → ∀ x, x < a - ML → (qtr tbl c t).tape x = 0 := by
      intro t ht x hx
      have := hR.cell_frozen x 0 t (by omega) (fun u _ h2' he => by
        have h1 := hl u (by omega)
        unfold QP at he; rw [he] at h1; omega)
      rw [Nat.zero_add] at this
      rw [this]; exact hz x (Or.inl (by omega))
    have hr := right_boundK H hR hzero (fun t ht => hR.tape_lt hcl h2 t ht) hb (fun x hx => hz x (Or.inr hx))
    have hW : wW (a - ML) b = (b - a + ML + 1).toNat := by unfold wW; congr 1; omega
    rw [hW] at hr
    exact bound_of_window hsrc hcl hR (mrK ML a b) ML a b hz h2 hl hr
  · intro h; exact ⟨_, h⟩

/-! ### Bool の検査 -/

/-- period-doubling 型のセルの規則が、戻りの状態 z・要求の状態 r1, r2 と f' で立つ。 -/
def cellPWith (tbl : List Quint) (z r1 r2 f' : Nat) : Bool :=
  decide (find? tbl r1 0 = some ⟨r1, 0, 1, Dir.L, z⟩) && decide (find? tbl r1 1 = some ⟨r1, 1, f', Dir.R, r2⟩) &&
  decide (find? tbl r2 1 = some ⟨r2, 1, f', Dir.R, r1⟩) && decide (find? tbl z f' = some ⟨z, f', 0, Dir.L, z⟩) &&
  decide (find? tbl r2 0 = none) &&
  tbl.all fun ρ => decide (ρ.d = Dir.R → ρ.q = r1 ∨ ρ.q = r2)

/-- **period-doubling 型のセルの規則の検査**（(z, r1, r2) の 6 通りと f'）。 -/
def cellPChk (tbl : List Quint) : Bool :=
  cell2Roles.any fun r => [0, 1].any fun f' => cellPWith tbl r.1 r.2.1 r.2.2 f'

theorem cellPWith_spec {tbl : List Quint} {z r1 r2 f' : Nat} (h : cellPWith tbl z r1 r2 f' = true) :
    CellP tbl z r1 r2 f' := by
  unfold cellPWith at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, hent⟩ := h
  exact ⟨h1, h2, h3, h4, h5, fun ρ hρ hd => hent ρ hρ hd⟩

theorem cellPChk_spec {tbl : List Quint} (h : cellPChk tbl = true) : ∃ z r1 r2 f', CellP tbl z r1 r2 f' := by
  unfold cellPChk at h
  simp only [List.any_eq_true] at h
  obtain ⟨r, -, f', -, hw⟩ := h
  exact ⟨_, _, _, _, cellPWith_spec hw⟩

/-- 右に period-doubling 型のセル、左に段階 1 の証明書が立つ。 -/
def sideK (tbl : List Quint) : Bool := cellPChk tbl && checkR (mirTbl tbl)

/-- **群 D の period-doubling 型の 4 類の検査**: 表か、その鏡像が `sideK`。 -/
def grpK (es : List Nat) (D : List Dir) : Bool :=
  sideK (URTM.Three.realize es D) || sideK (mirTbl (URTM.Three.realize es D))

/-- 段階 2e の 7 の例外: `isExcJ` の表のうち、この 4 類に当たらない表。 -/
def isExcK (es : List Nat) (D : List Dir) : Bool := isExcJ es D && !grpK es D

theorem sideK_bound {tbl : List Quint} (hsrc : Src3 tbl) (hcl : QClosed tbl 2) (hdir : DirConsistent tbl)
    (h : sideK tbl = true) :
    ∃ ML : Nat, ∀ (c : QConf) (a b : Int), a ≤ c.pos → c.pos ≤ b →
      (∀ x, (x < a ∨ b < x) → c.tape x = 0) → (∀ x, c.tape x < 2) →
      (QHalts tbl c ↔ qrun tbl (bound3 (mrK ML a b) ML a b) c = none) := by
  unfold sideK at h
  obtain ⟨hc, hL⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨CL, ML, hLc⟩ := checkR_spec hL
  obtain ⟨z, r1, r2, f', H⟩ := cellPChk_spec hc
  exact ⟨ML, fun c a b ha hb hz h2 => halts_iff_boundK hsrc hcl hdir H hLc c a b ha hb hz h2⟩

theorem sideK_mir_bound {tbl : List Quint} (hsrc : Src3 tbl) (hcl : QClosed tbl 2) (hdir : DirConsistent tbl)
    (h : sideK (mirTbl tbl) = true) :
    ∃ ML : Nat, ∀ (c : QConf) (a b : Int), a ≤ c.pos → c.pos ≤ b →
      (∀ x, (x < a ∨ b < x) → c.tape x = 0) → (∀ x, c.tape x < 2) →
      (QHalts tbl c ↔ qrun tbl (bound3 (mrK ML a b) ML a b) c = none) := by
  rw [mirTbl_eq] at h
  obtain ⟨ML, hb⟩ := sideK_bound (src3_mir hsrc) (closed_mir hcl) (dirConsistent_mir hdir) h
  refine ⟨ML, fun c a b ha hb' hz h2 => ?_⟩
  have := hb (mirQ c) (-b) (-a) (by show -b ≤ -c.pos; omega) (by show -c.pos ≤ -a; omega)
    (fun x hx => by show c.tape (-x) = 0; exact hz (-x) (by omega)) (fun x => h2 (-x))
  rw [QHalts_mir, qrun_mir] at this
  have e1 : mrK ML (-b) (-a) = mrK ML a b := by
    unfold mrK; rw [show -a - -b + (ML : Int) + 1 = b - a + ML + 1 by omega]
  have e : bound3 (mrK ML a b) ML (-b) (-a) = bound3 (mrK ML a b) ML a b := by
    unfold bound3
    rw [show -a + ((mrK ML a b : Nat) : Int) - (-b - ML) + 1 = b + (mrK ML a b : Nat) - (a - ML) + 1 by omega]
  rw [e1, e] at this
  rw [this]
  cases qrun tbl (bound3 (mrK ML a b) ML a b) c <;> simp

/-- 窓の幅で書いた上界。 -/
def bndK (ML w : Nat) : Nat := bnd3N (5 * cardK (w + ML + 1)) ML w

theorem bndK_primrec (ML : Nat) : Primrec (bndK ML) := by
  have hc : Primrec cardK :=
    (Primrec.nat_add.comp (Primrec.nat_mul.comp (pow_primrec.comp (Primrec.const 2) Primrec.id)
      (Primrec.const 2)) (Primrec.const 2)).of_eq fun W => rfl
  have hMR : Primrec fun w : Nat => 5 * cardK (w + ML + 1) :=
    Primrec.nat_mul.comp (Primrec.const 5) (hc.comp
      (Primrec.nat_add.comp (Primrec.nat_add.comp Primrec.id (Primrec.const ML)) (Primrec.const 1)))
  exact (Primrec.nat_add.comp (csize_primrec.comp (Primrec.const 2)
    (Primrec.nat_add.comp (Primrec.nat_add.comp (Primrec.nat_add.comp Primrec.id hMR)
      (Primrec.const ML)) (Primrec.const 1))) (Primrec.const 1)).of_eq fun w => rfl

theorem boundK_eq (ML m n : Nat) :
    bound3 (mrK ML (-(m : Int)) (n : Int)) ML (-(m : Int)) (n : Int) = bndK ML (m + n) := by
  unfold bndK
  rw [← bound3_eq]
  congr 1
  unfold mrK
  rw [show ((n : Int) - -(m : Int) + ML + 1).toNat = m + n + ML + 1 by omega]

section
variable {tbl : List Quint} {q₀ q₁ q₂ sg : Nat}

/-- **4 類の有界停止**（任意の表の正規形）。 -/
theorem okK_bound (H : RTM32 tbl q₀ q₁ q₂ sg)
    (hok : grpK (absCodes q₀ q₁ q₂ sg tbl) (absDirs q₀ q₁ q₂ tbl) = true) :
    ∃ ML : Nat, ∀ (c : QConf) (m n : ℕ), -(m : ℤ) ≤ c.pos → c.pos ≤ (n : ℤ) →
      (∀ x, (x < -(m : ℤ) ∨ (n : ℤ) < x) → c.tape x = 0) → (∀ x, c.tape x < 2) →
      (QHalts (normT (tbl := tbl) (q₀ := q₀) (q₁ := q₁) (q₂ := q₂) (σ := sg)) c ↔
        qrun (normT (tbl := tbl) (q₀ := q₀) (q₁ := q₁) (q₂ := q₂) (σ := sg)) (bndK ML (m + n)) c
          = none) := by
  have hsrc := realize_src3 (absCodes q₀ q₁ q₂ sg tbl) (absDirs q₀ q₁ q₂ tbl)
  have hcl := realize_closed (absCodes q₀ q₁ q₂ sg tbl) (absDirs q₀ q₁ q₂ tbl)
  have hdir := realize_dir (absCodes q₀ q₁ q₂ sg tbl) (absDirs q₀ q₁ q₂ tbl)
  unfold grpK at hok
  obtain ⟨ML, hb⟩ : ∃ ML : Nat, ∀ (c : QConf) (a b : Int), a ≤ c.pos → c.pos ≤ b →
      (∀ x, (x < a ∨ b < x) → c.tape x = 0) → (∀ x, c.tape x < 2) →
      (QHalts (URTM.Three.realize (absCodes q₀ q₁ q₂ sg tbl) (absDirs q₀ q₁ q₂ tbl)) c ↔
        qrun (URTM.Three.realize (absCodes q₀ q₁ q₂ sg tbl) (absDirs q₀ q₁ q₂ tbl))
          (bound3 (mrK ML a b) ML a b) c = none) := by
    rcases Bool.or_eq_true_iff.mp hok with h | h
    · exact sideK_bound hsrc hcl hdir h
    · exact sideK_mir_bound hsrc hcl hdir h
  refine ⟨ML, fun c m n ha hb' hz h2 => ?_⟩
  rw [← boundK_eq]
  exact hb c _ _ ha hb' hz h2

/-- **3 状態 2 記号の RTM の停止問題は、U の ID の上で計算可能**（`isExcK` の表を除く）。 -/
theorem three_halting_computable_K (H : RTM32 tbl q₀ q₁ q₂ sg)
    (hne : isExcK (absCodes q₀ q₁ q₂ sg tbl) (absDirs q₀ q₁ q₂ tbl) = false) :
    ∃ f : ZID → Bool, Computable f ∧
      ∀ z, (∀ a ∈ z.2.1 ++ z.2.2, a = 0 ∨ a ∈ [sg]) → (ZHalts tbl z ↔ f z = true) := by
  cases hJ : isExcJ (absCodes q₀ q₁ q₂ sg tbl) (absDirs q₀ q₁ q₂ tbl) with
  | false => exact three_halting_computable_J H hJ
  | true =>
    have hK : grpK (absCodes q₀ q₁ q₂ sg tbl) (absDirs q₀ q₁ q₂ tbl) = true := by
      unfold isExcK at hne; rw [hJ] at hne; simpa using hne
    obtain ⟨ML, hb⟩ := okK_bound H hK
    exact halting_computable_of_bound H (bndK_primrec ML) hb

/-- **定理（段階 2e の 7）: `isExcK` の表を除き、3 状態 2 記号の URTM は存在しない**（Morita Def. 7.1、
    U の記号集合 {0, sg} の上の ID への符号化）。 -/
theorem no_three_two_URTM_K (H : RTM32 tbl q₀ q₁ q₂ sg)
    (hne : isExcK (absCodes q₀ q₁ q₂ sg tbl) (absDirs q₀ q₁ q₂ tbl) = false) :
    ¬ IsUTM_MoritaOver tbl [sg] :=
  not_UTM_of_halting_computable (three_halting_computable_K H hne)

end

/-! ### 残る例外の数

段階 2e の 6 の例外の上界 168 表（`excJKeys`）のうち、`grpK` に当たる 48 表（4 類）の鍵を一覧 `k48Keys` に書き、
それらが `grpK` に当たることを kernel で確かめる。残る例外はその外の 120 表に**含まれる**（上界）。 -/

/-- `grpK` に当たる 48 表の鍵（Python で生成。下の `k48_grpK` が kernel で検査する）。 -/
def k48Keys : List Nat := [
  287561, 287575, 292265, 292279, 304692, 304694, 309396, 309398, 723573, 724945, 733173, 734545,
  740632, 740828, 750232, 750428, 987181, 987469, 1020795, 1021083, 1028348, 1028636, 1033150, 1033438,
  2163671, 2163959, 2197285, 2197573, 2204838, 2205126, 2209640, 2209928, 2370659, 2372031, 2380259, 2381631,
  2387718, 2387914, 2397318, 2397514, 2875839, 2875853, 2880543, 2880557, 2892970, 2892972, 2897674, 2897676
]

theorem k48_grpK : k48Keys.all (fun k => grpK (unkey k).1 (unkey k).2) = true := by decide +kernel

theorem k48_sub : k48Keys.all (fun k => excJKeys.contains k) = true := by decide +kernel

/-- 段階 2e の 7 の例外の鍵（の上界）。 -/
def excKKeys : List Nat := excJKeys.filter fun k => !k48Keys.contains k

/-- **段階 2e の 7 の例外の表（の上界）の一覧**。 -/
def excKTables : List (List Nat × List Dir) := excKKeys.map unkey

/-- **主定理の仮定が外れる表は一覧に載る**（符号 6 つ・向き 3 つの表について）。 -/
theorem mem_excKTables {es : List Nat} {D : List Dir} (h : ValidKey es D) (hx : isExcK es D = true) :
    (es, D) ∈ excKTables := by
  unfold isExcK at hx
  obtain ⟨hJ, hK⟩ := Bool.and_eq_true_iff.mp hx
  obtain ⟨k, hk, he⟩ := List.mem_map.mp (mem_excJTables h hJ)
  refine List.mem_map.mpr ⟨k, List.mem_filter.mpr ⟨hk, ?_⟩, he⟩
  cases hc : k48Keys.contains k
  · rfl
  · exfalso
    have := List.all_eq_true.mp k48_grpK k (List.contains_iff_mem.mp hc)
    rw [he] at this
    simp only [this, Bool.not_true] at hK
    exact Bool.false_ne_true hK

/-- **段階 2e の 7 の例外は高々 120 表**（168 − 48。kernel の評価）。 -/
theorem excKKeys_length : excKKeys.length = 120 := by decide +kernel

theorem excKTables_length : excKTables.length = 120 := by
  unfold excKTables; rw [List.length_map, excKKeys_length]


end URTM.Meta
