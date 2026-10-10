/-
  3 状態 2 記号の URTM（段階 2d）: **群 D のうち「一様な反射板」8 類**（2 進カウンタ）。**手書き**。

  群 D（段階 2b の例外 68 類）のうち 8 類（96 表）では、片側（右とする。左は鏡像）が次の形をしている。
  * 右へ動く規則はどれも状態 e へ入る（`hent`）。窓の右端 b から b+1 へは e でしか出られない。
  * 3 本の規則 (e, 1) → (w, R, e)、(e, 0) → (1, L, r)、(r, w) → (0, L, r)（w は 0 か 1）。
  b+1 から右の中身が 1^j 0 v のとき、e で b+1 に入った実行は 2j+1 歩で状態 r・位置 b に戻り、中身は 0^j 1 v になる
  （`visit_counter`。中身を下位桁が先の 2 進数と読めば 1 を足す）。**どの中身でも同じ状態で戻り、途中で止まらない**。

  そこで、ヘッドが b 以下にある時刻（外の時刻）の配置を (−∞, b] に切り詰めたもの（`cut`）は、次の外の時刻の
  切り詰めを決める（`cut_next`）。止まる実行では外の時刻の切り詰めは繰り返さない（`no_repeat_cut`）。
  左側は段階 1 の証明書（`closedR (mirTbl tbl)`）で有界なので、切り詰めは有限個（窓 [a − ML, b] の配置）。
  よって外の時刻は高々 K = csize 2 W 個で、i 番目の外の時刻までに右の中身の長さは i 以下、各訪問は 2i+2 歩以内。
  止まるなら K(2K+2) 歩以内に止まる（`halts_iff_boundD`）。

  検査 `grpD es D`（Bool）: 表か鏡像の表が、左の証明書と上の 3 本の規則・入る向きの条件を満たす。
  例外 816 表のうち `grpD` に当たるのは 96 表（8 類）。主定理 `no_three_two_URTM_D`（`isExcD = isExcC && !grpD`）。
-/
import URTMMeta.ThreeExcCount

namespace URTM.Meta
open URTM URTM.TwoState URTM.Three

/-! ### カウンタの規則 -/

/-- 右側のカウンタの規則。 -/
structure Counter (tbl : List Quint) (e r w : Nat) : Prop where
  h1 : find? tbl e 1 = some ⟨e, 1, w, Dir.R, e⟩
  h0 : find? tbl e 0 = some ⟨e, 0, 1, Dir.L, r⟩
  hr : find? tbl r w = some ⟨r, w, 0, Dir.L, r⟩
  hent : ∀ ρ ∈ tbl, ρ.d = Dir.R → ρ.q = e

theorem qstep_of_find {tbl : List Quint} {c : QConf} {ρ : Quint} (h : find? tbl c.st (c.tape c.pos) = some ρ) :
    qstep tbl c = some ⟨ρ.q, move ρ.d c.pos, write c.tape c.pos ρ.t⟩ := by
  unfold qstep; rw [h]

section visit
variable {tbl : List Quint} {e r w : Nat} (H : Counter tbl e r w)
include H

/-- 往路: e で 1 の上を右へ（1 を w に書き換える）。 -/
theorem phase1 (pos : Int) (tape : Int → Nat) :
    ∀ i : Nat, (∀ k : Nat, k < i → tape (pos + k) = 1) →
      qrun tbl i ⟨e, pos, tape⟩ = some ⟨e, pos + i, fun x => if pos ≤ x ∧ x < pos + i then w else tape x⟩
  | 0, _ => by
    simp only [qrun, Nat.cast_zero, Int.add_zero, Option.some.injEq, QConf.mk.injEq, true_and]
    funext x; split_ifs <;> first | rfl | omega
  | i + 1, h => by
    rw [qrun_succ_right, phase1 pos tape i (fun k hk => h k (by omega))]
    simp only [Option.bind_some]
    have hread : (if pos ≤ pos + (i : Int) ∧ pos + (i : Int) < pos + i then w else tape (pos + i)) = 1 := by
      rw [if_neg (by omega)]; exact h i (by omega)
    rw [qstep_of_find (by simp only; rw [hread]; exact H.h1)]
    simp only [Option.some.injEq, QConf.mk.injEq, true_and, move]
    refine ⟨by push_cast; omega, ?_⟩
    funext x; simp only [write]; split_ifs <;> first | rfl | omega

/-- 復路: r で w の上を左へ（0 に書き換える）。 -/
theorem phase3 (pos : Int) (j : Nat) (t : Int → Nat) (ht : ∀ x, pos ≤ x → x < pos + j → t x = w) :
    ∀ i : Nat, i ≤ j →
      qrun tbl i ⟨r, pos + j - 1, t⟩ =
        some ⟨r, pos + j - 1 - i, fun x => if pos + j - i ≤ x ∧ x < pos + j then 0 else t x⟩
  | 0, _ => by
    simp only [qrun, Nat.cast_zero, Int.sub_zero, Option.some.injEq, QConf.mk.injEq, true_and]
    funext x; split_ifs <;> first | rfl | omega
  | i + 1, hi => by
    rw [qrun_succ_right, phase3 pos j t ht i (by omega)]
    simp only [Option.bind_some]
    have hread : (if pos + (j : Int) - i ≤ pos + j - 1 - i ∧ pos + j - 1 - i < pos + j then 0
        else t (pos + j - 1 - i)) = w := by
      rw [if_neg (by omega)]; exact ht _ (by omega) (by omega)
    rw [qstep_of_find (by simp only; rw [hread]; exact H.hr)]
    simp only [Option.some.injEq, QConf.mk.injEq, true_and, move]
    refine ⟨by push_cast; omega, ?_⟩
    funext x; simp only [write]; split_ifs <;> first | rfl | omega

/-- **訪問**: 中身 1^j 0 … に e で入ると、2j+1 歩で r・位置 pos − 1 に戻り、中身は 0^j 1 …。 -/
theorem visit_counter (pos : Int) (tape : Int → Nat) (j : Nat)
    (h1s : ∀ k : Nat, k < j → tape (pos + k) = 1) (h0 : tape (pos + j) = 0) :
    qrun tbl (2 * j + 1) ⟨e, pos, tape⟩ =
      some ⟨r, pos - 1, fun x => if pos ≤ x ∧ x < pos + j then 0 else if x = pos + j then 1 else tape x⟩ := by
  rw [show 2 * j + 1 = j + 1 + j by omega, qrun_add, qrun_add, phase1 H pos tape j h1s]
  simp only [Option.bind_some]
  have hread : (if pos ≤ pos + (j : Int) ∧ pos + (j : Int) < pos + j then w else tape (pos + j)) = 0 := by
    rw [if_neg (by omega)]; exact h0
  have hs : qrun tbl 1 ⟨e, pos + j, fun x => if pos ≤ x ∧ x < pos + j then w else tape x⟩ =
      some ⟨r, pos + j - 1, write (fun x => if pos ≤ x ∧ x < pos + j then w else tape x) (pos + j) 1⟩ := by
    rw [qrun_succ_some tbl 0 (qstep_of_find (by simp only; rw [hread]; exact H.h0))]
    simp [qrun, move]
  rw [hs]
  simp only [Option.bind_some]
  rw [phase3 H pos j _ (fun x h1 h2 => by simp only [write]; rw [if_neg (by omega), if_pos ⟨h1, h2⟩]) j le_rfl]
  simp only [Option.some.injEq, QConf.mk.injEq, true_and]
  refine ⟨by omega, ?_⟩
  funext x; simp only [write]; split_ifs <;> first | rfl | omega

end visit

/-! ### 外の時刻の列 -/

/-- (−∞, b] に切り詰めた配置。 -/
def cut (b : Int) (c : QConf) : QConf := ⟨c.st, c.pos, fun x => if x ≤ b then c.tape x else 0⟩

/-- b+1 から右で最初に 1 でないマスまでの距離。 -/
noncomputable def jOf (b : Int) (d : QConf) : Nat :=
  open Classical in if h : ∃ j : Nat, d.tape (b + 1 + j) ≠ 1 then Nat.find h else 0

theorem jOf_spec {b : Int} {d : QConf} {L : Nat} (hL : d.tape (b + 1 + L) = 0) :
    jOf b d ≤ L ∧ (∀ k : Nat, k < jOf b d → d.tape (b + 1 + k) = 1) ∧ d.tape (b + 1 + jOf b d) ≠ 1 := by
  classical
  have hex : ∃ j : Nat, d.tape (b + 1 + j) ≠ 1 := ⟨L, by rw [hL]; decide⟩
  have e : jOf b d = Nat.find hex := by unfold jOf; rw [dif_pos hex]
  rw [e]
  refine ⟨Nat.find_min' hex (by rw [hL]; decide), fun k hk => ?_, Nat.find_spec hex⟩
  have := Nat.find_min hex hk
  simpa using this

section run
variable {tbl : List Quint} {c : QConf} {T : Nat} (b : Int)

/-- 外の時刻 t から次の外の時刻までの歩数。 -/
noncomputable def mu (tbl : List Quint) (c : QConf) (t : Nat) : Nat :=
  if b < (qtr tbl c (t + 1)).pos then 2 * jOf b (qtr tbl c (t + 1)) + 2 else 1

/-- 外の時刻の列（止まる時刻 T に着いたら止める）。 -/
noncomputable def tau (tbl : List Quint) (c : QConf) (T : Nat) : Nat → Nat
  | 0 => 0
  | i + 1 => if tau tbl c T i < T then tau tbl c T i + mu b tbl c (tau tbl c T i) else tau tbl c T i

/-- 右の中身の長さが L 以下。 -/
def Supp (L : Nat) (d : QConf) : Prop := ∀ x, b + L < x → d.tape x = 0

theorem qtr_of_run {t n : Nat} {d : QConf} (hR : QHaltRun tbl c T) (ht : t ≤ T)
    (h : qrun tbl n (qtr tbl c t) = some d) : t + n ≤ T ∧ qtr tbl c (t + n) = d := by
  have hle : t + n ≤ T := by
    by_contra hc
    have := qrun_none_mono tbl _ _ n (hR.run_from t ht) (by omega)
    rw [h] at this; cases this
  refine ⟨hle, ?_⟩
  have := hR.run_mid t n hle
  rw [h] at this; exact (Option.some.inj this).symm

theorem qtr_zero : qtr tbl c 0 = c := rfl

theorem qstep_qtr_T (hR : QHaltRun tbl c T) : qstep tbl (qtr tbl c T) = none := by
  have h := hR.dead
  rw [qrun_succ_right, hR.run T le_rfl] at h
  exact h

/-- 切り詰めが等しい。 -/
theorem cut_eq {c₁ c₂ : QConf} (h : cut b c₁ = cut b c₂) :
    c₁.st = c₂.st ∧ c₁.pos = c₂.pos ∧ ∀ x, x ≤ b → c₁.tape x = c₂.tape x := by
  have h1 := congrArg QConf.st h
  have h2 := congrArg QConf.pos h
  have h3 := congrArg QConf.tape h
  refine ⟨h1, h2, fun x hx => ?_⟩
  have := congrFun h3 x
  simp only [cut, if_pos hx] at this
  exact this

theorem cut_eq_of {c₁ c₂ : QConf} (h1 : c₁.st = c₂.st) (h2 : c₁.pos = c₂.pos)
    (h3 : ∀ x, x ≤ b → c₁.tape x = c₂.tape x) : cut b c₁ = cut b c₂ := by
  unfold cut; rw [h1, h2]; congr 1; funext x; split_ifs with hx
  · exact h3 x hx
  · rfl

/-- 外の配置で切り詰めが等しいなら、読む規則は同じ。 -/
theorem find_eq_of_cut {c₁ c₂ : QConf} (h : cut b c₁ = cut b c₂) (hout : c₁.pos ≤ b) :
    find? tbl c₁.st (c₁.tape c₁.pos) = find? tbl c₂.st (c₂.tape c₂.pos) := by
  obtain ⟨h1, h2, h3⟩ := cut_eq b h
  rw [h1, ← h2, h3 _ hout]

section macroS
variable {e r w : Nat} (H : Counter tbl e r w) (hR : QHaltRun tbl c T)
  (htape : ∀ u, u ≤ T → ∀ x, (qtr tbl c u).tape x < 2)
include H hR htape

/-- **外の時刻の 1 歩（マクロの 1 歩）**。 -/
theorem macroStep {t L : Nat} (htT : t < T) (hout : (qtr tbl c t).pos ≤ b) (hsupp : Supp b L (qtr tbl c t)) :
    t + mu b tbl c t ≤ T ∧ (qtr tbl c (t + mu b tbl c t)).pos ≤ b ∧
      Supp b (L + 1) (qtr tbl c (t + mu b tbl c t)) ∧ mu b tbl c t ≤ 2 * L + 2 ∧
      ((b < (qtr tbl c (t + 1)).pos ∧ (qtr tbl c (t + mu b tbl c t)).st = r ∧
          (qtr tbl c (t + mu b tbl c t)).pos = b ∧
          ∀ x, x ≤ b → (qtr tbl c (t + mu b tbl c t)).tape x = (qtr tbl c (t + 1)).tape x) ∨
        ((qtr tbl c (t + 1)).pos ≤ b ∧ mu b tbl c t = 1)) := by
  obtain ⟨ρ, hρ, _, e1⟩ := qstep_some (hR.step t htT)
  have hsupp1 : Supp b L (qtr tbl c (t + 1)) := by
    intro x hxL
    rw [e1]; show write _ _ _ x = 0
    rw [write_off _ _ _ (by omega)]; exact hsupp x hxL
  by_cases hx : b < (qtr tbl c (t + 1)).pos
  · -- 訪問
    have hmu : mu b tbl c t = 2 * jOf b (qtr tbl c (t + 1)) + 2 := by unfold mu; rw [if_pos hx]
    have hd : ρ.d = Dir.R := by
      cases hrd : ρ.d with
      | L => rw [e1, hrd] at hx; simp [move] at hx; omega
      | Z => rw [e1, hrd] at hx; simp [move] at hx; omega
      | R => rfl
    have hpos : (qtr tbl c (t + 1)).pos = b + 1 := by
      have := hx; rw [e1, hd] at this ⊢; simp [move] at this ⊢; omega
    have hst : (qtr tbl c (t + 1)).st = e := by rw [e1]; exact H.hent ρ hρ hd
    obtain ⟨hjL, hj1, hj0⟩ := jOf_spec (b := b) (d := qtr tbl c (t + 1)) (L := L) (hsupp1 _ (by omega))
    set j := jOf b (qtr tbl c (t + 1)) with hjdef
    have hj0' : (qtr tbl c (t + 1)).tape (b + 1 + j) = 0 := by
      have := htape (t + 1) (by omega) (b + 1 + j); omega
    have hv := visit_counter H (b + 1) (qtr tbl c (t + 1)).tape j hj1 hj0'
    have hq : qtr tbl c (t + 1) = ⟨e, b + 1, (qtr tbl c (t + 1)).tape⟩ := by
      rw [← hst, ← hpos]
    rw [← hq] at hv
    obtain ⟨hle, hV⟩ := qtr_of_run hR (by omega) hv
    have ht : t + mu b tbl c t = t + 1 + (2 * j + 1) := by rw [hmu]; omega
    rw [ht, hV]
    refine ⟨by omega, by simp, fun x hxL => ?_, by omega, Or.inl ⟨hx, rfl, by simp, fun x hxb => ?_⟩⟩
    · simp only
      rw [if_neg (by omega), if_neg (by omega)]; exact hsupp1 x (by omega)
    · simp only
      rw [if_neg (by omega), if_neg (by omega)]
  · -- 窓の中
    have hmu : mu b tbl c t = 1 := by unfold mu; rw [if_neg hx]
    rw [hmu]
    exact ⟨by omega, by omega, fun x hxL => hsupp1 x (by omega), by omega, Or.inr ⟨by omega, rfl⟩⟩

/-- **切り詰めは次の外の時刻の切り詰めを決める**。 -/
theorem cut_next {t t' : Nat} (htT : t < T) (htT' : t' < T) (hout : (qtr tbl c t).pos ≤ b)
    (hout' : (qtr tbl c t').pos ≤ b) {L L' : Nat} (hsupp : Supp b L (qtr tbl c t))
    (hsupp' : Supp b L' (qtr tbl c t')) (hcut : cut b (qtr tbl c t) = cut b (qtr tbl c t')) :
    cut b (qtr tbl c (t + mu b tbl c t)) = cut b (qtr tbl c (t' + mu b tbl c t')) := by
  obtain ⟨ρ, _, hf, e1⟩ := qstep_some (hR.step t htT)
  obtain ⟨ρ', _, hf', e1'⟩ := qstep_some (hR.step t' htT')
  have hρ : ρ = ρ' := by
    rw [find_eq_of_cut b hcut hout, hf'] at hf; exact (Option.some.inj hf).symm
  subst hρ
  obtain ⟨hs, hp, htp⟩ := cut_eq b hcut
  -- 1 歩後
  have h1 : (qtr tbl c (t + 1)).pos = (qtr tbl c (t' + 1)).pos := by rw [e1, e1', hp]
  have h1t : ∀ x, x ≤ b → (qtr tbl c (t + 1)).tape x = (qtr tbl c (t' + 1)).tape x := by
    intro x hxb; rw [e1, e1']; show write _ _ _ x = write _ _ _ x
    simp only [write]; rw [hp]; split_ifs
    · rfl
    · exact htp x hxb
  obtain ⟨-, -, -, -, hm⟩ := macroStep b H hR htape htT hout hsupp
  obtain ⟨-, -, -, -, hm'⟩ := macroStep b H hR htape htT' hout' hsupp'
  rcases hm with ⟨hx, s1, p1, t1⟩ | ⟨hx, m1⟩ <;> rcases hm' with ⟨hx', s1', p1', t1'⟩ | ⟨hx', m1'⟩
  · exact cut_eq_of b (s1.trans s1'.symm) (p1.trans p1'.symm)
      (fun x hxb => by rw [t1 x hxb, t1' x hxb]; exact h1t x hxb)
  · omega
  · omega
  · rw [m1, m1']
    exact cut_eq_of b (by rw [e1, e1']) h1 h1t

end macroS

/-! ### 外の時刻の列の性質 -/

theorem sq_step (i : Nat) : i * (2 * i + 2) + (2 * i + 2) ≤ (i + 1) * (2 * (i + 1) + 2) := by grind

section tauprops
variable {e r w : Nat} (H : Counter tbl e r w) (hR : QHaltRun tbl c T)
  (htape : ∀ u, u ≤ T → ∀ x, (qtr tbl c u).tape x < 2)
  (hb : c.pos ≤ b) (hz : ∀ x, b < x → c.tape x = 0)
include H hR htape hb hz

theorem tau_inv : ∀ i : Nat, tau b tbl c T i ≤ T ∧ (qtr tbl c (tau b tbl c T i)).pos ≤ b ∧
    Supp b i (qtr tbl c (tau b tbl c T i)) ∧ tau b tbl c T i ≤ i * (2 * i + 2) ∧
    (tau b tbl c T i = T ∨ i ≤ tau b tbl c T i)
  | 0 => ⟨Nat.zero_le _, hb, fun x hx => hz x (by omega), le_rfl, Or.inr le_rfl⟩
  | i + 1 => by
    obtain ⟨h1, h2, h3, h4, h5⟩ := tau_inv i
    by_cases hlt : tau b tbl c T i < T
    · have e : tau b tbl c T (i + 1) = tau b tbl c T i + mu b tbl c (tau b tbl c T i) := by
        show (if tau b tbl c T i < T then _ else _) = _; rw [if_pos hlt]
      obtain ⟨m1, m2, m3, m4, -⟩ := macroStep b H hR htape hlt h2 h3
      rw [e]
      have hmu1 : 1 ≤ mu b tbl c (tau b tbl c T i) := by unfold mu; split_ifs <;> omega
      refine ⟨m1, m2, m3, ?_, ?_⟩
      · have := sq_step i
        omega
      · rcases h5 with h5 | h5
        · omega
        · right; omega
    · have e : tau b tbl c T (i + 1) = tau b tbl c T i := by
        show (if tau b tbl c T i < T then _ else _) = _; rw [if_neg hlt]
      rw [e]
      refine ⟨h1, h2, fun x hx => h3 x (by omega), by have := sq_step i; omega, Or.inl (by omega)⟩

theorem tau_reaches : ∃ M, tau b tbl c T M = T := by
  obtain ⟨h1, -, -, -, h5⟩ := tau_inv b H hR htape hb hz (T + 1)
  rcases h5 with h5 | h5
  · exact ⟨T + 1, h5⟩
  · omega

end tauprops

theorem qstep_none_of_cut {c₁ c₂ : QConf} (hcut : cut b c₁ = cut b c₂) (hout : c₁.pos ≤ b)
    (h : qstep tbl c₂ = none) : qstep tbl c₁ = none := by
  unfold qstep at h ⊢
  rw [find_eq_of_cut b hcut hout]
  cases hf : find? tbl c₂.st (c₂.tape c₂.pos) with
  | none => rfl
  | some ρ => rw [hf] at h; cases h

section norep
variable {e r w : Nat} (H : Counter tbl e r w) (hR : QHaltRun tbl c T)
  (htape : ∀ u, u ≤ T → ∀ x, (qtr tbl c u).tape x < 2)
  (hb : c.pos ≤ b) (hz : ∀ x, b < x → c.tape x = 0)
include H hR htape hb hz

/-- **止まる実行では、外の時刻の切り詰めは繰り返さない**。 -/
theorem no_rep_tau {M : Nat} (hM : tau b tbl c T M = T) (hlt : ∀ i, i < M → tau b tbl c T i < T) :
    ∀ n i j, j + n + 1 = M → i < j →
      cut b (qtr tbl c (tau b tbl c T i)) = cut b (qtr tbl c (tau b tbl c T j)) → False := by
  intro n
  induction n with
  | zero =>
    intro i j hj hij hcut
    obtain ⟨-, hoi, hsi, -, -⟩ := tau_inv b H hR htape hb hz i
    obtain ⟨-, hoj, hsj, -, -⟩ := tau_inv b H hR htape hb hz j
    have hti := hlt i (by omega)
    have htj := hlt j (by omega)
    have hn := cut_next b H hR htape hti htj hoi hoj hsi hsj hcut
    have ei : tau b tbl c T (i + 1) = tau b tbl c T i + mu b tbl c (tau b tbl c T i) := by
      show (if tau b tbl c T i < T then _ else _) = _; rw [if_pos hti]
    have ej : tau b tbl c T (j + 1) = tau b tbl c T j + mu b tbl c (tau b tbl c T j) := by
      show (if tau b tbl c T j < T then _ else _) = _; rw [if_pos htj]
    rw [← ei, ← ej, show j + 1 = M by omega, hM] at hn
    obtain ⟨-, ho1, -, -, -⟩ := tau_inv b H hR htape hb hz (i + 1)
    have hs1 := hR.step _ (hlt (i + 1) (by omega))
    rw [qstep_none_of_cut b hn ho1 (qstep_qtr_T hR)] at hs1
    cases hs1
  | succ n ih =>
    intro i j hj hij hcut
    obtain ⟨-, hoi, hsi, -, -⟩ := tau_inv b H hR htape hb hz i
    obtain ⟨-, hoj, hsj, -, -⟩ := tau_inv b H hR htape hb hz j
    have hti := hlt i (by omega)
    have htj := hlt j (by omega)
    have hn := cut_next b H hR htape hti htj hoi hoj hsi hsj hcut
    have ei : tau b tbl c T (i + 1) = tau b tbl c T i + mu b tbl c (tau b tbl c T i) := by
      show (if tau b tbl c T i < T then _ else _) = _; rw [if_pos hti]
    have ej : tau b tbl c T (j + 1) = tau b tbl c T j + mu b tbl c (tau b tbl c T j) := by
      show (if tau b tbl c T j < T then _ else _) = _; rw [if_pos htj]
    rw [← ei, ← ej] at hn
    exact ih (i + 1) (j + 1) (by omega) (by omega) hn

end norep

end run

/-! ### 有界停止 -/

/-- 止まる実行の歩数の上界（窓 [a − ML, b] の配置の数 K について K(2K+2)）。 -/
def boundD (ML : Nat) (a b : Int) : Nat :=
  csize 2 (b - (a - ML) + 1).toNat * (2 * csize 2 (b - (a - ML) + 1).toNat + 2) + 1

theorem toC2_cut_inj {b : Int} {x y : QConf} (hx : x.st < 3) (hy : y.st < 3)
    (h : URTM.Three.toC2 (cut b x) = URTM.Three.toC2 (cut b y)) : cut b x = cut b y := by
  unfold URTM.Three.toC2 at h
  injection h with h1 h2 h3
  have hst := stDir_inj hx hy h3
  unfold cut at h1 h2 ⊢
  simp only at h1 h2 hst
  rw [hst, h2, h1]

/-- **有界停止（右がカウンタ、左が証明書）**。 -/
theorem halts_iff_boundD {tbl : List Quint} {e r w : Nat} (hsrc : Src3 tbl) (hcl : QClosed tbl 2)
    (hdir : DirConsistent tbl) (H : Counter tbl e r w) {CL : List (List Nat)} {ML : Nat}
    (hLc : closedR (mirTbl tbl) CL ML = true)
    (c : QConf) (a b : Int) (ha : a ≤ c.pos) (hb : c.pos ≤ b)
    (hz : ∀ x, (x < a ∨ b < x) → c.tape x = 0) (h2 : ∀ x, c.tape x < 2) :
    QHalts tbl c ↔ qrun tbl (boundD ML a b) c = none := by
  constructor
  · intro hH
    classical
    obtain ⟨T, hR⟩ := qhalts_haltRun hH
    have htape := hR.tape_lt hcl h2
    have hzr : ∀ x, b < x → c.tape x = 0 := fun x hx => hz x (Or.inr hx)
    have hl := left_bound hR hdir hLc a ha (fun x hx => hz x (Or.inl hx))
    have hex := tau_reaches b H hR htape hb hzr
    let M := Nat.find hex
    have hM : tau b tbl c T M = T := Nat.find_spec hex
    have hlt : ∀ i, i < M → tau b tbl c T i < T := by
      intro i hi
      have h1 := (tau_inv b H hR htape hb hzr i).1
      have h2 : tau b tbl c T i ≠ T := Nat.find_min hex hi
      omega
    obtain ⟨W, hW⟩ : ∃ W : Nat, W = (b - (a - ML) + 1).toNat := ⟨_, rfl⟩
    have hWi : (W : Int) = b - (a - ML) + 1 := by rw [hW]; omega
    -- 窓の中
    have hinw : ∀ i, InWin 2 (a - ML) W (URTM.Three.toC2 (cut b (qtr tbl c (tau b tbl c T i)))) := by
      intro i
      obtain ⟨hTi, hoi, -, -, -⟩ := tau_inv b H hR htape hb hzr i
      refine ⟨hl _ hTi, by show (qtr tbl c _).pos < a - ML + W; omega, fun x hx => ?_, fun x => ?_⟩
      · show (if x ≤ b then (qtr tbl c _).tape x else 0) = 0
        split_ifs with hxb
        · have := hR.cell_frozen x 0 (tau b tbl c T i) (by omega) (fun u _ h2 he => by
            have := hl u (by omega); unfold QP at he; omega)
          rw [Nat.zero_add] at this
          rw [this]; exact hz x (Or.inl (by omega))
        · rfl
      · show (if x ≤ b then (qtr tbl c _).tape x else 0) < 2
        split_ifs
        · exact htape _ hTi x
        · decide
    have hMK : M ≤ csize 2 W := by
      by_contra hcon
      obtain ⟨i, j, hij, hjK, hq⟩ := pigeon (csize 2 W)
        (fun i => ccode 2 (a - ML) W (URTM.Three.toC2 (cut b (qtr tbl c (tau b tbl c T i)))))
        (fun i _ => ccode_lt (hinw i))
      have he := ccode_inj (hinw i) (hinw j) hq
      have hcut := toC2_cut_inj (hR.st_lt hsrc _ (hlt i (by omega))) (hR.st_lt hsrc _ (hlt j (by omega))) he
      exact no_rep_tau b H hR htape hb hzr hM hlt (M - j - 1) i j (by omega) hij hcut
    have hTM : T ≤ M * (2 * M + 2) := by rw [← hM]; exact (tau_inv b H hR htape hb hzr M).2.2.2.1
    have hmono : M * (2 * M + 2) ≤ csize 2 W * (2 * csize 2 W + 2) :=
      Nat.mul_le_mul hMK (by omega)
    exact qrun_none_mono tbl c (T + 1) _ hR.dead (by unfold boundD; rw [← hW]; omega)
  · intro h; exact ⟨_, h⟩

/-! ### 鏡像 -/

theorem mirTbl_mirTbl (tbl : List Quint) : mirTbl (mirTbl tbl) = tbl := by
  unfold mirTbl; rw [List.map_map]
  conv => rhs; rw [← List.map_id tbl]
  refine List.map_congr_left fun ρ _ => ?_
  obtain ⟨p, s, t, d, q⟩ := ρ; cases d <;> rfl

theorem src3_mir {tbl : List Quint} (h : Src3 tbl) : Src3 (mirT tbl) := by
  intro ρ hρ; obtain ⟨ρ₀, h₀, rfl⟩ := mem_mirT hρ; exact h ρ₀ h₀

theorem closed_mir {tbl : List Quint} (h : QClosed tbl 2) : QClosed (mirT tbl) 2 := by
  intro ρ hρ; obtain ⟨ρ₀, h₀, rfl⟩ := mem_mirT hρ; exact h ρ₀ h₀

/-! ### Bool の検査 -/

/-- 右側のカウンタの規則（Bool）。 -/
def cntR (tbl : List Quint) (e r w : Nat) : Bool :=
  find? tbl e 1 == some ⟨e, 1, w, Dir.R, e⟩ && find? tbl e 0 == some ⟨e, 0, 1, Dir.L, r⟩ &&
  find? tbl r w == some ⟨r, w, 0, Dir.L, r⟩ && (entR tbl).all (· == e)

/-- 右がカウンタで、左に段階 1 の証明書が立つ。 -/
def sideD (tbl : List Quint) : Bool := checkR (mirTbl tbl) &&
  (List.range 3).any fun e => (List.range 3).any fun r => (List.range 2).any fun w => cntR tbl e r w

/-- **群 D の 8 類の検査**: 表か、その鏡像が `sideD`。 -/
def grpD (es : List Nat) (D : List Dir) : Bool :=
  sideD (URTM.Three.realize es D) || sideD (mirTbl (URTM.Three.realize es D))

/-- 段階 2d の例外: 段階 2b の例外のうち、群 D の 8 類に当たらない表。 -/
def isExcD (es : List Nat) (D : List Dir) : Bool := isExcC es D && !grpD es D

theorem cntR_spec {tbl : List Quint} {e r w : Nat} (h : cntR tbl e r w = true) : Counter tbl e r w := by
  unfold cntR at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨h1, h0⟩, hr⟩, hent⟩ := h
  refine ⟨h1, h0, hr, fun ρ hρ hd => ?_⟩
  have := hent ρ.q (mem_entR hρ hd)
  simpa using this

theorem sideD_bound {tbl : List Quint} (hsrc : Src3 tbl) (hcl : QClosed tbl 2) (hdir : DirConsistent tbl)
    (h : sideD tbl = true) :
    ∃ ML : Nat, ∀ (c : QConf) (a b : Int), a ≤ c.pos → c.pos ≤ b →
      (∀ x, (x < a ∨ b < x) → c.tape x = 0) → (∀ x, c.tape x < 2) →
      (QHalts tbl c ↔ qrun tbl (boundD ML a b) c = none) := by
  unfold sideD at h
  obtain ⟨hL, hc⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨CL, ML, hLc⟩ := checkR_spec hL
  obtain ⟨e, -, hc⟩ := List.any_eq_true.mp hc
  obtain ⟨r, -, hc⟩ := List.any_eq_true.mp hc
  obtain ⟨w, -, hc⟩ := List.any_eq_true.mp hc
  exact ⟨ML, fun c a b ha hb hz h2 => halts_iff_boundD hsrc hcl hdir (cntR_spec hc) hLc c a b ha hb hz h2⟩

theorem sideD_mir_bound {tbl : List Quint} (hsrc : Src3 tbl) (hcl : QClosed tbl 2) (hdir : DirConsistent tbl)
    (h : sideD (mirTbl tbl) = true) :
    ∃ ML : Nat, ∀ (c : QConf) (a b : Int), a ≤ c.pos → c.pos ≤ b →
      (∀ x, (x < a ∨ b < x) → c.tape x = 0) → (∀ x, c.tape x < 2) →
      (QHalts tbl c ↔ qrun tbl (boundD ML a b) c = none) := by
  rw [mirTbl_eq] at h
  obtain ⟨ML, hb⟩ := sideD_bound (src3_mir hsrc) (closed_mir hcl) (dirConsistent_mir hdir) h
  refine ⟨ML, fun c a b ha hb' hz h2 => ?_⟩
  have := hb (mirQ c) (-b) (-a) (by show -b ≤ -c.pos; omega) (by show -c.pos ≤ -a; omega)
    (fun x hx => by show c.tape (-x) = 0; exact hz (-x) (by omega)) (fun x => h2 (-x))
  rw [QHalts_mir, qrun_mir] at this
  have e : boundD ML (-b) (-a) = boundD ML a b := by
    unfold boundD; rw [show -a - (-b - (ML : Int)) + 1 = b - (a - ML) + 1 by omega]
  rw [e] at this
  rw [this]
  cases qrun tbl (boundD ML a b) c <;> simp

/-- 窓の幅で書いた上界。 -/
def bndD (ML w : Nat) : Nat := csize 2 (w + ML + 1) * (2 * csize 2 (w + ML + 1) + 2) + 1

theorem bndD_primrec (ML : Nat) : Primrec (bndD ML) := by
  have hK : Primrec fun w => csize 2 (w + ML + 1) :=
    csize_primrec.comp (Primrec.const 2)
      (Primrec.nat_add.comp (Primrec.nat_add.comp Primrec.id (Primrec.const ML)) (Primrec.const 1))
  exact (Primrec.nat_add.comp (Primrec.nat_mul.comp hK
    (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) hK) (Primrec.const 2)))
    (Primrec.const 1)).of_eq fun w => rfl

theorem boundD_eq (ML m n : Nat) : boundD ML (-(m : Int)) (n : Int) = bndD ML (m + n) := by
  unfold boundD bndD
  rw [show ((n : Int) - (-(m : Int) - ML) + 1).toNat = m + n + ML + 1 by omega]

section
variable {tbl : List Quint} {q₀ q₁ q₂ sg : Nat}

/-- **群 D の 8 類の有界停止**（任意の表の正規形）。 -/
theorem okD_bound (H : RTM32 tbl q₀ q₁ q₂ sg)
    (hok : grpD (absCodes q₀ q₁ q₂ sg tbl) (absDirs q₀ q₁ q₂ tbl) = true) :
    ∃ ML : Nat, ∀ (c : QConf) (m n : ℕ), -(m : ℤ) ≤ c.pos → c.pos ≤ (n : ℤ) →
      (∀ x, (x < -(m : ℤ) ∨ (n : ℤ) < x) → c.tape x = 0) → (∀ x, c.tape x < 2) →
      (QHalts (normT (tbl := tbl) (q₀ := q₀) (q₁ := q₁) (q₂ := q₂) (σ := sg)) c ↔
        qrun (normT (tbl := tbl) (q₀ := q₀) (q₁ := q₁) (q₂ := q₂) (σ := sg)) (bndD ML (m + n)) c = none) := by
  have hsrc := realize_src3 (absCodes q₀ q₁ q₂ sg tbl) (absDirs q₀ q₁ q₂ tbl)
  have hcl := realize_closed (absCodes q₀ q₁ q₂ sg tbl) (absDirs q₀ q₁ q₂ tbl)
  have hdir := realize_dir (absCodes q₀ q₁ q₂ sg tbl) (absDirs q₀ q₁ q₂ tbl)
  unfold grpD at hok
  obtain ⟨ML, hb⟩ : ∃ ML : Nat, ∀ (c : QConf) (a b : Int), a ≤ c.pos → c.pos ≤ b →
      (∀ x, (x < a ∨ b < x) → c.tape x = 0) → (∀ x, c.tape x < 2) →
      (QHalts (URTM.Three.realize (absCodes q₀ q₁ q₂ sg tbl) (absDirs q₀ q₁ q₂ tbl)) c ↔
        qrun (URTM.Three.realize (absCodes q₀ q₁ q₂ sg tbl) (absDirs q₀ q₁ q₂ tbl)) (boundD ML a b) c = none) := by
    rcases Bool.or_eq_true_iff.mp hok with h | h
    · exact sideD_bound hsrc hcl hdir h
    · exact sideD_mir_bound hsrc hcl hdir h
  refine ⟨ML, fun c m n ha hb' hz h2 => ?_⟩
  rw [← boundD_eq]
  exact hb c _ _ ha hb' hz h2

/-- **3 状態 2 記号の RTM の停止問題は、U の ID の上で計算可能**（`isExcD` の表を除く）。 -/
theorem three_halting_computable_D (H : RTM32 tbl q₀ q₁ q₂ sg)
    (hne : isExcD (absCodes q₀ q₁ q₂ sg tbl) (absDirs q₀ q₁ q₂ tbl) = false) :
    ∃ f : ZID → Bool, Computable f ∧
      ∀ z, (∀ a ∈ z.2.1 ++ z.2.2, a = 0 ∨ a ∈ [sg]) → (ZHalts tbl z ↔ f z = true) := by
  cases hC : isExcC (absCodes q₀ q₁ q₂ sg tbl) (absDirs q₀ q₁ q₂ tbl) with
  | false => exact three_halting_computable_C H hC
  | true =>
    have hD : grpD (absCodes q₀ q₁ q₂ sg tbl) (absDirs q₀ q₁ q₂ tbl) = true := by
      unfold isExcD at hne; rw [hC] at hne; simpa using hne
    obtain ⟨ML, hb⟩ := okD_bound H hD
    exact halting_computable_of_bound H (bndD_primrec ML) hb

/-- **定理（段階 2d）: `isExcD` の表を除き、3 状態 2 記号の URTM は存在しない**（Morita Def. 7.1、
    U の記号集合 {0, sg} の上の ID への符号化）。 -/
theorem no_three_two_URTM_D (H : RTM32 tbl q₀ q₁ q₂ sg)
    (hne : isExcD (absCodes q₀ q₁ q₂ sg tbl) (absDirs q₀ q₁ q₂ tbl) = false) :
    ¬ IsUTM_MoritaOver tbl [sg] :=
  not_UTM_of_halting_computable (three_halting_computable_D H hne)

end

/-! ### 残る例外の数

例外 816 表のうち `grpD` に当たる 96 表（8 類）の鍵を一覧 `d96Keys` に書き、それらが `grpD` に当たることを
kernel で確かめる（証明書の閉包が立つ側の計算なので軽い）。残る例外はその外の 720 表に**含まれる**（上界）。
残る 720 表のどれも `grpD` に当たらないこと（＝ちょうど 720）は、閉包が立たない側の計算で kernel では重い
（試行で 29 GB・heartbeat 超過）ので、`#eval`（`tools/three_exc2d.lean`）でだけ確かめている。 -/

/-- `grpD` に当たる 96 表の鍵（`#eval` で生成。下の `d96_grpD` が kernel で検査する）。 -/
def d96Keys : List Nat := [
  238991, 239040, 241973, 242316, 253397, 253446, 270785, 271128, 297835, 298423, 314642, 315230,
  326605, 326899, 329006, 329300, 714579, 714580, 716661, 716668, 736033, 736057, 752840, 752864,
  757797, 757798, 774285, 774292, 793999, 794017, 796400, 796418, 1030345, 1030352, 1032109, 1032116,
  1035327, 1035363, 1035670, 1035706, 1047091, 1047092, 1048561, 1048562, 1052721, 1052751, 1052770, 1052800,
  2206835, 2206842, 2208599, 2208606, 2211817, 2211853, 2212160, 2212196, 2223581, 2223582, 2225051, 2225052,
  2229211, 2229241, 2229260, 2229290, 2361665, 2361666, 2363747, 2363754, 2383119, 2383143, 2399926, 2399950,
  2404883, 2404884, 2421371, 2421378, 2441085, 2441103, 2443486, 2443504, 2827269, 2827318, 2830251, 2830594,
  2841675, 2841724, 2859063, 2859406, 2886113, 2886701, 2902920, 2903508, 2914883, 2915177, 2917284, 2917578
]

theorem d96_grpD : d96Keys.all (fun k => grpD (unkey k).1 (unkey k).2) = true := by decide +kernel

theorem d96_sub : d96Keys.all (fun k => excCKeys.contains k) = true := by decide +kernel

/-- 段階 2d の例外の鍵（の上界）。 -/
def excDKeys : List Nat := excCKeys.filter fun k => !d96Keys.contains k

/-- **段階 2d の例外の表（の上界）の一覧**。 -/
def excDTables : List (List Nat × List Dir) := excDKeys.map unkey

/-- **主定理の仮定が外れる表は一覧に載る**（符号 6 つ・向き 3 つの表について）。 -/
theorem mem_excDTables {es : List Nat} {D : List Dir} (h : ValidKey es D) (hx : isExcD es D = true) :
    (es, D) ∈ excDTables := by
  unfold isExcD at hx
  obtain ⟨hC, hD⟩ := Bool.and_eq_true_iff.mp hx
  obtain ⟨k, hk, he⟩ := List.mem_map.mp ((mem_excCTables h).mp hC)
  refine List.mem_map.mpr ⟨k, List.mem_filter.mpr ⟨hk, ?_⟩, he⟩
  cases hc : d96Keys.contains k
  · rfl
  · exfalso
    have := List.all_eq_true.mp d96_grpD k (List.contains_iff_mem.mp hc)
    rw [he] at this
    simp only [this, Bool.not_true] at hD
    exact Bool.false_ne_true hD

/-- **段階 2d の例外は高々 720 表**（816 − 96。kernel の評価）。 -/
theorem excDKeys_length : excDKeys.length = 720 := by decide +kernel

theorem excDTables_length : excDTables.length = 720 := by
  unfold excDTables; rw [List.length_map, excDKeys_length]

end URTM.Meta
