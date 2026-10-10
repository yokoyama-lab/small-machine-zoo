/-
  3 状態 2 記号の URTM（段階 2e）: **右側を有限個の類で要約する一般の枠組み**（`RSide`）と、
  **群 D のうち 1 進カウンタの 4 類**（48 表）。**手書き**。

  段階 2d（`ThreeD`）の議論は「右へ入る訪問は、どの中身でも同じ状態で戻る」ことを使った。ここでは
  右の中身（b+1 から右）を有限個（m 個）の類に分け、訪問の行き先（戻る状態と戻ったときの類、または
  「戻らない」）が、入る状態と類だけで決まる場合に一般化する（`RSide`）。
  * 外の時刻（ヘッドが b 以下）の (切り詰め `cut`, 類) は、次の外の時刻の (切り詰め, 類) を決める（`cutE_next`）。
  * 「戻らない」訪問は、止まるなら g L 歩以内に止まる（L は中身の長さ）と仮定する（`RSide.fin`）。
  外の時刻の列は、止まる時刻か「戻らない」訪問の始まりで終わる（`tauE`）。止まる実行では、列の中で
  (切り詰め, 類) は繰り返さない（`no_rep_tauE`）。左は段階 1 の証明書で有界なので、列の長さは
  K = csize 2 W · m 以下で、止まるなら K(g K + 2) + g K + 1 歩以内に止まる（`halts_iff_boundE`）。

  **1 進カウンタ**（`Unary`。右側の向きで書く。入り口 e・f、戻り r、e が書く記号 w）:
    (e, 1) → (w, R, e)、(e, 0) → (w, R, f)、(f, 0) → (0, L, r)、(r, w) → (1, L, r)、
    (f, 1) は規則無し、または (f, 1) → (1 − w, R, e) で (r, 1 − w) は規則無し。右へ入る状態は e か f。
  中身はいつも 1^n。e で入ると 2n+3 歩で r・位置 b に戻り中身は 1^(n+1)（`visit_unary`）。f で入ると、
  n = 0 なら 1 歩で r で戻り中身は空のまま、n ≥ 1 なら 2n+3 歩以内に止まる（`unary_halt`）。
  類は「中身が空か」の 2 つ（m = 2）。
  検査 `grpE es D`（Bool）: 表か鏡像の表が、左の証明書と上の規則（`uniR`）を満たす。
  主定理 `no_three_two_URTM_E`（`isExcE = isExcD && !grpE`）。例外は高々 672 表（`excEKeys_length`）。
-/
import URTMMeta.ThreeD

namespace URTM.Meta
open URTM URTM.TwoState URTM.Three

/-! ### 右側の要約 -/

/-- b+1 から右の中身。 -/
def rpart (b : Int) (t : Int → Nat) : Nat → Nat := fun k => t (b + 1 + k)

/-- 中身の長さが L 以下。 -/
def SuppN (L : Nat) (P : Nat → Nat) : Prop := ∀ k, L ≤ k → P k = 0

/-- **右側の要約**: E は右へ入る状態、Inv は中身の不変条件、cls は類（m 未満）、vl は戻る訪問の歩数、
    out e a は「状態 e・類 a で入った訪問」の行き先（some (戻る状態, 戻ったときの類)、または戻らない none）。
    戻らない訪問は、止まるなら g L 歩以内に止まる。 -/
structure RSide (tbl : List Quint) (E : List Nat) (Inv : (Nat → Nat) → Prop) (cls : (Nat → Nat) → Nat)
    (m : Nat) (vl : Nat → (Nat → Nat) → Nat) (out : Nat → Nat → Option (Nat × Nat)) (g : Nat → Nat) :
    Prop where
  hent : ∀ ρ ∈ tbl, ρ.d = Dir.R → ρ.q ∈ E
  inv0 : Inv fun _ => 0
  cls_lt : ∀ P, Inv P → cls P < m
  gmono : ∀ i j, i ≤ j → g i ≤ g j
  ret : ∀ e ∈ E, ∀ (b : Int) (t : Int → Nat) (L q a' : Nat),
    out e (cls (rpart b t)) = some (q, a') → Inv (rpart b t) → SuppN L (rpart b t) → (∀ x, t x < 2) →
    vl e (rpart b t) ≤ g L ∧ ∃ t' : Int → Nat,
      qrun tbl (vl e (rpart b t)) ⟨e, b + 1, t⟩ = some ⟨q, b, t'⟩ ∧ (∀ x, x ≤ b → t' x = t x) ∧
      Inv (rpart b t') ∧ cls (rpart b t') = a' ∧ SuppN (L + 1) (rpart b t')
  fin : ∀ e ∈ E, ∀ (b : Int) (t : Int → Nat) (L : Nat),
    out e (cls (rpart b t)) = none → Inv (rpart b t) → SuppN L (rpart b t) → (∀ x, t x < 2) →
    QHalts tbl ⟨e, b + 1, t⟩ → qrun tbl (g L) ⟨e, b + 1, t⟩ = none

/-! ### 外の時刻の列 -/

section runE
variable {tbl : List Quint} {c : QConf} {T : Nat} (b : Int)
  {E : List Nat} {Inv : (Nat → Nat) → Prop} {cls : (Nat → Nat) → Nat} {m : Nat}
  {vl : Nat → (Nat → Nat) → Nat} {out : Nat → Nat → Option (Nat × Nat)} {g : Nat → Nat}

/-- 時刻 t の次の 1 歩で、戻らない訪問が始まる。 -/
def EndAt (tbl : List Quint) (c : QConf) (T : Nat) (cls : (Nat → Nat) → Nat)
    (out : Nat → Nat → Option (Nat × Nat)) (t : Nat) : Prop :=
  t < T ∧ b < (qtr tbl c (t + 1)).pos ∧
    out (qtr tbl c (t + 1)).st (cls (rpart b (qtr tbl c (t + 1)).tape)) = none

/-- 外の時刻 t から次の外の時刻までの歩数。 -/
def muE (tbl : List Quint) (c : QConf) (vl : Nat → (Nat → Nat) → Nat) (t : Nat) : Nat :=
  if b < (qtr tbl c (t + 1)).pos then 1 + vl (qtr tbl c (t + 1)).st (rpart b (qtr tbl c (t + 1)).tape) else 1

open Classical in
/-- 外の時刻の列（止まる時刻 T か、戻らない訪問の始まりで止める）。 -/
noncomputable def tauE (tbl : List Quint) (c : QConf) (T : Nat) (cls : (Nat → Nat) → Nat)
    (out : Nat → Nat → Option (Nat × Nat)) (vl : Nat → (Nat → Nat) → Nat) : Nat → Nat
  | 0 => 0
  | i + 1 =>
    if tauE tbl c T cls out vl i < T ∧ ¬ EndAt b tbl c T cls out (tauE tbl c T cls out vl i) then
      tauE tbl c T cls out vl i + muE b tbl c vl (tauE tbl c T cls out vl i)
    else tauE tbl c T cls out vl i

open Classical in
theorem tauE_succ_of {i : Nat} (h1 : tauE b tbl c T cls out vl i < T)
    (h2 : ¬ EndAt b tbl c T cls out (tauE b tbl c T cls out vl i)) :
    tauE b tbl c T cls out vl (i + 1) =
      tauE b tbl c T cls out vl i + muE b tbl c vl (tauE b tbl c T cls out vl i) := by
  show (if _ then _ else _) = _
  rw [if_pos ⟨h1, h2⟩]

open Classical in
theorem tauE_succ_stop {i : Nat}
    (h : ¬ (tauE b tbl c T cls out vl i < T ∧ ¬ EndAt b tbl c T cls out (tauE b tbl c T cls out vl i))) :
    tauE b tbl c T cls out vl (i + 1) = tauE b tbl c T cls out vl i := by
  show (if _ then _ else _) = _
  rw [if_neg h]

/-- 1 歩で書くのは b 以下のマスなので、右の中身は変わらない。 -/
theorem rpart_step (hR : QHaltRun tbl c T) {t : Nat} (htT : t < T) (hout : (qtr tbl c t).pos ≤ b) :
    rpart b (qtr tbl c (t + 1)).tape = rpart b (qtr tbl c t).tape := by
  funext k
  show (qtr tbl c (t + 1)).tape (b + 1 + k) = (qtr tbl c t).tape (b + 1 + k)
  exact hR.tape_off t htT _ (by show b + 1 + (k : Int) ≠ (qtr tbl c t).pos; omega)

/-- 切り詰めと類が等しい外の時刻では、「戻らない訪問が始まる」かどうかも同じ。 -/
theorem endAt_of_cut (hR : QHaltRun tbl c T) {t t' : Nat} (htT : t < T) (htT' : t' < T)
    (hout : (qtr tbl c t).pos ≤ b) (hout' : (qtr tbl c t').pos ≤ b)
    (hcut : cut b (qtr tbl c t) = cut b (qtr tbl c t'))
    (hcls : cls (rpart b (qtr tbl c t).tape) = cls (rpart b (qtr tbl c t').tape))
    (h : EndAt b tbl c T cls out t') : EndAt b tbl c T cls out t := by
  obtain ⟨ρ, _, hf, e1⟩ := qstep_some (hR.step t htT)
  obtain ⟨ρ', _, hf', e1'⟩ := qstep_some (hR.step t' htT')
  have hρ : ρ = ρ' := by
    rw [find_eq_of_cut b hcut hout, hf'] at hf; exact (Option.some.inj hf).symm
  subst hρ
  obtain ⟨-, hp, -⟩ := cut_eq b hcut
  have hst : (qtr tbl c (t + 1)).st = (qtr tbl c (t' + 1)).st := by rw [e1, e1']
  have hpos : (qtr tbl c (t + 1)).pos = (qtr tbl c (t' + 1)).pos := by rw [e1, e1', hp]
  obtain ⟨-, hx, ho⟩ := h
  refine ⟨htT, by rw [hpos]; exact hx, ?_⟩
  rw [hst, rpart_step b hR htT hout, hcls, ← rpart_step b hR htT' hout']
  exact ho

section macroS
variable (S : RSide tbl E Inv cls m vl out g) (hR : QHaltRun tbl c T)
  (htape : ∀ u, u ≤ T → ∀ x, (qtr tbl c u).tape x < 2)
include S hR htape

/-- **外の時刻の 1 歩（マクロの 1 歩）**。 -/
theorem macroE {t L : Nat} (htT : t < T) (hend : ¬ EndAt b tbl c T cls out t)
    (hout : (qtr tbl c t).pos ≤ b) (hsupp : SuppN L (rpart b (qtr tbl c t).tape))
    (hinv : Inv (rpart b (qtr tbl c t).tape)) :
    t + muE b tbl c vl t ≤ T ∧ (qtr tbl c (t + muE b tbl c vl t)).pos ≤ b ∧
      SuppN (L + 1) (rpart b (qtr tbl c (t + muE b tbl c vl t)).tape) ∧
      Inv (rpart b (qtr tbl c (t + muE b tbl c vl t)).tape) ∧ muE b tbl c vl t ≤ g L + 1 ∧
      ((b < (qtr tbl c (t + 1)).pos ∧ ∃ q a',
          out (qtr tbl c (t + 1)).st (cls (rpart b (qtr tbl c t).tape)) = some (q, a') ∧
          (qtr tbl c (t + muE b tbl c vl t)).st = q ∧ (qtr tbl c (t + muE b tbl c vl t)).pos = b ∧
          (∀ x, x ≤ b → (qtr tbl c (t + muE b tbl c vl t)).tape x = (qtr tbl c (t + 1)).tape x) ∧
          cls (rpart b (qtr tbl c (t + muE b tbl c vl t)).tape) = a') ∨
        ((qtr tbl c (t + 1)).pos ≤ b ∧ muE b tbl c vl t = 1)) := by
  obtain ⟨ρ, hρ, _, e1⟩ := qstep_some (hR.step t htT)
  have hrp := rpart_step b hR htT hout
  by_cases hx : b < (qtr tbl c (t + 1)).pos
  · -- 訪問
    have hmu : muE b tbl c vl t = 1 + vl (qtr tbl c (t + 1)).st (rpart b (qtr tbl c (t + 1)).tape) := by
      unfold muE; rw [if_pos hx]
    have hd : ρ.d = Dir.R := by
      cases hrd : ρ.d with
      | L => rw [e1, hrd] at hx; simp [move] at hx; omega
      | Z => rw [e1, hrd] at hx; simp [move] at hx; omega
      | R => rfl
    have hpos : (qtr tbl c (t + 1)).pos = b + 1 := by
      have := hx; rw [e1, hd] at this ⊢; simp [move] at this ⊢; omega
    have hE : (qtr tbl c (t + 1)).st ∈ E := by rw [e1]; exact S.hent ρ hρ hd
    have hq : qtr tbl c (t + 1) = ⟨(qtr tbl c (t + 1)).st, b + 1, (qtr tbl c (t + 1)).tape⟩ := by
      rw [← hpos]
    cases ho : out (qtr tbl c (t + 1)).st (cls (rpart b (qtr tbl c (t + 1)).tape)) with
    | none => exact absurd ⟨htT, hx, ho⟩ hend
    | some qa =>
      obtain ⟨q, a'⟩ := qa
      obtain ⟨hvl, t', hrun, hagree, hinv', hcls', hsupp'⟩ :=
        S.ret _ hE b (qtr tbl c (t + 1)).tape L q a' ho (by rw [hrp]; exact hinv) (by rw [hrp]; exact hsupp)
          (htape (t + 1) (by omega))
      rw [← hq] at hrun
      obtain ⟨hle, hV⟩ := qtr_of_run hR (by omega) hrun
      have ht : t + muE b tbl c vl t =
          t + 1 + vl (qtr tbl c (t + 1)).st (rpart b (qtr tbl c (t + 1)).tape) := by
        rw [hmu]; omega
      rw [ht, hV]
      refine ⟨by omega, by show b ≤ b; exact le_rfl, hsupp', hinv', by rw [hmu]; omega,
        Or.inl ⟨hx, q, a', by rw [← hrp]; exact ho, rfl, rfl, hagree, hcls'⟩⟩
  · -- 窓の中
    have hmu : muE b tbl c vl t = 1 := by unfold muE; rw [if_neg hx]
    rw [hmu]
    refine ⟨by omega, by omega, fun k hk => ?_, by rw [hrp]; exact hinv, by omega, Or.inr ⟨by omega, rfl⟩⟩
    rw [hrp]; exact hsupp k (by omega)

/-- **(切り詰め, 類) は次の外の時刻の (切り詰め, 類) を決める**。 -/
theorem cutE_next {t t' L L' : Nat} (htT : t < T) (htT' : t' < T)
    (hend : ¬ EndAt b tbl c T cls out t) (hend' : ¬ EndAt b tbl c T cls out t')
    (hout : (qtr tbl c t).pos ≤ b) (hout' : (qtr tbl c t').pos ≤ b)
    (hsupp : SuppN L (rpart b (qtr tbl c t).tape)) (hsupp' : SuppN L' (rpart b (qtr tbl c t').tape))
    (hinv : Inv (rpart b (qtr tbl c t).tape)) (hinv' : Inv (rpart b (qtr tbl c t').tape))
    (hcut : cut b (qtr tbl c t) = cut b (qtr tbl c t'))
    (hcls : cls (rpart b (qtr tbl c t).tape) = cls (rpart b (qtr tbl c t').tape)) :
    cut b (qtr tbl c (t + muE b tbl c vl t)) = cut b (qtr tbl c (t' + muE b tbl c vl t')) ∧
      cls (rpart b (qtr tbl c (t + muE b tbl c vl t)).tape) =
        cls (rpart b (qtr tbl c (t' + muE b tbl c vl t')).tape) := by
  obtain ⟨ρ, _, hf, e1⟩ := qstep_some (hR.step t htT)
  obtain ⟨ρ', _, hf', e1'⟩ := qstep_some (hR.step t' htT')
  have hρ : ρ = ρ' := by
    rw [find_eq_of_cut b hcut hout, hf'] at hf; exact (Option.some.inj hf).symm
  subst hρ
  obtain ⟨-, hp, htp⟩ := cut_eq b hcut
  have h1 : (qtr tbl c (t + 1)).pos = (qtr tbl c (t' + 1)).pos := by rw [e1, e1', hp]
  have h1s : (qtr tbl c (t + 1)).st = (qtr tbl c (t' + 1)).st := by rw [e1, e1']
  have h1t : ∀ x, x ≤ b → (qtr tbl c (t + 1)).tape x = (qtr tbl c (t' + 1)).tape x := by
    intro x hxb; rw [e1, e1']; show write _ _ _ x = write _ _ _ x
    simp only [write]; rw [hp]; split_ifs
    · rfl
    · exact htp x hxb
  obtain ⟨-, -, -, -, -, hm⟩ := macroE b S hR htape htT hend hout hsupp hinv
  obtain ⟨-, -, -, -, -, hm'⟩ := macroE b S hR htape htT' hend' hout' hsupp' hinv'
  rcases hm with ⟨hx, q, a, ho, s1, p1, t1, c1⟩ | ⟨hx, m1⟩ <;>
    rcases hm' with ⟨hx', q', a'', ho', s1', p1', t1', c1'⟩ | ⟨hx', m1'⟩
  · rw [h1s, hcls, ho'] at ho
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj ho)
    exact ⟨cut_eq_of b (s1.trans s1'.symm) (p1.trans p1'.symm)
      (fun x hxb => by rw [t1 x hxb, t1' x hxb]; exact h1t x hxb), c1.trans c1'.symm⟩
  · omega
  · omega
  · rw [m1, m1']
    refine ⟨cut_eq_of b h1s h1 h1t, ?_⟩
    rw [rpart_step b hR htT hout, rpart_step b hR htT' hout']
    exact hcls

end macroS

theorem step_bound (i a a' : Nat) (h : a ≤ a') : i * (a + 2) + (a + 1) ≤ (i + 1) * (a' + 2) := by
  have := Nat.mul_le_mul_left i (show a + 2 ≤ a' + 2 by omega)
  rw [Nat.succ_mul]; omega

section norepE
variable (S : RSide tbl E Inv cls m vl out g) (hR : QHaltRun tbl c T)
  (htape : ∀ u, u ≤ T → ∀ x, (qtr tbl c u).tape x < 2)
  (hb : c.pos ≤ b) (hz : ∀ x, b < x → c.tape x = 0)
include S hR htape hb hz

theorem tauE_inv : ∀ i : Nat, tauE b tbl c T cls out vl i ≤ T ∧
    (qtr tbl c (tauE b tbl c T cls out vl i)).pos ≤ b ∧
    SuppN i (rpart b (qtr tbl c (tauE b tbl c T cls out vl i)).tape) ∧
    Inv (rpart b (qtr tbl c (tauE b tbl c T cls out vl i)).tape) ∧
    tauE b tbl c T cls out vl i ≤ i * (g i + 2) ∧
    (tauE b tbl c T cls out vl i = T ∨ EndAt b tbl c T cls out (tauE b tbl c T cls out vl i) ∨
      i ≤ tauE b tbl c T cls out vl i)
  | 0 => by
    have hc : qtr tbl c (tauE b tbl c T cls out vl 0) = c := rfl
    have hr0 : rpart b c.tape = fun _ => 0 := by funext k; exact hz _ (by omega)
    have h0 : tauE b tbl c T cls out vl 0 = 0 := rfl
    rw [hc, hr0, h0]
    exact ⟨Nat.zero_le _, hb, fun _ _ => rfl, S.inv0, Nat.zero_le _, Or.inr (Or.inr (Nat.zero_le _))⟩
  | i + 1 => by
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := tauE_inv i
    have hgm := S.gmono i (i + 1) (by omega)
    have hsb := step_bound i (g i) (g (i + 1)) hgm
    by_cases hgo : tauE b tbl c T cls out vl i < T ∧ ¬ EndAt b tbl c T cls out (tauE b tbl c T cls out vl i)
    · rw [tauE_succ_of b hgo.1 hgo.2]
      obtain ⟨m1, m2, m3, m4, m5, -⟩ := macroE b S hR htape hgo.1 hgo.2 h2 h3 h4
      have hmu1 : 1 ≤ muE b tbl c vl (tauE b tbl c T cls out vl i) := by unfold muE; split_ifs <;> omega
      refine ⟨m1, m2, m3, m4, by omega, ?_⟩
      rcases h6 with h6 | h6 | h6
      · omega
      · exact absurd h6 hgo.2
      · right; right; omega
    · rw [tauE_succ_stop b hgo]
      refine ⟨h1, h2, fun k hk => h3 k (by omega), h4, by omega, ?_⟩
      by_cases hT : tauE b tbl c T cls out vl i < T
      · right; left; by_contra hc; exact hgo ⟨hT, hc⟩
      · left; omega

theorem tauE_reaches : ∃ M, tauE b tbl c T cls out vl M = T ∨
    EndAt b tbl c T cls out (tauE b tbl c T cls out vl M) := by
  obtain ⟨h1, -, -, -, -, h6⟩ := tauE_inv b S hR htape hb hz (T + 1)
  rcases h6 with h6 | h6 | h6
  · exact ⟨T + 1, Or.inl h6⟩
  · exact ⟨T + 1, Or.inr h6⟩
  · omega

/-- **止まる実行では、外の時刻の (切り詰め, 類) は繰り返さない**。 -/
theorem no_rep_tauE {M : Nat}
    (hlt : ∀ i, i < M → tauE b tbl c T cls out vl i < T ∧
      ¬ EndAt b tbl c T cls out (tauE b tbl c T cls out vl i))
    (hM : tauE b tbl c T cls out vl M = T ∨ EndAt b tbl c T cls out (tauE b tbl c T cls out vl M)) :
    ∀ n i j, j + n = M → i < j →
      cut b (qtr tbl c (tauE b tbl c T cls out vl i)) = cut b (qtr tbl c (tauE b tbl c T cls out vl j)) →
      cls (rpart b (qtr tbl c (tauE b tbl c T cls out vl i)).tape) =
        cls (rpart b (qtr tbl c (tauE b tbl c T cls out vl j)).tape) → False := by
  intro n
  induction n with
  | zero =>
    intro i j hj hij hcut hcls
    obtain ⟨hti, hei⟩ := hlt i (by omega)
    obtain ⟨-, hoi, -, -, -, -⟩ := tauE_inv b S hR htape hb hz i
    obtain ⟨-, hoj, -, -, -, -⟩ := tauE_inv b S hR htape hb hz j
    obtain rfl : j = M := by omega
    rcases hM with hM | hM
    · rw [hM] at hcut
      have hs := hR.step _ hti
      rw [qstep_none_of_cut b hcut hoi (qstep_qtr_T hR)] at hs
      cases hs
    · exact hei (endAt_of_cut b hR hti hM.1 hoi hoj hcut hcls hM)
  | succ n ih =>
    intro i j hj hij hcut hcls
    obtain ⟨hti, hei⟩ := hlt i (by omega)
    obtain ⟨htj, hej⟩ := hlt j (by omega)
    obtain ⟨-, hoi, hsi, hii, -, -⟩ := tauE_inv b S hR htape hb hz i
    obtain ⟨-, hoj, hsj, hij', -, -⟩ := tauE_inv b S hR htape hb hz j
    obtain ⟨hn1, hn2⟩ := cutE_next b S hR htape hti htj hei hej hoi hoj hsi hsj hii hij' hcut hcls
    rw [← tauE_succ_of b hti hei, ← tauE_succ_of b htj hej] at hn1 hn2
    exact ih (i + 1) (j + 1) (by omega) (by omega) hn1 hn2

end norepE

end runE

/-! ### 有界停止 -/

theorem pair_lt {x y C m : Nat} (hx : x < C) (hy : y < m) : x * m + y < C * m := by
  have := Nat.mul_le_mul_right m (show x + 1 ≤ C by omega)
  rw [Nat.succ_mul] at this; omega

theorem pair_inj {x₁ x₂ y₁ y₂ m : Nat} (h₁ : y₁ < m) (h₂ : y₂ < m) (h : x₁ * m + y₁ = x₂ * m + y₂) :
    x₁ = x₂ ∧ y₁ = y₂ := by
  have hm : 0 < m := by omega
  have d1 : (x₁ * m + y₁) / m = x₁ := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hm, Nat.div_eq_of_lt h₁, Nat.zero_add]
  have d2 : (x₂ * m + y₂) / m = x₂ := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hm, Nat.div_eq_of_lt h₂, Nat.zero_add]
  have r1 : (x₁ * m + y₁) % m = y₁ := by rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h₁]
  have r2 : (x₂ * m + y₂) % m = y₂ := by rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h₂]
  exact ⟨by rw [← d1, ← d2, h], by rw [← r1, ← r2, h]⟩

/-- 止まる実行の歩数の上界（窓 [a − ML, b] の配置の数と類の数の積 K について K(g K + 2) + g K + 1）。 -/
def boundE (m : Nat) (g : Nat → Nat) (ML : Nat) (a b : Int) : Nat :=
  csize 2 (b - (a - ML) + 1).toNat * m * (g (csize 2 (b - (a - ML) + 1).toNat * m) + 2) +
    g (csize 2 (b - (a - ML) + 1).toNat * m) + 1

/-- **有界停止（右が `RSide`、左が証明書）**。 -/
theorem halts_iff_boundE {tbl : List Quint} {E : List Nat} {Inv : (Nat → Nat) → Prop}
    {cls : (Nat → Nat) → Nat} {m : Nat} {vl : Nat → (Nat → Nat) → Nat}
    {out : Nat → Nat → Option (Nat × Nat)} {g : Nat → Nat}
    (hsrc : Src3 tbl) (hcl : QClosed tbl 2) (hdir : DirConsistent tbl)
    (S : RSide tbl E Inv cls m vl out g) {CL : List (List Nat)} {ML : Nat}
    (hLc : closedR (mirTbl tbl) CL ML = true)
    (c : QConf) (a b : Int) (ha : a ≤ c.pos) (hb : c.pos ≤ b)
    (hz : ∀ x, (x < a ∨ b < x) → c.tape x = 0) (h2 : ∀ x, c.tape x < 2) :
    QHalts tbl c ↔ qrun tbl (boundE m g ML a b) c = none := by
  constructor
  · intro hH
    classical
    obtain ⟨T, hR⟩ := qhalts_haltRun hH
    have htape := hR.tape_lt hcl h2
    have hzr : ∀ x, b < x → c.tape x = 0 := fun x hx => hz x (Or.inr hx)
    have hl := left_bound hR hdir hLc a ha (fun x hx => hz x (Or.inl hx))
    have hex := tauE_reaches b S hR htape hb hzr
    have hM := Nat.find_spec hex
    have hlt : ∀ i, i < Nat.find hex → tauE b tbl c T cls out vl i < T ∧
        ¬ EndAt b tbl c T cls out (tauE b tbl c T cls out vl i) := by
      intro i hi
      have hmin := Nat.find_min hex hi
      have h1 := (tauE_inv b S hR htape hb hzr i).1
      refine ⟨?_, fun h => hmin (Or.inr h)⟩
      by_contra hc; exact hmin (Or.inl (by omega))
    obtain ⟨W, hW⟩ : ∃ W : Nat, W = (b - (a - ML) + 1).toNat := ⟨_, rfl⟩
    have hWi : (W : Int) = b - (a - ML) + 1 := by rw [hW]; omega
    -- 窓の中
    have hinw : ∀ i, InWin 2 (a - ML) W (URTM.Three.toC2 (cut b (qtr tbl c (tauE b tbl c T cls out vl i)))) := by
      intro i
      obtain ⟨hTi, hoi, -, -, -, -⟩ := tauE_inv b S hR htape hb hzr i
      refine ⟨hl _ hTi, by show (qtr tbl c _).pos < a - ML + W; omega, fun x hx => ?_, fun x => ?_⟩
      · show (if x ≤ b then (qtr tbl c _).tape x else 0) = 0
        split_ifs with hxb
        · have := hR.cell_frozen x 0 (tauE b tbl c T cls out vl i) (by omega) (fun u _ h2 he => by
            have := hl u (by omega); unfold QP at he; omega)
          rw [Nat.zero_add] at this
          rw [this]; exact hz x (Or.inl (by omega))
        · rfl
      · show (if x ≤ b then (qtr tbl c _).tape x else 0) < 2
        split_ifs
        · exact htape _ hTi x
        · decide
    have hMK : Nat.find hex ≤ csize 2 W * m := by
      by_contra hcon
      obtain ⟨i, j, hij, hjK, hq⟩ := pigeon (csize 2 W * m)
        (fun i => ccode 2 (a - ML) W (URTM.Three.toC2 (cut b (qtr tbl c (tauE b tbl c T cls out vl i)))) * m +
          cls (rpart b (qtr tbl c (tauE b tbl c T cls out vl i)).tape))
        (fun i _ => pair_lt (ccode_lt (hinw i)) (S.cls_lt _ (tauE_inv b S hR htape hb hzr i).2.2.2.1))
      obtain ⟨he, hc⟩ := pair_inj (S.cls_lt _ (tauE_inv b S hR htape hb hzr i).2.2.2.1)
        (S.cls_lt _ (tauE_inv b S hR htape hb hzr j).2.2.2.1) hq
      have he' := ccode_inj (hinw i) (hinw j) he
      have hcut := toC2_cut_inj (hR.st_lt hsrc _ (hlt i (by omega)).1)
        (hR.st_lt hsrc _ (hlt j (by omega)).1) he'
      exact no_rep_tauE b S hR htape hb hzr hlt hM (Nat.find hex - j) i j (by omega) hij hcut hc
    have hgK := S.gmono _ _ hMK
    have hbd : boundE m g ML a b = csize 2 W * m * (g (csize 2 W * m) + 2) + g (csize 2 W * m) + 1 := by
      unfold boundE; rw [← hW]
    have hmono : Nat.find hex * (g (Nat.find hex) + 2) ≤ csize 2 W * m * (g (csize 2 W * m) + 2) :=
      Nat.mul_le_mul hMK (by omega)
    obtain ⟨-, ho0, hs0, hi0, hb0, -⟩ := tauE_inv b S hR htape hb hzr (Nat.find hex)
    rcases hM with hM | hM
    · -- 止まる時刻に着いた
      rw [hM] at hb0
      exact qrun_none_mono tbl c (T + 1) _ hR.dead (by rw [hbd]; omega)
    · -- 戻らない訪問が始まった
      obtain ⟨hMT, hx, ho⟩ := hM
      obtain ⟨ρ, hρ, _, e1⟩ := qstep_some (hR.step _ hMT)
      have hd : ρ.d = Dir.R := by
        cases hrd : ρ.d with
        | L => rw [e1, hrd] at hx; simp [move] at hx; omega
        | Z => rw [e1, hrd] at hx; simp [move] at hx; omega
        | R => rfl
      have hpos : (qtr tbl c (tauE b tbl c T cls out vl (Nat.find hex) + 1)).pos = b + 1 := by
        have := hx; rw [e1, hd] at this ⊢; simp [move] at this ⊢; omega
      have hE : (qtr tbl c (tauE b tbl c T cls out vl (Nat.find hex) + 1)).st ∈ E := by
        rw [e1]; exact S.hent ρ hρ hd
      have hrp := rpart_step b hR hMT ho0
      have hq : qtr tbl c (tauE b tbl c T cls out vl (Nat.find hex) + 1) =
          ⟨(qtr tbl c (tauE b tbl c T cls out vl (Nat.find hex) + 1)).st, b + 1,
            (qtr tbl c (tauE b tbl c T cls out vl (Nat.find hex) + 1)).tape⟩ := by
        rw [← hpos]
      have hH' : QHalts tbl ⟨(qtr tbl c (tauE b tbl c T cls out vl (Nat.find hex) + 1)).st, b + 1,
          (qtr tbl c (tauE b tbl c T cls out vl (Nat.find hex) + 1)).tape⟩ := by
        rw [← hq]; exact ⟨_, hR.run_from _ (by omega)⟩
      have hfin := S.fin _ hE b _ (Nat.find hex) ho (by rw [hrp]; exact hi0) (by rw [hrp]; exact hs0)
        (htape _ (by omega)) hH'
      rw [← hq] at hfin
      have hrun : qrun tbl (tauE b tbl c T cls out vl (Nat.find hex) + 1 + g (Nat.find hex)) c = none := by
        rw [qrun_add, hR.run _ (by omega)]; exact hfin
      exact qrun_none_mono tbl c _ _ hrun (by rw [hbd]; omega)
  · intro h; exact ⟨_, h⟩

/-! ### 1 進カウンタ -/

/-- 右へ同じ状態のまま x の上を進み、y に書き換える。 -/
theorem sweepR {tbl : List Quint} {s x y : Nat} (h : find? tbl s x = some ⟨s, x, y, Dir.R, s⟩)
    (pos : Int) (tape : Int → Nat) :
    ∀ i : Nat, (∀ k : Nat, k < i → tape (pos + k) = x) →
      qrun tbl i ⟨s, pos, tape⟩ = some ⟨s, pos + i, fun z => if pos ≤ z ∧ z < pos + i then y else tape z⟩
  | 0, _ => by
    simp only [qrun, Nat.cast_zero, Int.add_zero, Option.some.injEq, QConf.mk.injEq, true_and]
    funext z; split_ifs <;> first | rfl | omega
  | i + 1, hx => by
    rw [qrun_succ_right, sweepR h pos tape i (fun k hk => hx k (by omega))]
    simp only [Option.bind_some]
    have hread : (if pos ≤ pos + (i : Int) ∧ pos + (i : Int) < pos + i then y else tape (pos + i)) = x := by
      rw [if_neg (by omega)]; exact hx i (by omega)
    rw [qstep_of_find (by simp only; rw [hread]; exact h)]
    simp only [Option.some.injEq, QConf.mk.injEq, true_and, move]
    refine ⟨by push_cast; omega, ?_⟩
    funext z; simp only [write]; split_ifs <;> first | rfl | omega

/-- 左へ同じ状態のまま x の上を進み、y に書き換える。 -/
theorem sweepL {tbl : List Quint} {s x y : Nat} (h : find? tbl s x = some ⟨s, x, y, Dir.L, s⟩)
    (pos : Int) (tape : Int → Nat) :
    ∀ i : Nat, (∀ k : Nat, k < i → tape (pos - k) = x) →
      qrun tbl i ⟨s, pos, tape⟩ = some ⟨s, pos - i, fun z => if pos - i < z ∧ z ≤ pos then y else tape z⟩
  | 0, _ => by
    simp only [qrun, Nat.cast_zero, Int.sub_zero, Option.some.injEq, QConf.mk.injEq, true_and]
    funext z; split_ifs <;> first | rfl | omega
  | i + 1, hx => by
    rw [qrun_succ_right, sweepL h pos tape i (fun k hk => hx k (by omega))]
    simp only [Option.bind_some]
    have hread : (if pos - (i : Int) < pos - i ∧ pos - (i : Int) ≤ pos then y else tape (pos - i)) = x := by
      rw [if_neg (by omega)]; exact hx i (by omega)
    rw [qstep_of_find (by simp only; rw [hread]; exact h)]
    simp only [Option.some.injEq, QConf.mk.injEq, true_and, move]
    refine ⟨by push_cast; omega, ?_⟩
    funext z; simp only [write]; split_ifs <;> first | rfl | omega

theorem qstep_none_at {tbl : List Quint} {st s : Nat} {pos : Int} {tape : Int → Nat}
    (hs : tape pos = s) (h : find? tbl st s = none) : qstep tbl ⟨st, pos, tape⟩ = none := by
  simp only [qstep, hs, h]

/-- 右側の 1 進カウンタの規則（入り口 e・f、戻り r、e が書く記号 w）。 -/
structure Unary (tbl : List Quint) (e f r w : Nat) : Prop where
  he1 : find? tbl e 1 = some ⟨e, 1, w, Dir.R, e⟩
  he0 : find? tbl e 0 = some ⟨e, 0, w, Dir.R, f⟩
  hf0 : find? tbl f 0 = some ⟨f, 0, 0, Dir.L, r⟩
  hrw : find? tbl r w = some ⟨r, w, 1, Dir.L, r⟩
  hf1 : find? tbl f 1 = none ∨ (find? tbl f 1 = some ⟨f, 1, 1 - w, Dir.R, e⟩ ∧ find? tbl r (1 - w) = none)
  hent : ∀ ρ ∈ tbl, ρ.d = Dir.R → ρ.q ∈ [e, f]

section unary
variable {tbl : List Quint} {e f r w : Nat} (H : Unary tbl e f r w)
include H

/-- **e の訪問**: 中身 1^n 0 0 … に e で入ると、2n+3 歩で r・位置 pos − 1 に戻り、中身は 1^(n+1) 0 …。 -/
theorem visit_unary (pos : Int) (tape : Int → Nat) (n : Nat)
    (h1s : ∀ k : Nat, k < n → tape (pos + k) = 1) (h0 : tape (pos + n) = 0) (h0' : tape (pos + n + 1) = 0) :
    qrun tbl (2 * n + 3) ⟨e, pos, tape⟩ =
      some ⟨r, pos - 1, fun z => if pos ≤ z ∧ z ≤ pos + n then 1 else if z = pos + n + 1 then 0 else tape z⟩ := by
  rw [show 2 * n + 3 = n + (n + 1 + 1 + 1) by omega, qrun_add, sweepR H.he1 pos tape n h1s]
  simp only [Option.bind_some]
  have hr1 : (if pos ≤ pos + (n : Int) ∧ pos + (n : Int) < pos + n then w else tape (pos + n)) = 0 := by
    rw [if_neg (by omega)]; exact h0
  rw [qrun_succ_some tbl _ (qstep_of_find (by simp only; rw [hr1]; exact H.he0))]
  simp only [move]
  have hr2 : write (fun z => if pos ≤ z ∧ z < pos + n then w else tape z) (pos + n) w (pos + n + 1) = 0 := by
    simp only [write]; rw [if_neg (by omega), if_neg (by omega)]; exact h0'
  rw [qrun_succ_some tbl _ (qstep_of_find (by simp only; rw [hr2]; exact H.hf0))]
  simp only [move]
  rw [sweepL H.hrw (pos + n + 1 - 1) _ (n + 1) (fun k hk => by
    simp only [write]; split_ifs <;> first | rfl | omega)]
  simp only [Option.some.injEq, QConf.mk.injEq, true_and]
  refine ⟨by push_cast; omega, ?_⟩
  funext z; simp only [write]; split_ifs <;> first | rfl | omega

/-- **f の訪問（中身が空でない）**: 中身 1^(n+1) 0 0 … に f で入り (f, 1) → (1 − w, R, e) なら、2n+5 歩以内に止まる。 -/
theorem unary_halt (hB : find? tbl f 1 = some ⟨f, 1, 1 - w, Dir.R, e⟩) (hr : find? tbl r (1 - w) = none)
    (pos : Int) (tape : Int → Nat) (n : Nat)
    (h1s : ∀ k : Nat, k < n + 1 → tape (pos + k) = 1) (h0 : tape (pos + ((n + 1 : Nat) : Int)) = 0)
    (h0' : tape (pos + ((n + 1 : Nat) : Int) + 1) = 0) :
    qrun tbl (2 * n + 5) ⟨f, pos, tape⟩ = none := by
  have hp1 : tape pos = 1 := by have := h1s 0 (by omega); simpa using this
  have hs1 : qrun tbl 1 ⟨f, pos, tape⟩ = some ⟨e, pos + 1, write tape pos (1 - w)⟩ := by
    rw [qrun_succ_some tbl 0 (qstep_of_find (by simp only; rw [hp1]; exact hB))]; rfl
  have hv := visit_unary H (pos + 1) (write tape pos (1 - w)) n
    (fun k hk => by
      simp only [write]; rw [if_neg (by omega)]
      rw [show pos + 1 + (k : Int) = pos + ((k + 1 : Nat) : Int) by push_cast; omega]
      exact h1s (k + 1) (by omega))
    (by
      simp only [write]; rw [if_neg (by omega)]
      rw [show pos + 1 + (n : Int) = pos + ((n + 1 : Nat) : Int) by push_cast; omega]; exact h0)
    (by
      simp only [write]; rw [if_neg (by omega)]
      rw [show pos + 1 + (n : Int) + 1 = pos + ((n + 1 : Nat) : Int) + 1 by push_cast; omega]; exact h0')
  have hs2 : qstep tbl ⟨r, pos + 1 - 1, fun z => if pos + 1 ≤ z ∧ z ≤ pos + 1 + n then 1
      else if z = pos + 1 + n + 1 then 0 else write tape pos (1 - w) z⟩ = none := by
    refine qstep_none_at ?_ hr
    show (if pos + 1 ≤ pos + 1 - 1 ∧ pos + 1 - 1 ≤ pos + 1 + (n : Int) then 1
      else if pos + 1 - 1 = pos + 1 + (n : Int) + 1 then 0 else write tape pos (1 - w) (pos + 1 - 1)) = 1 - w
    rw [if_neg (by omega), if_neg (by omega)]; simp only [write]; rw [if_pos (by omega)]
  rw [show 2 * n + 5 = 1 + (2 * n + 3 + 1) by omega, qrun_add, hs1]
  show qrun tbl (2 * n + 3 + 1) ⟨e, pos + 1, write tape pos (1 - w)⟩ = none
  rw [qrun_add, hv]
  exact qrun_succ_none tbl 0 hs2

end unary

/-! ### 1 進カウンタの要約 -/

/-- 中身は 1^n。 -/
def UInv (P : Nat → Nat) : Prop := ∃ n, ∀ k, P k = if k < n then 1 else 0

/-- 類: 中身が空なら 0、空でなければ 1。 -/
def ucls (P : Nat → Nat) : Nat := if P 0 = 1 then 1 else 0

open Classical in
/-- 先頭から続く 1 の数。 -/
noncomputable def lead1 (P : Nat → Nat) : Nat := if h : ∃ j, P j ≠ 1 then Nat.find h else 0

theorem lead1_eq {P : Nat → Nat} {n : Nat} (h : ∀ k, P k = if k < n then 1 else 0) : lead1 P = n := by
  classical
  have hex : ∃ j, P j ≠ 1 := ⟨n, by rw [h n, if_neg (by omega)]; decide⟩
  unfold lead1; rw [dif_pos hex, Nat.find_eq_iff]
  refine ⟨by rw [h n, if_neg (by omega)]; decide, fun k hk => ?_⟩
  rw [h k, if_pos hk]; simp

/-- 訪問の歩数（e なら 2n+3、f なら 1）。 -/
noncomputable def uvl (e e' : Nat) (P : Nat → Nat) : Nat := if e' = e then 2 * lead1 P + 3 else 1

/-- 行き先: e なら r で戻り中身は空でない。f なら、中身が空のとき r で戻り空のまま、空でないとき戻らない。 -/
def uout (e r e' a : Nat) : Option (Nat × Nat) :=
  if e' = e then some (r, 1) else if a = 0 then some (r, 0) else none

def ug (L : Nat) : Nat := 2 * L + 3

theorem uinv_le {P : Nat → Nat} {n L : Nat} (hn : ∀ k, P k = if k < n then 1 else 0) (hs : SuppN L P) :
    n ≤ L := by
  by_contra hc
  have := hs L (le_refl L)
  rw [hn L, if_pos (by omega)] at this
  exact absurd this (by decide)

/-- **1 進カウンタは `RSide`**。 -/
theorem unary_rside {tbl : List Quint} {e f r w : Nat} (H : Unary tbl e f r w) :
    RSide tbl [e, f] UInv ucls 2 (uvl e) (uout e r) ug where
  hent := H.hent
  inv0 := ⟨0, fun k => by simp⟩
  cls_lt := fun P _ => by unfold ucls; split_ifs <;> omega
  gmono := fun i j h => by unfold ug; omega
  ret := by
    intro e' he' b t L q a' ho hinv hsupp _
    obtain ⟨n, hn⟩ := hinv
    have hnL := uinv_le hn hsupp
    have hval : ∀ k : Nat, t (b + 1 + k) = if k < n then 1 else 0 := hn
    by_cases hee : e' = e
    · rw [hee] at ho ⊢
      have ho' : uout e r e (ucls (rpart b t)) = some (r, 1) := by unfold uout; rw [if_pos rfl]
      rw [ho'] at ho
      obtain ⟨hq, ha⟩ := Prod.mk.inj (Option.some.inj ho)
      rw [← hq, ← ha]
      have hvl : uvl e e (rpart b t) = 2 * n + 3 := by unfold uvl; rw [if_pos rfl, lead1_eq hn]
      rw [hvl]
      refine ⟨by unfold ug; omega,
        fun z => if b + 1 ≤ z ∧ z ≤ b + 1 + n then 1 else if z = b + 1 + n + 1 then 0 else t z,
        ?_, ?_, ?_, ?_, ?_⟩
      · rw [visit_unary H (b + 1) t n (fun k hk => by rw [hval k, if_pos hk])
          (by rw [hval n, if_neg (by omega)])
          (by rw [show b + 1 + (n : Int) + 1 = b + 1 + ((n + 1 : Nat) : Int) by push_cast; omega,
            hval (n + 1), if_neg (by omega)]),
          show b + 1 - 1 = b by omega]
      · intro x hx; simp only; rw [if_neg (by omega), if_neg (by omega)]
      · refine ⟨n + 1, fun k => ?_⟩
        show (if b + 1 ≤ b + 1 + (k : Int) ∧ b + 1 + (k : Int) ≤ b + 1 + n then 1
          else if b + 1 + (k : Int) = b + 1 + n + 1 then 0 else t (b + 1 + k)) = _
        by_cases hk : k < n + 1
        · rw [if_pos hk, if_pos (by omega)]
        · rw [if_neg hk, if_neg (by omega)]
          split_ifs
          · rfl
          · rw [hval k, if_neg (by omega)]
      · have h0 : rpart b (fun z => if b + 1 ≤ z ∧ z ≤ b + 1 + n then 1
            else if z = b + 1 + n + 1 then 0 else t z) 0 = 1 := by
          show (if b + 1 ≤ b + 1 + ((0 : Nat) : Int) ∧ b + 1 + ((0 : Nat) : Int) ≤ b + 1 + n then 1
            else _) = 1
          rw [if_pos (by omega)]
        unfold ucls; rw [if_pos h0]
      · intro k hk
        show (if b + 1 ≤ b + 1 + (k : Int) ∧ b + 1 + (k : Int) ≤ b + 1 + n then 1
          else if b + 1 + (k : Int) = b + 1 + n + 1 then 0 else t (b + 1 + k)) = 0
        rw [if_neg (by omega)]
        split_ifs
        · rfl
        · rw [hval k, if_neg (by omega)]
    · have hef : e' = f := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at he'
        rcases he' with h | h
        · exact absurd h hee
        · exact h
      have hfe : f ≠ e := by rw [← hef]; exact hee
      rw [hef] at ho ⊢
      have hc0 : ucls (rpart b t) = 0 := by
        by_contra hc
        have : uout e r f (ucls (rpart b t)) = none := by unfold uout; rw [if_neg hfe, if_neg hc]
        rw [this] at ho; cases ho
      have hn0 : n = 0 := by
        by_contra hc
        have h1 : rpart b t 0 = 1 := by
          show t (b + 1 + ((0 : Nat) : Int)) = 1; rw [hval 0, if_pos (by omega)]
        unfold ucls at hc0; rw [if_pos h1] at hc0; cases hc0
      subst hn0
      have ho' : uout e r f (ucls (rpart b t)) = some (r, 0) := by
        unfold uout; rw [if_neg hfe, if_pos hc0]
      rw [ho'] at ho
      obtain ⟨hq, ha⟩ := Prod.mk.inj (Option.some.inj ho)
      rw [← hq, ← ha]
      have hvl : uvl e f (rpart b t) = 1 := by unfold uvl; rw [if_neg hfe]
      have ht1 : t (b + 1) = 0 := by have := hval 0; simpa using this
      rw [hvl]
      refine ⟨by unfold ug; omega, write t (b + 1) 0, ?_, ?_, ?_, ?_, ?_⟩
      · rw [qrun_succ_some tbl 0 (qstep_of_find (by simp only; rw [ht1]; exact H.hf0))]
        simp [qrun, move]
      · intro x hx; exact write_off _ _ _ (by omega)
      · refine ⟨0, fun k => ?_⟩
        show write t (b + 1) 0 (b + 1 + k) = _
        rw [if_neg (Nat.not_lt_zero k)]
        simp only [write]
        split_ifs
        · rfl
        · rw [hval k, if_neg (Nat.not_lt_zero k)]
      · have h0 : rpart b (write t (b + 1) 0) 0 ≠ 1 := by
          show write t (b + 1) 0 (b + 1 + ((0 : Nat) : Int)) ≠ 1
          simp [write]
        unfold ucls; rw [if_neg h0]
      · intro k _
        show write t (b + 1) 0 (b + 1 + k) = 0
        simp only [write]
        split_ifs
        · rfl
        · rw [hval k, if_neg (Nat.not_lt_zero k)]
  fin := by
    intro e' he' b t L ho hinv hsupp _ _
    obtain ⟨n, hn⟩ := hinv
    have hnL := uinv_le hn hsupp
    have hval : ∀ k : Nat, t (b + 1 + k) = if k < n then 1 else 0 := hn
    have hee : e' ≠ e := by
      intro h; rw [h] at ho; unfold uout at ho; rw [if_pos rfl] at ho; cases ho
    have hef : e' = f := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he'
      rcases he' with h | h
      · exact absurd h hee
      · exact h
    have hfe : f ≠ e := by rw [← hef]; exact hee
    rw [hef] at ho ⊢
    have hc1 : ucls (rpart b t) ≠ 0 := by
      intro hc; unfold uout at ho; rw [if_neg hfe, if_pos hc] at ho; cases ho
    have hn1 : 1 ≤ n := by
      by_contra hc
      have h0 : rpart b t 0 ≠ 1 := by
        show t (b + 1 + ((0 : Nat) : Int)) ≠ 1; rw [hval 0, if_neg (by omega)]; decide
      apply hc1; unfold ucls; rw [if_neg h0]
    have ht1 : t (b + 1) = 1 := by have := hval 0; rw [if_pos (by omega)] at this; simpa using this
    rcases H.hf1 with hA | ⟨hB, hr⟩
    · exact qrun_none_mono tbl _ 1 _ (qrun_succ_none tbl 0 (qstep_none_at ht1 hA)) (by unfold ug; omega)
    · obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      exact qrun_none_mono tbl _ _ _ (unary_halt H hB hr (b + 1) t n' (fun k hk => by rw [hval k, if_pos hk])
        (by rw [hval (n' + 1), if_neg (by omega)])
        (by rw [show b + 1 + ((n' + 1 : Nat) : Int) + 1 = b + 1 + ((n' + 2 : Nat) : Int) by push_cast; omega,
          hval (n' + 2), if_neg (by omega)])) (by unfold ug; omega)

/-! ### Bool の検査 -/

/-- 右側の 1 進カウンタの規則（Bool）。 -/
def uniR (tbl : List Quint) (e f r w : Nat) : Bool :=
  find? tbl e 1 == some ⟨e, 1, w, Dir.R, e⟩ && find? tbl e 0 == some ⟨e, 0, w, Dir.R, f⟩ &&
  find? tbl f 0 == some ⟨f, 0, 0, Dir.L, r⟩ && find? tbl r w == some ⟨r, w, 1, Dir.L, r⟩ &&
  (find? tbl f 1 == none ||
    (find? tbl f 1 == some ⟨f, 1, 1 - w, Dir.R, e⟩ && find? tbl r (1 - w) == none)) &&
  (entR tbl).all (fun q => q == e || q == f)

theorem uniR_spec {tbl : List Quint} {e f r w : Nat} (h : uniR tbl e f r w = true) : Unary tbl e f r w := by
  unfold uniR at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h1, h0⟩, hf0⟩, hrw⟩, hf1⟩, hent⟩ := h
  refine ⟨h1, h0, hf0, hrw, hf1, fun ρ hρ hd => ?_⟩
  have := hent ρ.q (mem_entR hρ hd)
  simpa using this

/-- 右が 1 進カウンタで、左に段階 1 の証明書が立つ。 -/
def sideE (tbl : List Quint) : Bool := checkR (mirTbl tbl) &&
  (List.range 3).any fun e => (List.range 3).any fun f => (List.range 3).any fun r =>
    (List.range 2).any fun w => uniR tbl e f r w

/-- **群 D の 1 進カウンタ 4 類の検査**: 表か、その鏡像が `sideE`。 -/
def grpE (es : List Nat) (D : List Dir) : Bool :=
  sideE (URTM.Three.realize es D) || sideE (mirTbl (URTM.Three.realize es D))

/-- 段階 2e の例外: 段階 2d の例外のうち、1 進カウンタの 4 類に当たらない表。 -/
def isExcE (es : List Nat) (D : List Dir) : Bool := isExcD es D && !grpE es D

theorem sideE_bound {tbl : List Quint} (hsrc : Src3 tbl) (hcl : QClosed tbl 2) (hdir : DirConsistent tbl)
    (h : sideE tbl = true) :
    ∃ ML : Nat, ∀ (c : QConf) (a b : Int), a ≤ c.pos → c.pos ≤ b →
      (∀ x, (x < a ∨ b < x) → c.tape x = 0) → (∀ x, c.tape x < 2) →
      (QHalts tbl c ↔ qrun tbl (boundE 2 ug ML a b) c = none) := by
  unfold sideE at h
  obtain ⟨hL, hc⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨CL, ML, hLc⟩ := checkR_spec hL
  obtain ⟨e, -, hc⟩ := List.any_eq_true.mp hc
  obtain ⟨f, -, hc⟩ := List.any_eq_true.mp hc
  obtain ⟨r, -, hc⟩ := List.any_eq_true.mp hc
  obtain ⟨w, -, hc⟩ := List.any_eq_true.mp hc
  exact ⟨ML, fun c a b ha hb hz h2 =>
    halts_iff_boundE hsrc hcl hdir (unary_rside (uniR_spec hc)) hLc c a b ha hb hz h2⟩

theorem sideE_mir_bound {tbl : List Quint} (hsrc : Src3 tbl) (hcl : QClosed tbl 2) (hdir : DirConsistent tbl)
    (h : sideE (mirTbl tbl) = true) :
    ∃ ML : Nat, ∀ (c : QConf) (a b : Int), a ≤ c.pos → c.pos ≤ b →
      (∀ x, (x < a ∨ b < x) → c.tape x = 0) → (∀ x, c.tape x < 2) →
      (QHalts tbl c ↔ qrun tbl (boundE 2 ug ML a b) c = none) := by
  rw [mirTbl_eq] at h
  obtain ⟨ML, hb⟩ := sideE_bound (src3_mir hsrc) (closed_mir hcl) (dirConsistent_mir hdir) h
  refine ⟨ML, fun c a b ha hb' hz h2 => ?_⟩
  have := hb (mirQ c) (-b) (-a) (by show -b ≤ -c.pos; omega) (by show -c.pos ≤ -a; omega)
    (fun x hx => by show c.tape (-x) = 0; exact hz (-x) (by omega)) (fun x => h2 (-x))
  rw [QHalts_mir, qrun_mir] at this
  have e : boundE 2 ug ML (-b) (-a) = boundE 2 ug ML a b := by
    unfold boundE; rw [show -a - (-b - (ML : Int)) + 1 = b - (a - ML) + 1 by omega]
  rw [e] at this
  rw [this]
  cases qrun tbl (boundE 2 ug ML a b) c <;> simp

/-- 窓の幅で書いた上界。 -/
def bndE (ML w : Nat) : Nat :=
  csize 2 (w + ML + 1) * 2 * (2 * (csize 2 (w + ML + 1) * 2) + 3 + 2) +
    (2 * (csize 2 (w + ML + 1) * 2) + 3) + 1

theorem bndE_primrec (ML : Nat) : Primrec (bndE ML) := by
  have hK : Primrec fun w => csize 2 (w + ML + 1) * 2 :=
    Primrec.nat_mul.comp (csize_primrec.comp (Primrec.const 2)
      (Primrec.nat_add.comp (Primrec.nat_add.comp Primrec.id (Primrec.const ML)) (Primrec.const 1)))
      (Primrec.const 2)
  have hg : Primrec fun w => 2 * (csize 2 (w + ML + 1) * 2) + 3 :=
    Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) hK) (Primrec.const 3)
  exact (Primrec.nat_add.comp (Primrec.nat_add.comp (Primrec.nat_mul.comp hK
    (Primrec.nat_add.comp hg (Primrec.const 2))) hg) (Primrec.const 1)).of_eq fun w => rfl

theorem boundE_eq (ML m n : Nat) : boundE 2 ug ML (-(m : Int)) (n : Int) = bndE ML (m + n) := by
  unfold boundE bndE ug
  rw [show ((n : Int) - (-(m : Int) - ML) + 1).toNat = m + n + ML + 1 by omega]

section
variable {tbl : List Quint} {q₀ q₁ q₂ sg : Nat}

/-- **群 D の 1 進カウンタ 4 類の有界停止**（任意の表の正規形）。 -/
theorem okE_bound (H : RTM32 tbl q₀ q₁ q₂ sg)
    (hok : grpE (absCodes q₀ q₁ q₂ sg tbl) (absDirs q₀ q₁ q₂ tbl) = true) :
    ∃ ML : Nat, ∀ (c : QConf) (m n : ℕ), -(m : ℤ) ≤ c.pos → c.pos ≤ (n : ℤ) →
      (∀ x, (x < -(m : ℤ) ∨ (n : ℤ) < x) → c.tape x = 0) → (∀ x, c.tape x < 2) →
      (QHalts (normT (tbl := tbl) (q₀ := q₀) (q₁ := q₁) (q₂ := q₂) (σ := sg)) c ↔
        qrun (normT (tbl := tbl) (q₀ := q₀) (q₁ := q₁) (q₂ := q₂) (σ := sg)) (bndE ML (m + n)) c = none) := by
  have hsrc := realize_src3 (absCodes q₀ q₁ q₂ sg tbl) (absDirs q₀ q₁ q₂ tbl)
  have hcl := realize_closed (absCodes q₀ q₁ q₂ sg tbl) (absDirs q₀ q₁ q₂ tbl)
  have hdir := realize_dir (absCodes q₀ q₁ q₂ sg tbl) (absDirs q₀ q₁ q₂ tbl)
  unfold grpE at hok
  obtain ⟨ML, hb⟩ : ∃ ML : Nat, ∀ (c : QConf) (a b : Int), a ≤ c.pos → c.pos ≤ b →
      (∀ x, (x < a ∨ b < x) → c.tape x = 0) → (∀ x, c.tape x < 2) →
      (QHalts (URTM.Three.realize (absCodes q₀ q₁ q₂ sg tbl) (absDirs q₀ q₁ q₂ tbl)) c ↔
        qrun (URTM.Three.realize (absCodes q₀ q₁ q₂ sg tbl) (absDirs q₀ q₁ q₂ tbl)) (boundE 2 ug ML a b) c
          = none) := by
    rcases Bool.or_eq_true_iff.mp hok with h | h
    · exact sideE_bound hsrc hcl hdir h
    · exact sideE_mir_bound hsrc hcl hdir h
  refine ⟨ML, fun c m n ha hb' hz h2 => ?_⟩
  rw [← boundE_eq]
  exact hb c _ _ ha hb' hz h2

/-- **3 状態 2 記号の RTM の停止問題は、U の ID の上で計算可能**（`isExcE` の表を除く）。 -/
theorem three_halting_computable_E (H : RTM32 tbl q₀ q₁ q₂ sg)
    (hne : isExcE (absCodes q₀ q₁ q₂ sg tbl) (absDirs q₀ q₁ q₂ tbl) = false) :
    ∃ f : ZID → Bool, Computable f ∧
      ∀ z, (∀ a ∈ z.2.1 ++ z.2.2, a = 0 ∨ a ∈ [sg]) → (ZHalts tbl z ↔ f z = true) := by
  cases hD : isExcD (absCodes q₀ q₁ q₂ sg tbl) (absDirs q₀ q₁ q₂ tbl) with
  | false => exact three_halting_computable_D H hD
  | true =>
    have hE : grpE (absCodes q₀ q₁ q₂ sg tbl) (absDirs q₀ q₁ q₂ tbl) = true := by
      unfold isExcE at hne; rw [hD] at hne; simpa using hne
    obtain ⟨ML, hb⟩ := okE_bound H hE
    exact halting_computable_of_bound H (bndE_primrec ML) hb

/-- **定理（段階 2e）: `isExcE` の表を除き、3 状態 2 記号の URTM は存在しない**（Morita Def. 7.1、
    U の記号集合 {0, sg} の上の ID への符号化）。 -/
theorem no_three_two_URTM_E (H : RTM32 tbl q₀ q₁ q₂ sg)
    (hne : isExcE (absCodes q₀ q₁ q₂ sg tbl) (absDirs q₀ q₁ q₂ tbl) = false) :
    ¬ IsUTM_MoritaOver tbl [sg] :=
  not_UTM_of_halting_computable (three_halting_computable_E H hne)

end

/-! ### 残る例外の数

段階 2d の例外の上界 720 表（`excDKeys`）のうち、`grpE` に当たる 48 表（4 類）の鍵を一覧 `e48Keys` に書き、
それらが `grpE` に当たることを kernel で確かめる。残る例外はその外の 672 表に**含まれる**（上界）。 -/

/-- `grpE` に当たる 48 表の鍵（Python で類から生成。下の `e48_grpE` が kernel で検査する）。 -/
def e48Keys : List Nat := [
  239003, 239382, 289800, 306203, 326629, 328645, 345812, 347522, 713991, 714538, 731296, 746919,
  792571, 794587, 812948, 813158, 956539, 956709, 989467, 1023909, 1042640, 1043530, 1044698, 1050712,
  2133029, 2133199, 2165957, 2200399, 2219130, 2220020, 2221188, 2227202, 2361077, 2361624, 2378382, 2394005,
  2439657, 2441673, 2460034, 2460244, 2827281, 2827660, 2878078, 2894481, 2914907, 2916923, 2934090, 2935800
]

theorem e48_grpE : e48Keys.all (fun k => grpE (unkey k).1 (unkey k).2) = true := by decide +kernel

theorem e48_sub : e48Keys.all (fun k => excDKeys.contains k) = true := by decide +kernel

/-- 段階 2e の例外の鍵（の上界）。 -/
def excEKeys : List Nat := excDKeys.filter fun k => !e48Keys.contains k

/-- **段階 2e の例外の表（の上界）の一覧**。 -/
def excETables : List (List Nat × List Dir) := excEKeys.map unkey

/-- **主定理の仮定が外れる表は一覧に載る**（符号 6 つ・向き 3 つの表について）。 -/
theorem mem_excETables {es : List Nat} {D : List Dir} (h : ValidKey es D) (hx : isExcE es D = true) :
    (es, D) ∈ excETables := by
  unfold isExcE at hx
  obtain ⟨hD, hE⟩ := Bool.and_eq_true_iff.mp hx
  obtain ⟨k, hk, he⟩ := List.mem_map.mp (mem_excDTables h hD)
  refine List.mem_map.mpr ⟨k, List.mem_filter.mpr ⟨hk, ?_⟩, he⟩
  cases hc : e48Keys.contains k
  · rfl
  · exfalso
    have := List.all_eq_true.mp e48_grpE k (List.contains_iff_mem.mp hc)
    rw [he] at this
    simp only [this, Bool.not_true] at hE
    exact Bool.false_ne_true hE

/-- **段階 2e の例外は高々 672 表**（720 − 48。kernel の評価）。 -/
theorem excEKeys_length : excEKeys.length = 672 := by decide +kernel

theorem excETables_length : excETables.length = 672 := by
  unfold excETables; rw [List.length_map, excEKeys_length]

end URTM.Meta
