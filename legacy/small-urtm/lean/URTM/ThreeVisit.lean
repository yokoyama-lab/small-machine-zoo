/-
  3 状態 2 記号 RTM の停止問題の決定可能性 その 4: **訪問の検査の健全性**。**手書き**。

  `ThreeCheck.visit` の結果は、両側無限テープの実際の実行（`qrun`）について正しい。
  窓の右端を b、(−∞, b] の中身を任意の `left` とし、セル b+1, b+2, … に模様 P を置いた配置
  `vreal b left ⟨e, 1, P⟩` から:
    * `ret q P' k mp` : k 歩目にヘッドが b に戻り、状態 q、(b, ∞) の中身は P'。それまでヘッドは (b, b+mp]
    * `halt k mp` : k+1 歩目で止まる。それまでヘッドは (b, b+mp]
    * `div` : 決して止まらず、ヘッドはずっと b より右
  `left` は何でもよい（訪問のあいだ (−∞, b] は読まれも書かれもしない）。
-/
import URTM.ThreeShift
import URTM.ThreeCheck

namespace URTM.Three
open URTM URTM.TwoState

/-- (−∞, b] は `left`、b+1+i は列の i 番目（先は空白）。 -/
def glue (b : Int) (left : Int → Nat) (l : List Nat) : Int → Nat :=
  fun x => if b < x then l.getD (x - b - 1).toNat 0 else left x

/-- 訪問の配置を両側無限テープの配置に戻す。 -/
def vreal (b : Int) (left : Int → Nat) (x : VConf) : QConf := ⟨x.st, b + x.pos, glue b left x.tape⟩

theorem getD_of_le {l : List Nat} {i : Nat} (h : l.length ≤ i) : l.getD i 0 = 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]; rfl

theorem getD_append (l₁ l₂ : List Nat) (j : Nat) :
    (l₁ ++ l₂).getD j 0 = if j < l₁.length then l₁.getD j 0 else l₂.getD (j - l₁.length) 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append]
  split <;> rfl

theorem getD_zeros (l : List Nat) (hl : ∀ a ∈ l, a = 0) (j : Nat) : l.getD j 0 = 0 := by
  rw [List.getD_eq_getElem?_getD]
  cases h : l[j]? with
  | none => rfl
  | some a => exact hl a (List.mem_of_getElem? h)

theorem getD_setPad (l : List Nat) (i v j : Nat) :
    (setPad l i v).getD j 0 = if j = i then v else l.getD j 0 := by
  unfold setPad
  split
  · rename_i hi
    simp only [List.getD_eq_getElem?_getD, List.getElem?_set]
    by_cases hj : j = i
    · subst hj; simp [hi]
    · simp [Ne.symm hj, hj]
  · rename_i hi
    rw [getD_append, getD_append]
    simp only [List.length_append, List.length_replicate]
    by_cases hj : j < l.length
    · rw [if_pos (by omega), if_pos hj, if_neg (by omega)]
    · rw [getD_of_le (l := l) (by omega)]
      by_cases hj2 : j < i
      · rw [if_pos (by omega), if_neg hj, if_neg (by omega),
          getD_zeros _ (fun a ha => (List.eq_of_mem_replicate ha))]
      · rw [if_neg (by omega)]
        by_cases hj3 : j = i
        · rw [if_pos hj3, show j - (l.length + (i - l.length)) = 0 by omega]; rfl
        · rw [if_neg hj3, getD_of_le (by simp; omega)]

theorem trim_spec (l : List Nat) : ∃ z : List Nat, (∀ a ∈ z, a = 0) ∧ l = trim l ++ z := by
  refine ⟨(l.reverse.takeWhile (· == 0)).reverse, ?_, ?_⟩
  · intro a ha
    have hall := List.all_takeWhile (p := (· == 0)) (l := l.reverse)
    rw [List.all_eq_true] at hall
    simpa using hall a (List.mem_reverse.mp ha)
  · have h := List.takeWhile_append_dropWhile (p := (· == 0)) (l := l.reverse)
    unfold trim
    calc l = l.reverse.reverse := by simp
      _ = (l.reverse.takeWhile (· == 0) ++ l.reverse.dropWhile (· == 0)).reverse := by rw [h]
      _ = _ := by rw [List.reverse_append]

theorem getD_trim (l : List Nat) (j : Nat) : (trim l).getD j 0 = l.getD j 0 := by
  obtain ⟨z, hz, hl⟩ := trim_spec l
  conv => rhs; rw [hl]
  rw [getD_append]
  split
  · rfl
  · rw [getD_of_le (by omega), getD_zeros z hz]

theorem glue_trim (b : Int) (left : Int → Nat) (l : List Nat) : glue b left (trim l) = glue b left l := by
  funext x; unfold glue; split
  · rw [getD_trim]
  · rfl

theorem vmove_real (d : Dir) (b : Int) (p : Nat) (hp : 1 ≤ p) :
    move d (b + p) = b + (vmove d p : Nat) := by
  cases d with
  | L => show b + p - 1 = b + ((p - 1 : Nat) : Int); omega
  | Z => rfl
  | R => show b + p + 1 = b + ((p + 1 : Nat) : Int); push_cast; omega

/-- **訪問の 1 歩は実際の 1 歩と一致する**（ヘッドが b より右のとき）。 -/
theorem vstep_real (tbl : List Quint) (b : Int) (left : Int → Nat) (x : VConf) (hp : 1 ≤ x.pos) :
    qstep tbl (vreal b left x) = (vstep tbl x).map (vreal b left) := by
  have hread : (vreal b left x).tape (vreal b left x).pos = x.tape.getD (x.pos - 1) 0 := by
    show glue b left x.tape (b + x.pos) = _
    unfold glue
    rw [if_pos (by omega)]
    congr 1; omega
  unfold qstep vstep
  rw [hread]
  show (match find? tbl x.st (x.tape.getD (x.pos - 1) 0) with
    | none => none
    | some r => some (⟨r.q, move r.d (b + x.pos), write (glue b left x.tape) (b + x.pos) r.t⟩ : QConf)) = _
  cases find? tbl x.st (x.tape.getD (x.pos - 1) 0) with
  | none => rfl
  | some r =>
    show some (⟨r.q, move r.d (b + x.pos), write (glue b left x.tape) (b + x.pos) r.t⟩ : QConf)
      = some ⟨r.q, b + (vmove r.d x.pos : Nat), glue b left (setPad x.tape (x.pos - 1) r.t)⟩
    congr 2
    · exact vmove_real r.d b x.pos hp
    · funext y
      unfold write glue
      by_cases hy : y = b + x.pos
      · subst hy
        rw [if_pos rfl, if_pos (by omega), getD_setPad, if_pos (by omega)]
      · rw [if_neg hy]
        by_cases hb : b < y
        · rw [if_pos hb, if_pos hb, getD_setPad, if_neg (by omega)]
        · rw [if_neg hb, if_neg hb]

/-! ### 訪問の結果の意味 -/

/-- 訪問の結果が、配置 X₀ からの実際の実行について言うこと。 -/
def VSpec (tbl : List Quint) (b : Int) (left : Int → Nat) (X₀ : QConf) : VOut → Prop
  | VOut.ret q P k mp => qrun tbl k X₀ = some ⟨q, b, glue b left P⟩ ∧
      ∀ t, t < k → ∀ d, qrun tbl t X₀ = some d → b + 1 ≤ d.pos ∧ d.pos ≤ b + mp
  | VOut.halt k mp => qrun tbl (k + 1) X₀ = none ∧
      ∀ t, t ≤ k → ∀ d, qrun tbl t X₀ = some d → b + 1 ≤ d.pos ∧ d.pos ≤ b + mp
  | VOut.div => ∀ n, ∃ d, qrun tbl n X₀ = some d ∧ b + 1 ≤ d.pos
  | VOut.unk => True

theorem qrun_split {tbl : List Quint} {X₀ c : QConf} {t : Nat} (h : qrun tbl t X₀ = some c) (n : Nat) :
    qrun tbl (t + n) X₀ = qrun tbl n c := by
  rw [qrun_add, h]; rfl

theorem qrun_step_of {tbl : List Quint} {X₀ c c' : QConf} {k : Nat}
    (h : qrun tbl k X₀ = some c) (hs : qstep tbl c = some c') : qrun tbl (k + 1) X₀ = some c' := by
  rw [qrun_split h 1, qrun_succ_some tbl 0 hs]; rfl

theorem qrun_step_none {tbl : List Quint} {X₀ c : QConf} {k : Nat}
    (h : qrun tbl k X₀ = some c) (hs : qstep tbl c = none) : qrun tbl (k + 1) X₀ = none := by
  rw [qrun_split h 1, qrun_succ_none tbl 0 hs]

/-- 並進周期の判定が当たれば、配置 c から先は決して止まらず、ヘッドは b + lo 以上に居る。 -/
theorem shiftMatch_sound {tbl : List Quint} {b : Int} {left : Int → Nat} {x₁ x₂ : VConf} {lo Δ : Nat}
    (hm : shiftMatch x₁ x₂ lo = true) (hΔ : 1 ≤ Δ)
    (hrun : qrun tbl Δ (vreal b left x₁) = some (vreal b left x₂))
    (hposr : ∀ t, t < Δ → ∀ d, qrun tbl t (vreal b left x₁) = some d → b + lo ≤ d.pos) :
    ∀ n, ∃ d, qrun tbl n (vreal b left x₁) = some d ∧ b + lo ≤ d.pos := by
  unfold shiftMatch at hm
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hm
  obtain ⟨⟨⟨⟨hst, hle⟩, hlo1⟩, hlo2⟩, hall⟩ := hm
  have hall' : ∀ i, x₁.tape.getD (lo - 1 + i) 0 = x₂.tape.getD (lo - 1 + (x₂.pos - x₁.pos) + i) 0 := by
    intro i
    by_cases hi : i < max (x₁.tape.length + 1) (x₂.tape.length + 1)
    · exact hall i hi
    · rw [getD_of_le (by omega), getD_of_le (by omega)]
  refine qescapeG (vreal b left x₁) (vreal b left x₂) Δ ((x₂.pos : Int) - x₁.pos) (b + lo) hΔ
    (by omega) hrun hposr hst.symm ?_ ?_
  · show b + (x₂.pos : Int) = b + x₁.pos + ((x₂.pos : Int) - x₁.pos); omega
  · intro y hy
    show glue b left x₂.tape y = glue b left x₁.tape (y - ((x₂.pos : Int) - x₁.pos))
    unfold glue
    rw [if_pos (by omega), if_pos (by omega)]
    have := hall' ((y - b - 1).toNat - (lo - 1) - (x₂.pos - x₁.pos))
    rw [show lo - 1 + (x₂.pos - x₁.pos) + ((y - b - 1).toNat - (lo - 1) - (x₂.pos - x₁.pos))
        = (y - b - 1).toNat by omega] at this
    rw [← this]
    congr 1; omega

/-- **訪問の検査の健全性**（不変条件つきの一般形）。 -/
theorem visitAux_sound (tbl : List Quint) (b : Int) (left : Int → Nat) (X₀ : QConf) :
    ∀ (fuel : Nat) (x : VConf) (h : Hist) (k mp : Nat),
      qrun tbl k X₀ = some (vreal b left x) → 1 ≤ x.pos → x.pos ≤ mp →
      (∀ t, t < k → ∀ d, qrun tbl t X₀ = some d → b + 1 ≤ d.pos ∧ d.pos ≤ b + mp) →
      (∀ e ∈ h, ∃ t, t < k ∧ qrun tbl t X₀ = some (vreal b left e.1) ∧
        ∀ u, t ≤ u → u ≤ k → ∀ d, qrun tbl u X₀ = some d → b + e.2 ≤ d.pos) →
      VSpec tbl b left X₀ (visitAux tbl fuel x h k mp) := by
  intro fuel
  induction fuel with
  | zero => intro x h k mp _ _ _ _ _; trivial
  | succ fuel ih =>
    intro x h k mp hk hx1 hxm hpre hh
    have hreal := vstep_real tbl b left x hx1
    unfold visitAux
    cases hv : vstep tbl x with
    | none =>
      simp only
      refine ⟨qrun_step_none hk (by rw [hreal, hv]; rfl), fun t ht d hd => ?_⟩
      rcases Nat.lt_or_ge t k with htk | htk
      · exact hpre t htk d hd
      · have : t = k := by omega
        subst this; rw [hk] at hd; cases hd
        show b + 1 ≤ b + (x.pos : Int) ∧ b + (x.pos : Int) ≤ b + mp; omega
    | some y =>
      simp only
      have hk1 : qrun tbl (k + 1) X₀ = some (vreal b left y) :=
        qrun_step_of hk (by rw [hreal, hv]; rfl)
      -- k 歩目までの位置
      have hpre' : ∀ t, t < k + 1 → ∀ d, qrun tbl t X₀ = some d → b + 1 ≤ d.pos ∧ d.pos ≤ b + mp := by
        intro t ht d hd
        rcases Nat.lt_or_ge t k with htk | htk
        · exact hpre t htk d hd
        · have : t = k := by omega
          subst this; rw [hk] at hd; cases hd
          show b + 1 ≤ b + (x.pos : Int) ∧ b + (x.pos : Int) ≤ b + mp; omega
      by_cases hy0 : y.pos = 0
      · rw [if_pos hy0]
        refine ⟨?_, hpre'⟩
        rw [hk1]; unfold vreal; rw [hy0, glue_trim]; simp
      · rw [if_neg hy0]
        -- 履歩の不変条件（k+1 歩目まで）
        have hh' : ∀ e ∈ histUpdate ((x, x.pos) :: h) y.pos, ∃ t, t < k + 1 ∧
            qrun tbl t X₀ = some (vreal b left e.1) ∧
            ∀ u, t ≤ u → u ≤ k + 1 → ∀ d, qrun tbl u X₀ = some d → b + e.2 ≤ d.pos := by
          intro e he
          unfold histUpdate at he
          obtain ⟨e₀, he₀, rfl⟩ := List.mem_map.mp he
          rcases List.mem_cons.mp he₀ with rfl | he₀
          · refine ⟨k, by omega, hk, fun u hu1 hu2 d hd => ?_⟩
            rcases Nat.lt_or_ge u (k + 1) with hu | hu
            · have : u = k := by omega
              subst this; rw [hk] at hd; cases hd
              show b + ((min x.pos y.pos : Nat) : Int) ≤ b + x.pos; omega
            · have : u = k + 1 := by omega
              subst this; rw [hk1] at hd; cases hd
              show b + ((min x.pos y.pos : Nat) : Int) ≤ b + y.pos; omega
          · obtain ⟨t, ht, htr, hlb⟩ := hh e₀ he₀
            refine ⟨t, by omega, htr, fun u hu1 hu2 d hd => ?_⟩
            rcases Nat.lt_or_ge u (k + 1) with hu | hu
            · have := hlb u hu1 (by omega) d hd
              show b + ((min e₀.2 y.pos : Nat) : Int) ≤ d.pos; omega
            · have : u = k + 1 := by omega
              subst this; rw [hk1] at hd; cases hd
              show b + ((min e₀.2 y.pos : Nat) : Int) ≤ b + y.pos; omega
        by_cases hit : histHit (histUpdate ((x, x.pos) :: h) y.pos) y = true
        · rw [if_pos hit]
          unfold histHit at hit
          obtain ⟨e, he, hme⟩ := List.any_eq_true.mp hit
          obtain ⟨t, ht, htr, hlb⟩ := hh' e he
          have hΔ : qrun tbl (k + 1 - t) (vreal b left e.1) = some (vreal b left y) := by
            rw [← qrun_split htr, show t + (k + 1 - t) = k + 1 by omega]; exact hk1
          have hdiv := shiftMatch_sound (tbl := tbl) (b := b) (left := left) hme (by omega) hΔ
            (fun s hs d hd => by
              have := hlb (t + s) (by omega) (by omega) d (by rw [qrun_split htr]; exact hd)
              have hmin : min e.2 y.pos ≤ e.2 := Nat.min_le_left _ _
              omega)
          have hlo1 : 1 ≤ min e.2 y.pos := by
            unfold shiftMatch at hme
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hme
            exact hme.1.1.2
          intro n
          rcases Nat.lt_or_ge n t with hn | hn
          · obtain ⟨d, hd⟩ : ∃ d, qrun tbl n X₀ = some d := by
              cases hq : qrun tbl n X₀ with
              | none =>
                have := qrun_none_mono tbl X₀ n t hq (by omega)
                rw [htr] at this; cases this
              | some d => exact ⟨d, rfl⟩
            exact ⟨d, hd, (hpre' n (by omega) d hd).1⟩
          · obtain ⟨d, hd, hdp⟩ := hdiv (n - t)
            refine ⟨d, by rw [show n = t + (n - t) by omega, qrun_split htr]; exact hd, ?_⟩
            omega
        · rw [if_neg hit]
          refine ih y _ (k + 1) (max mp y.pos) hk1 (by omega) (by omega) ?_ hh'
          intro t ht d hd
          have := hpre' t ht d hd
          constructor
          · exact this.1
          · have : mp ≤ max mp y.pos := Nat.le_max_left _ _; omega

/-- **訪問の検査の健全性**。 -/
theorem visit_sound (tbl : List Quint) (b : Int) (left : Int → Nat) (e : Nat) (P : List Nat) :
    VSpec tbl b left (vreal b left ⟨e, 1, P⟩) (visit tbl e P) :=
  visitAux_sound tbl b left _ visitFuel ⟨e, 1, P⟩ [] 0 1 rfl (Nat.le_refl 1) (Nat.le_refl 1)
    (fun t ht => absurd ht (by omega)) (fun e he => absurd he (by simp))

end URTM.Three
