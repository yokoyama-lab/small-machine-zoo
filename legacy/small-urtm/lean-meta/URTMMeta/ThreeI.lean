/-
  3 状態 2 記号の URTM（段階 2e の 5）: **群 D のうち「カウンタのセル」の 12 類**（I 族、144 表）。**手書き**。

  向き: 開いている側を右にそろえる。右へ動いて入る状態は e（要求）だけ、残りの r1, r2 は左へ動いて入る（応答）。
  **セルの規則**（`Cell`）: 中身 0 のセルへの要求は即答 (e,0) → (1 を書き, L, o)、中身 1 のセルへの要求は転送
  (e,1) → (f' を書き, R, e)、中身 f' のセルへの応答 q（q = r1, r2）は即答 (q,f') → (c q を書き, L, a q)。
  すると b より右（初め空白）は、同じセルが並んだカスケードになる。n 回目の訪問は応答 `wc n` を返し、
  右の中身は `pc n` から `pc (n+1)` になる（`cell_visit`）。
  応答の列 w は射 ψ（`cpsi`）の不動点 w = o ψ(o) ψ²(o) …（`ublk_prefix`）。窓 [a − ML, b]（左は段階 1 の証明書で有界）
  は、訪問の始まりの窓のテープを状態とする有限の自動機械として w を読み（`run_chain`、`phase_cut`）、止まるのは
  この自動機械が「止まった」に入るとき。自動機械が射の不動点を読む話は鳩の巣で閉じ（`dfa_morph`）、止まるなら
  訪問は 2 ^ cardI W 回未満、ヘッドは b + 2 ^ cardI W 以下（`right_boundI`）。上界は原始再帰（`bndI_primrec`）。
  検査 `grpI es D`（Bool）: 表か鏡像の表で、右にセルの規則（`cellChk`）、左に段階 1 の証明書が立つ。
  主定理 `no_three_two_URTM_I`（`isExcI = isExcH && !grpI`）。例外は高々 192 表（`excIKeys_length`）。
-/
import URTMMeta.ThreeH
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Fintype.BigOperators

namespace URTM.Meta
open URTM URTM.TwoState URTM.Three

/-! ### セルの規則 -/

/-- 右側のカウンタのセルの規則（上の説明）。 -/
structure Cell (tbl : List Quint) (e r1 r2 o f' : Nat) (a c : Nat → Nat) : Prop where
  h00 : find? tbl e 0 = some ⟨e, 0, 1, Dir.L, o⟩
  h01 : find? tbl e 1 = some ⟨e, 1, f', Dir.R, e⟩
  hq1 : find? tbl r1 f' = some ⟨r1, f', c r1, Dir.L, a r1⟩
  hq2 : find? tbl r2 f' = some ⟨r2, f', c r2, Dir.L, a r2⟩
  ho : o = r1 ∨ o = r2
  ha1 : a r1 = r1 ∨ a r1 = r2
  ha2 : a r2 = r1 ∨ a r2 = r2
  ha3 : ∀ q, a q < 3
  hc1 : c r1 < 2
  hc2 : c r2 < 2
  hr1 : r1 < 3
  hr2 : r2 < 3
  hent : ∀ ρ ∈ tbl, ρ.d = Dir.R → ρ.q = e

/-! ### 空白から始まるカスケード -/

/-- 1 番目のセルの 1 回の要求: (中身, 転送した回数, 応答の列)。 -/
def cstep (o : Nat) (a c : Nat → Nat) (s : Nat × Nat × List Nat) : Nat × Nat × List Nat :=
  if s.1 = 0 then (1, s.2.1, s.2.2 ++ [o])
  else (c (s.2.2.getD s.2.1 0), s.2.1 + 1, s.2.2 ++ [a (s.2.2.getD s.2.1 0)])

/-- n 回の要求のあとの 1 番目のセル。 -/
def cst (o : Nat) (a c : Nat → Nat) : Nat → Nat × Nat × List Nat
  | 0 => (0, 0, [])
  | n + 1 => cstep o a c (cst o a c n)

/-- n 回目の応答。 -/
def wc (o : Nat) (a c : Nat → Nat) (n : Nat) : Nat := (cst o a c (n + 1)).2.2.getD n 0

/-- n 回の訪問のあとの右の中身（セル k の中身）。 -/
def pc (o : Nat) (a c : Nat → Nat) : Nat → Nat → Nat
  | n, 0 => (cst o a c n).1
  | n, k + 1 => pc o a c (cst o a c n).2.1 k

section cascade
variable {o r1 r2 : Nat} {a c : Nat → Nat}

theorem cst_succ (n : Nat) : cst o a c (n + 1) = cstep o a c (cst o a c n) := rfl

theorem cst_len : ∀ n, (cst o a c n).2.2.length = n
  | 0 => rfl
  | n + 1 => by
    rw [cst_succ]; unfold cstep
    split_ifs <;> simp [cst_len n]

theorem cst_get_succ (n i : Nat) (hi : i < n) :
    (cst o a c (n + 1)).2.2.getD i 0 = (cst o a c n).2.2.getD i 0 := by
  rw [cst_succ]; unfold cstep
  have hl := cst_len (o := o) (a := a) (c := c) n
  split_ifs <;> simp only [List.getD_eq_getElem?_getD] <;> rw [List.getElem?_append_left (by omega)]

theorem cst_get (n i : Nat) (hi : i < n) : (cst o a c n).2.2.getD i 0 = wc o a c i := by
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_or_ge i n with h | h
    · rw [cst_get_succ n i h, ih h]
    · obtain rfl : i = n := by omega
      rfl

/-- 転送した回数は要求の回数より少ない（中身が 0 でなければ）。 -/
theorem cst_m_le : ∀ n, ((cst o a c n).1 = 0 → (cst o a c n).2.1 ≤ n) ∧
    ((cst o a c n).1 ≠ 0 → (cst o a c n).2.1 + 1 ≤ n)
  | 0 => ⟨fun _ => Nat.le_refl 0, fun h => absurd rfl h⟩
  | n + 1 => by
    obtain ⟨h1, h2⟩ := cst_m_le n
    rw [cst_succ]; unfold cstep
    by_cases hx : (cst o a c n).1 = 0
    · rw [if_pos hx]; have := h1 hx
      exact ⟨fun _ => by simp only; omega, fun _ => by simp only; omega⟩
    · rw [if_neg hx]; have := h2 hx
      exact ⟨fun _ => by simp only; omega, fun _ => by simp only; omega⟩

theorem cst_m_lt {n : Nat} (hx : (cst o a c n).1 ≠ 0) : (cst o a c n).2.1 < n := by
  have := (cst_m_le n).2 hx; omega

/-- 応答の漸化式。 -/
theorem wc_eq (n : Nat) : wc o a c n =
    if (cst o a c n).1 = 0 then o else a (wc o a c (cst o a c n).2.1) := by
  show (cst o a c (n + 1)).2.2.getD n 0 = _
  rw [cst_succ]; unfold cstep
  have hl := cst_len (o := o) (a := a) (c := c) n
  split_ifs with hx
  · simp only [List.getD_eq_getElem?_getD]; rw [List.getElem?_append_right (by omega)]; simp [hl]
  · rw [← cst_get n _ (cst_m_lt hx)]
    simp only [List.getD_eq_getElem?_getD]; rw [List.getElem?_append_right (by omega)]
    simp [hl]

theorem cst_x_succ (n : Nat) : (cst o a c (n + 1)).1 =
    if (cst o a c n).1 = 0 then 1 else c (wc o a c (cst o a c n).2.1) := by
  rw [cst_succ]; unfold cstep
  split_ifs with hx
  · rfl
  · show c _ = _; rw [cst_get n _ (cst_m_lt hx)]

theorem cst_m_succ (n : Nat) : (cst o a c (n + 1)).2.1 =
    if (cst o a c n).1 = 0 then (cst o a c n).2.1 else (cst o a c n).2.1 + 1 := by
  rw [cst_succ]; unfold cstep
  split_ifs <;> rfl

theorem pc_zero : ∀ k, pc o a c 0 k = 0
  | 0 => rfl
  | k + 1 => pc_zero k

/-- 応答は r1 か r2。 -/
theorem wc_val (H1 : o = r1 ∨ o = r2) (Ha1 : a r1 = r1 ∨ a r1 = r2) (Ha2 : a r2 = r1 ∨ a r2 = r2) :
    ∀ n, wc o a c n = r1 ∨ wc o a c n = r2 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [wc_eq]
    split_ifs with hx
    · exact H1
    · rcases ih _ (cst_m_lt hx) with h | h <;> rw [h]
      · exact Ha1
      · exact Ha2

/-- 中身は 0 か 1。 -/
theorem cst_x_lt (Hc1 : c r1 < 2) (Hc2 : c r2 < 2) (H1 : o = r1 ∨ o = r2) (Ha1 : a r1 = r1 ∨ a r1 = r2)
    (Ha2 : a r2 = r1 ∨ a r2 = r2) : ∀ n, (cst o a c n).1 < 2
  | 0 => by show (0 : Nat) < 2; omega
  | n + 1 => by
    rw [cst_x_succ]
    split_ifs
    · decide
    · rcases wc_val H1 Ha1 Ha2 (cst o a c n).2.1 with h | h <;> rw [h] <;> assumption

end cascade

/-! ### 訪問 -/

section visit
variable {tbl : List Quint} {e r1 r2 o f' : Nat} {a c : Nat → Nat} (H : Cell tbl e r1 r2 o f' a c)
include H

/-- **カスケードの訪問**: 右の中身が `pc n` なら、状態 e で b+1 に入った訪問は 2n+1 歩以内に応答 `wc n` で b に戻り、
    中身は `pc (n+1)` になる。訪問中のヘッドは b+1 から b+1+n。 -/
theorem cell_visit : ∀ n (b : Int) (t : Int → Nat), rpart b t = pc o a c n →
    ∃ k t', k ≤ 2 * n + 1 ∧ qrun tbl k ⟨e, b + 1, t⟩ = some ⟨wc o a c n, b, t'⟩ ∧
      (∀ x, x ≤ b → t' x = t x) ∧ rpart b t' = pc o a c (n + 1) ∧
      ∀ i, i < k → ∀ d, qrun tbl i ⟨e, b + 1, t⟩ = some d → b + 1 ≤ d.pos ∧ d.pos ≤ b + 1 + n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro b t ht
  have hx0 : t (b + 1) = (cst o a c n).1 := by
    have := congrFun ht 0; simpa [rpart, pc] using this
  by_cases hx : (cst o a c n).1 = 0
  · -- 即答
    refine ⟨1, write t (b + 1) 1, by omega, ?_, fun x hx' => write_off _ _ _ (by omega), ?_, ?_⟩
    · rw [qrun_succ_some tbl 0 (qstep_of_find (by simp only; rw [hx0, hx]; exact H.h00))]
      show some (⟨o, move Dir.L (b + 1), write t (b + 1) 1⟩ : QConf) = some (⟨wc o a c n, b, write t (b + 1) 1⟩ : QConf)
      rw [wc_eq, if_pos hx]; simp [move]
    · funext k
      cases k with
      | zero =>
        show write t (b + 1) 1 (b + 1 + ((0 : Nat) : Int)) = pc o a c (n + 1) 0
        simp only [pc, write, cst_x_succ, if_pos hx]; simp
      | succ k =>
        show write t (b + 1) 1 (b + 1 + ((k + 1 : Nat) : Int)) = pc o a c (n + 1) (k + 1)
        rw [write_off _ _ _ (by omega)]
        have := congrFun ht (k + 1)
        simp only [rpart] at this
        rw [this]
        show pc o a c (cst o a c n).2.1 k = pc o a c (cst o a c (n + 1)).2.1 k
        rw [cst_m_succ, if_pos hx]
    · intro i hi d hd
      obtain rfl : i = 0 := by omega
      simp only [qrun, Option.some.injEq] at hd
      subst hd; simp only; omega
  · -- 転送
    have hx1 : (cst o a c n).1 = 1 := by
      have := cst_x_lt H.hc1 H.hc2 H.ho H.ha1 H.ha2 n; omega
    have hmlt := cst_m_lt hx
    set m := (cst o a c n).2.1 with hm
    have hs1 : qstep tbl ⟨e, b + 1, t⟩ = some ⟨e, b + 1 + 1, write t (b + 1) f'⟩ := by
      rw [qstep_of_find (by simp only; rw [hx0, hx1]; exact H.h01)]; rfl
    have hr1 : rpart (b + 1) (write t (b + 1) f') = pc o a c m := by
      funext k
      show write t (b + 1) f' (b + 1 + 1 + k) = _
      rw [write_off _ _ _ (by omega)]
      have := congrFun ht (k + 1)
      simp only [rpart] at this
      rw [show b + 1 + 1 + (k : Int) = b + 1 + ((k + 1 : Nat) : Int) by push_cast; omega, this]
      rfl
    obtain ⟨k', t2, hk', hrun', hag', hr2, hpos'⟩ := ih m hmlt (b + 1) _ hr1
    have hq := wc_val (c := c) H.ho H.ha1 H.ha2 m
    have ht2 : t2 (b + 1) = f' := by rw [hag' _ le_rfl]; simp [write]
    have hfind : find? tbl (wc o a c m) (t2 (b + 1)) =
        some ⟨wc o a c m, f', c (wc o a c m), Dir.L, a (wc o a c m)⟩ := by
      rw [ht2]
      rcases hq with h | h <;> rw [h]
      · exact H.hq1
      · exact H.hq2
    have hs2 : qstep tbl ⟨wc o a c m, b + 1, t2⟩ =
        some ⟨a (wc o a c m), b, write t2 (b + 1) (c (wc o a c m))⟩ := by
      rw [qstep_of_find (by simp only; exact hfind)]
      show some (⟨a (wc o a c m), b + 1 - 1, _⟩ : QConf) = _
      rw [show b + 1 - 1 = b by omega]
    have e1 : qrun tbl 1 ⟨e, b + 1, t⟩ = some ⟨e, b + 1 + 1, write t (b + 1) f'⟩ := by
      rw [qrun_succ_some tbl 0 hs1]; rfl
    have e2 : qrun tbl 1 ⟨wc o a c m, b + 1, t2⟩ =
        some ⟨a (wc o a c m), b, write t2 (b + 1) (c (wc o a c m))⟩ := by
      rw [qrun_succ_some tbl 0 hs2]; rfl
    refine ⟨1 + (k' + 1), write t2 (b + 1) (c (wc o a c m)), by omega, ?_, ?_, ?_, ?_⟩
    · rw [qrun_add, e1, Option.bind_some, qrun_add, hrun', Option.bind_some, e2, wc_eq n, if_neg hx]
    · intro x hxb
      rw [write_off _ _ _ (by omega), hag' x (by omega), write_off _ _ _ (by omega)]
    · funext k
      cases k with
      | zero =>
        show write t2 (b + 1) (c (wc o a c m)) (b + 1 + ((0 : Nat) : Int)) = pc o a c (n + 1) 0
        simp only [pc, write, cst_x_succ, if_neg hx]; simp [hm]
      | succ k =>
        show write t2 (b + 1) (c (wc o a c m)) (b + 1 + ((k + 1 : Nat) : Int)) = pc o a c (n + 1) (k + 1)
        rw [write_off _ _ _ (by omega)]
        have := congrFun hr2 k
        simp only [rpart] at this
        rw [show b + 1 + ((k + 1 : Nat) : Int) = b + 1 + 1 + (k : Int) by push_cast; omega, this]
        show pc o a c (m + 1) k = pc o a c (cst o a c (n + 1)).2.1 k
        rw [cst_m_succ, if_neg hx]
    · intro i hi d hd
      rcases Nat.eq_zero_or_pos i with h0 | hpos
      · subst h0; simp only [qrun, Option.some.injEq] at hd; subst hd; simp only; omega
      · obtain ⟨i', rfl⟩ : ∃ i', i = 1 + i' := ⟨i - 1, by omega⟩
        rw [qrun_add, e1, Option.bind_some] at hd
        rcases Nat.lt_or_ge i' k' with hlt | hge
        · have := hpos' i' hlt d hd
          constructor <;> omega
        · obtain rfl : i' = k' := by omega
          rw [hrun'] at hd
          simp only [Option.some.injEq] at hd
          subst hd; simp only; omega

end visit

/-! ### 応答の列は射の不動点: w = o ψ(w) -/

/-- 応答 q を受けたセルが出す列（中身が 1 に戻れば次の要求は転送、0 に戻れば次の要求は即答 o）。 -/
def cpsi (o : Nat) (a c : Nat → Nat) (q : Nat) : List Nat := if c q = 1 then [a q] else [a q, o]

/-- U_0 = [o]、U_{j+1} = o :: ψ(U_j)（= o ψ(o) … ψ^{j+1}(o)）。 -/
def ublk (ψ : Nat → List Nat) (o : Nat) : Nat → List Nat
  | 0 => [o]
  | j + 1 => o :: (ublk ψ o j).flatMap ψ

section morph
variable {o r1 r2 : Nat} {a c : Nat → Nat}

/-- 1 番目のセルの不変条件: o :: ψ(消費した列) = 出した列 ++ （中身が 0 なら次に出す o）。 -/
theorem cst_inv (Hc1 : c r1 < 2) (Hc2 : c r2 < 2) (H1 : o = r1 ∨ o = r2) (Ha1 : a r1 = r1 ∨ a r1 = r2)
    (Ha2 : a r2 = r1 ∨ a r2 = r2) : ∀ n,
    o :: ((cst o a c n).2.2.take (cst o a c n).2.1).flatMap (cpsi o a c) =
      (cst o a c n).2.2 ++ (if (cst o a c n).1 = 0 then [o] else [])
  | 0 => rfl
  | n + 1 => by
    have ih := cst_inv Hc1 Hc2 H1 Ha1 Ha2 n
    have hl := cst_len (o := o) (a := a) (c := c) n
    have hm := cst_m_le (o := o) (a := a) (c := c) n
    rw [cst_succ]; unfold cstep
    by_cases hx : (cst o a c n).1 = 0
    · rw [if_pos hx] at ih ⊢
      simp only
      rw [List.take_append_of_le_length (by rw [hl]; exact hm.1 hx), ih]
      simp
    · rw [if_neg hx] at ih ⊢
      simp only
      have hlt := cst_m_lt hx
      rw [List.take_append_of_le_length (by rw [hl]; omega), List.take_add_one,
        List.getElem?_eq_getElem (by rw [hl]; exact hlt)]
      simp only [Option.toList_some, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
        List.append_nil]
      rw [← List.cons_append, ih, List.append_nil, List.append_assoc]
      congr 1
      have hq : (cst o a c n).2.2[(cst o a c n).2.1]'(by rw [hl]; exact hlt) =
          (cst o a c n).2.2.getD (cst o a c n).2.1 0 := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hl]; exact hlt)]
      rw [hq]
      have hv := cst_get (o := o) (a := a) (c := c) n _ hlt
      have hcv : c ((cst o a c n).2.2.getD (cst o a c n).2.1 0) < 2 := by
        rw [hv]; rcases wc_val (c := c) H1 Ha1 Ha2 (cst o a c n).2.1 with h | h <;> rw [h] <;> assumption
      unfold cpsi
      by_cases h1 : c ((cst o a c n).2.2.getD (cst o a c n).2.1 0) = 1
      · rw [if_pos h1, if_neg (by omega)]; simp
      · rw [if_neg h1, if_pos (by omega)]; simp

theorem cst_m_mono : ∀ n, (cst o a c n).2.1 ≤ (cst o a c (n + 1)).2.1 := by
  intro n; rw [cst_m_succ]; split_ifs <;> omega

theorem cst_m_mono' (n k : Nat) : (cst o a c n).2.1 ≤ (cst o a c (n + k)).2.1 := by
  induction k with
  | zero => exact le_rfl
  | succ k ih => exact ih.trans (cst_m_mono (n + k))

theorem cst_m_two : ∀ k, k ≤ (cst o a c (2 * k)).2.1
  | 0 => Nat.zero_le _
  | k + 1 => by
    have ih := cst_m_two k
    have h2 : (cst o a c (2 * k)).2.1 + 1 ≤ (cst o a c (2 * k + 2)).2.1 := by
      rw [cst_m_succ (2 * k + 1), cst_m_succ (2 * k), cst_x_succ (2 * k)]
      by_cases hx : (cst o a c (2 * k)).1 = 0
      · rw [if_pos hx, if_pos hx, if_neg (by omega)]
      · rw [if_neg hx, if_neg hx]; split_ifs <;> omega
    rw [show 2 * (k + 1) = 2 * k + 2 by omega]; omega

/-- **U_j は応答の列 w の接頭辞**。 -/
theorem ublk_prefix (Hc1 : c r1 < 2) (Hc2 : c r2 < 2) (H1 : o = r1 ∨ o = r2) (Ha1 : a r1 = r1 ∨ a r1 = r2)
    (Ha2 : a r2 = r1 ∨ a r2 = r2) : ∀ j i, i < (ublk (cpsi o a c) o j).length →
    wc o a c i = (ublk (cpsi o a c) o j).getD i 0
  | 0, i, hi => by
    simp only [ublk, List.length_singleton] at hi
    obtain rfl : i = 0 := by omega
    rw [wc_eq]; simp [cst, ublk]
  | j + 1, i, hi => by
    have ih := ublk_prefix Hc1 Hc2 H1 Ha1 Ha2 j
    set u := ublk (cpsi o a c) o j with hu
    set M := (ublk (cpsi o a c) o (j + 1)).length with hM
    -- 十分大きい n
    have hmn : u.length ≤ (cst o a c (2 * u.length + M)).2.1 := by
      have := cst_m_two (o := o) (a := a) (c := c) u.length
      have := cst_m_mono' (o := o) (a := a) (c := c) (2 * u.length) M
      omega
    set n := 2 * u.length + M with hn
    have hl := cst_len (o := o) (a := a) (c := c) n
    have hmle : (cst o a c n).2.1 ≤ n := by
      have := cst_m_le (o := o) (a := a) (c := c) n
      by_cases hx : (cst o a c n).1 = 0
      · exact this.1 hx
      · have := this.2 hx; omega
    -- 消費した列の先頭は u
    have htake : ((cst o a c n).2.2.take (cst o a c n).2.1).take u.length = u := by
      rw [List.take_take, Nat.min_eq_left hmn]
      apply List.ext_getElem
      · rw [List.length_take, hl]; omega
      · intro k hk1 hk2
        rw [List.getElem_take]
        have e1 := cst_get (o := o) (a := a) (c := c) n k (by rw [List.length_take] at hk1; omega)
        have e2 := ih k hk2
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hl]; rw [List.length_take] at hk1; omega),
          Option.getD_some] at e1
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk2, Option.getD_some] at e2
        rw [e1, e2]
    have hinv := cst_inv Hc1 Hc2 H1 Ha1 Ha2 n
    rw [← List.take_append_drop u.length ((cst o a c n).2.2.take (cst o a c n).2.1), htake,
      List.flatMap_append, ← List.cons_append] at hinv
    -- ublk (j+1) は hinv の左辺の接頭辞
    have hpre : ublk (cpsi o a c) o (j + 1) = o :: u.flatMap (cpsi o a c) := rfl
    have hiM : i < M := hi
    have hin : i < n := by omega
    have := congrArg (fun l => l.getD i 0) hinv
    rw [List.getD_append _ _ _ _ (by rw [← hpre]; exact hi), List.getD_append _ _ _ _ (by rw [hl]; exact hin),
      ← hpre] at this
    rw [this, cst_get n i hin]

end morph

/-! ### 射の不動点を読む有限の自動機械（純粋な組合せ） -/

/-- ψ^j(q)（外側から展開した形）。 -/
def pw (ψ : Nat → List Nat) : Nat → Nat → List Nat
  | 0, q => [q]
  | j + 1, q => (ψ q).flatMap (pw ψ j)

/-- ブロック 0..j−1 をつないだ列 V_j = ψ^0(o) ψ^1(o) … ψ^{j−1}(o)。 -/
def vblk (ψ : Nat → List Nat) (o : Nat) : Nat → List Nat
  | 0 => []
  | j + 1 => vblk ψ o j ++ pw ψ j o

theorem len_flatMap_le {f : Nat → List Nat} {B : Nat} :
    ∀ l : List Nat, (∀ x ∈ l, (f x).length ≤ B) → (l.flatMap f).length ≤ l.length * B
  | [], _ => by simp
  | x :: l, h => by
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    have h1 := len_flatMap_le l (fun y hy => h y (by simp [hy]))
    have h2 := h x (by simp)
    rw [Nat.succ_mul]; omega

section pure
variable (ψ : Nat → List Nat)

theorem pw_flatMap : ∀ j q, (pw ψ j q).flatMap ψ = pw ψ (j + 1) q
  | 0, q => by simp [pw]
  | j + 1, q => by
    show ((ψ q).flatMap (pw ψ j)).flatMap ψ = (ψ q).flatMap (pw ψ (j + 1))
    rw [List.flatMap_assoc]
    congr 1; funext x; exact pw_flatMap j x

theorem ublk_eq_vblk (o : Nat) : ∀ j, ublk ψ o j = vblk ψ o (j + 1)
  | 0 => rfl
  | j + 1 => by
    show o :: (ublk ψ o j).flatMap ψ = vblk ψ o (j + 1) ++ pw ψ (j + 1) o
    rw [ublk_eq_vblk o j]
    have key : ∀ k, o :: (vblk ψ o (k + 1)).flatMap ψ = vblk ψ o (k + 1) ++ pw ψ (k + 1) o := by
      intro k
      induction k with
      | zero => simp [vblk, pw]
      | succ k ih =>
        show o :: (vblk ψ o (k + 1) ++ pw ψ (k + 1) o).flatMap ψ =
          (vblk ψ o (k + 1) ++ pw ψ (k + 1) o) ++ pw ψ (k + 2) o
        rw [List.flatMap_append, ← List.cons_append, ih, pw_flatMap, List.append_assoc]
    exact key j

theorem pw_len (hψ : ∀ q, 1 ≤ (ψ q).length ∧ (ψ q).length ≤ 2) : ∀ j q, 1 ≤ (pw ψ j q).length ∧ (pw ψ j q).length ≤ 2 ^ j
  | 0, q => by simp [pw]
  | j + 1, q => by
    show 1 ≤ ((ψ q).flatMap (pw ψ j)).length ∧ ((ψ q).flatMap (pw ψ j)).length ≤ 2 ^ (j + 1)
    obtain ⟨h1, h2⟩ := hψ q
    rw [List.length_flatMap]
    constructor
    · obtain ⟨x, l, hxl⟩ : ∃ x l, ψ q = x :: l := by
        cases h : ψ q with
        | nil => rw [h] at h1; simp at h1
        | cons x l => exact ⟨x, l, rfl⟩
      rw [hxl]; simp only [List.map_cons, List.sum_cons]
      have := (pw_len hψ j x).1; omega
    · have hb : ∀ x ∈ (ψ q), (pw ψ j x).length ≤ 2 ^ j := fun x _ => (pw_len hψ j x).2
      have := len_flatMap_le (ψ q) hb
      rw [List.length_flatMap] at this
      rw [Nat.pow_succ]
      calc _ ≤ (ψ q).length * 2 ^ j := this
        _ ≤ 2 * 2 ^ j := Nat.mul_le_mul_right _ h2
        _ = 2 ^ j * 2 := Nat.mul_comm _ _

theorem vblk_len (hψ : ∀ q, 1 ≤ (ψ q).length ∧ (ψ q).length ≤ 2) (o : Nat) :
    ∀ j, j ≤ (vblk ψ o j).length ∧ (vblk ψ o j).length < 2 ^ j
  | 0 => by simp [vblk]
  | j + 1 => by
    obtain ⟨h1, h2⟩ := vblk_len hψ o j
    obtain ⟨h3, h4⟩ := pw_len ψ hψ j o
    simp only [vblk, List.length_append, Nat.pow_succ]
    omega

variable {S : Type} [Fintype S] [DecidableEq S] (δ : S → Nat → S) (h : S)

/-- **有限の自動機械が o ψ(o) ψ²(o) … を読む**: 吸収的な状態 h にいつか入るなら、ブロック C 個以内に入る
    （C は (状態, 文字 0・1・2 ごとの変換) の組の数）。o は 3 未満で、ψ は 3 未満の文字を 3 未満の文字の列へ写す。 -/
theorem dfa_morph (hh : ∀ q, δ h q = h) (o : Nat) (ho : o < 3)
    (hψ2 : ∀ q, q < 3 → ∀ x ∈ ψ q, x < 3)
    (s₀ : S) (hJ : ∃ J, (vblk ψ o J).foldl δ s₀ = h) :
    (vblk ψ o (Fintype.card (S × (Fin 3 → S → S)))).foldl δ s₀ = h := by
  classical
  -- ブロックの変換と状態（文字 i の変換を i 番目に置く）
  let F : Nat → Fin 3 → S → S := fun j i s => (pw ψ j i.val).foldl δ s
  let st : Nat → S := fun j => (vblk ψ o j).foldl δ s₀
  let p : Nat → S × (Fin 3 → S → S) := fun j => (st j, F j)
  let io : Fin 3 := ⟨o, ho⟩
  -- 次の組は今の組で決まる
  let Φ : (Fin 3 → S → S) → Fin 3 → S → S := fun G i s =>
    (ψ i.val).foldl (fun s x => if hx : x < 3 then G ⟨x, hx⟩ s else s) s
  have hF : ∀ j, F (j + 1) = Φ (F j) := by
    intro j; funext i s
    show ((ψ i.val).flatMap (pw ψ j)).foldl δ s = _
    rw [List.foldl_flatMap]
    apply List.foldl_ext
    intro s' x hx
    have hx2 := hψ2 i.val i.isLt x hx
    rw [dif_pos hx2]
  have hst : ∀ j, st (j + 1) = F j io (st j) := by
    intro j
    show (vblk ψ o j ++ pw ψ j o).foldl δ s₀ = (pw ψ j o).foldl δ ((vblk ψ o j).foldl δ s₀)
    rw [List.foldl_append]
  have hp : ∀ j, p (j + 1) = ((p j).2 io (p j).1, Φ (p j).2) := by
    intro j; show (st (j + 1), F (j + 1)) = _; rw [hst, hF]
  -- 吸収的
  have habs : ∀ (u : List Nat), u.foldl δ h = h := by
    intro u; induction u with
    | nil => rfl
    | cons x u ih => simp only [List.foldl_cons, hh, ih]
  have hmono : ∀ j k, st j = h → st (j + k) = h := by
    intro j k hj
    induction k with
    | zero => exact hj
    | succ k ih =>
      show st (j + k + 1) = h
      rw [hst, ih]; exact habs _
  -- 鳩の巣
  set C := Fintype.card (S × (Fin 3 → S → S)) with hC
  obtain ⟨x, y, hxy, hpxy⟩ := Fintype.exists_ne_map_eq_of_card_lt (fun i : Fin (C + 1) => p i.val)
    (by rw [Fintype.card_fin]; omega)
  obtain ⟨i, k, hik, hkC, hpe⟩ : ∃ i k, i < k ∧ k ≤ C ∧ p i = p k := by
    rcases Nat.lt_or_gt_of_ne (fun e => hxy (Fin.ext e)) with hl | hl
    · exact ⟨x.val, y.val, hl, by omega, hpxy⟩
    · exact ⟨y.val, x.val, hl, by omega, hpxy.symm⟩
  have hper : ∀ t, p (i + t) = p (k + t) := by
    intro t
    induction t with
    | zero => exact hpe
    | succ t ih => rw [← Nat.add_assoc, ← Nat.add_assoc, hp, hp, ih]
  -- 最初に h に入るブロック
  obtain ⟨J, hJ⟩ := hJ
  have hex : ∃ J, st J = h := ⟨J, hJ⟩
  have hJ₀h : st (Nat.find hex) = h := Nat.find_spec hex
  by_cases hle : Nat.find hex ≤ C
  · have := hmono (Nat.find hex) (C - Nat.find hex) hJ₀h
    rwa [show Nat.find hex + (C - Nat.find hex) = C by omega] at this
  · exfalso
    obtain ⟨t, ht⟩ : ∃ t, Nat.find hex = k + t := ⟨Nat.find hex - k, by omega⟩
    have e : st (Nat.find hex) = st (i + t) := by
      rw [ht]; exact (congrArg Prod.fst (hper t)).symm
    have hlt : i + t < Nat.find hex := by omega
    exact Nat.find_min hex hlt (e ▸ hJ₀h)

end pure

/-! ### 窓の自動機械 -/

/-- 窓 [lo, b] の幅。 -/
def wW (lo b : Int) : Nat := (b - lo + 1).toNat

/-- 窓のテープの符号（1 なら true）。 -/
def wenc (lo b : Int) (tp : Int → Nat) : Fin (wW lo b) → Bool := fun i => tp (lo + (i.val : Int)) == 1

/-- 符号から戻したテープ（窓の外は 0）。 -/
def wdec (lo b : Int) (τ : Fin (wW lo b) → Bool) : Int → Nat := fun x =>
  if h : lo ≤ x ∧ x ≤ b then (if τ ⟨(x - lo).toNat, by unfold wW; omega⟩ then 1 else 0) else 0

/-- 自動機械の状態: none = 止まった、some none = 使わない（死んだ）、some (some τ) = 訪問の始まりの窓のテープ。 -/
abbrev WS (lo b : Int) := Option (Option (Fin (wW lo b) → Bool))

/-- 時刻 t の次の 1 歩で、止まるか b より右へ出る。 -/
def wev (tbl : List Quint) (b : Int) (d : QConf) (t : Nat) : Prop :=
  match qrun tbl (t + 1) d with
  | none => True
  | some d' => b < d'.pos

/-- 出来事の結果。 -/
def wres (lo b : Int) : Option QConf → WS lo b
  | none => none
  | some d' => some (some (wenc lo b d'.tape))

open Classical in
/-- 窓の中の段: 最初の出来事まで走らせる（出来事が無ければ「死んだ」）。 -/
noncomputable def phase (tbl : List Quint) (lo b : Int) (d : QConf) : WS lo b :=
  if hE : ∃ t, wev tbl b d t then wres lo b (qrun tbl (Nat.find hE + 1) d) else some none

/-- 自動機械の遷移: 訪問の始まりのテープ τ に応答 q が戻ったら、次の段。 -/
noncomputable def wdelta (tbl : List Quint) (lo b : Int) : WS lo b → Nat → WS lo b
  | none, _ => none
  | some none, _ => some none
  | some (some τ), q => phase tbl lo b ⟨q, b, wdec lo b τ⟩

section phasecut
variable {tbl : List Quint} {b : Int}

/-- 切り詰めが等しく b 以下に居る配置の 1 歩。 -/
theorem step_cut {e e' : QConf} (hc : cut b e = cut b e') (hp : e.pos ≤ b) :
    (qstep tbl e = none ↔ qstep tbl e' = none) ∧
      ∀ e1, qstep tbl e = some e1 → ∃ e1', qstep tbl e' = some e1' ∧ cut b e1 = cut b e1' := by
  obtain ⟨-, hpp, htp⟩ := cut_eq b hc
  have hp' : e'.pos ≤ b := by rw [← hpp]; exact hp
  refine ⟨⟨fun h => qstep_none_of_cut b hc.symm hp' h, fun h => qstep_none_of_cut b hc hp h⟩, ?_⟩
  intro e1 he1
  obtain ⟨ρ, _, hf, rfl⟩ := qstep_some he1
  have hf' : find? tbl e'.st (e'.tape e'.pos) = some ρ := by
    rw [← find_eq_of_cut (tbl := tbl) b hc hp]; exact hf
  refine ⟨⟨ρ.q, move ρ.d e'.pos, write e'.tape e'.pos ρ.t⟩, qstep_of_find hf', ?_⟩
  refine cut_eq_of (c₁ := ⟨ρ.q, move ρ.d e.pos, write e.tape e.pos ρ.t⟩)
    (c₂ := ⟨ρ.q, move ρ.d e'.pos, write e'.tape e'.pos ρ.t⟩) b rfl (by simp only; rw [hpp]) ?_
  intro x hx
  simp only [write]; rw [hpp]
  split_ifs
  · rfl
  · exact htp x hx

/-- 出来事の前は、切り詰めの等しい 2 つの実行は切り詰めが等しいまま b 以下に居る。 -/
theorem run_cut {d d' : QConf} (hc : cut b d = cut b d') (hp : d.pos ≤ b) :
    ∀ t, (∀ s, s < t → ¬ wev tbl b d s) →
      ∃ e e', qrun tbl t d = some e ∧ qrun tbl t d' = some e' ∧ cut b e = cut b e' ∧ e.pos ≤ b
  | 0, _ => ⟨d, d', rfl, rfl, hc, hp⟩
  | t + 1, hno => by
    obtain ⟨e, e', h1, h2, hce, hpe⟩ := run_cut hc hp t (fun s hs => hno s (by omega))
    have hnt := hno t (by omega)
    unfold wev at hnt
    have hq1 : qrun tbl (t + 1) d = qstep tbl e := by rw [qrun_succ_right, h1]; rfl
    have hq2 : qrun tbl (t + 1) d' = qstep tbl e' := by rw [qrun_succ_right, h2]; rfl
    rw [hq1] at hnt ⊢; rw [hq2]
    cases he1 : qstep tbl e with
    | none => rw [he1] at hnt; exact absurd trivial hnt
    | some e1 =>
      rw [he1] at hnt
      obtain ⟨e1', he1', hc1⟩ := (step_cut (tbl := tbl) hce hpe).2 e1 he1
      exact ⟨e1, e1', rfl, he1', hc1, by simp only at hnt; omega⟩

/-- 出来事の有無は切り詰めで決まる。 -/
theorem wev_cut {d d' : QConf} (hc : cut b d = cut b d') (hp : d.pos ≤ b) (t : Nat)
    (hno : ∀ s, s < t → ¬ wev tbl b d s) : (wev tbl b d t ↔ wev tbl b d' t) := by
  obtain ⟨e, e', h1, h2, hce, hpe⟩ := run_cut (tbl := tbl) hc hp t hno
  have hq1 : qrun tbl (t + 1) d = qstep tbl e := by rw [qrun_succ_right, h1]; rfl
  have hq2 : qrun tbl (t + 1) d' = qstep tbl e' := by rw [qrun_succ_right, h2]; rfl
  unfold wev; rw [hq1, hq2]
  obtain ⟨hn, hs⟩ := step_cut (tbl := tbl) hce hpe
  cases he1 : qstep tbl e with
  | none => rw [hn.mp he1]
  | some e1 =>
    obtain ⟨e1', he1', hc1⟩ := hs e1 he1
    rw [he1']
    obtain ⟨-, hpp, -⟩ := cut_eq b hc1
    simp only; rw [hpp]

/-- **段の結果は切り詰めで決まる**（窓のテープは b 以下だけを読む）。 -/
theorem phase_cut {lo : Int} {d d' : QConf} (hc : cut b d = cut b d') (hp : d.pos ≤ b) :
    phase tbl lo b d = phase tbl lo b d' := by
  classical
  have hp' : d'.pos ≤ b := by obtain ⟨-, hpp, -⟩ := cut_eq b hc; rw [← hpp]; exact hp
  -- 出来事の時刻は同じ
  have hiff : (∃ t, wev tbl b d t) ↔ (∃ t, wev tbl b d' t) := by
    constructor
    · intro hE
      refine ⟨Nat.find hE, (wev_cut (tbl := tbl) hc hp _ (fun s hs => Nat.find_min hE hs)).mp (Nat.find_spec hE)⟩
    · intro hE
      refine ⟨Nat.find hE, (wev_cut (tbl := tbl) hc.symm hp' _ (fun s hs => Nat.find_min hE hs)).mp (Nat.find_spec hE)⟩
  unfold phase
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
      obtain ⟨-, -, htp⟩ := cut_eq b hc1
      show some (some (wenc lo b e1.tape)) = some (some (wenc lo b e1'.tape))
      congr 2; funext i
      unfold wenc
      have hi := i.isLt
      unfold wW at hi
      rw [htp _ (by omega)]
  · rw [dif_neg hE, dif_neg (fun h => hE (hiff.mpr h))]

end phasecut

/-! ### 実行との対応 -/

/-- 応答の列の n 番目から V 個。 -/
def wsl (o : Nat) (a c : Nat → Nat) (n V : Nat) : List Nat := (List.range V).map fun i => wc o a c (n + i)

theorem wsl_succ (o : Nat) (a c : Nat → Nat) (n V : Nat) :
    wsl o a c n (V + 1) = wc o a c n :: wsl o a c (n + 1) V := by
  unfold wsl
  rw [List.range_succ_eq_map]
  simp only [List.map_cons, List.map_map, Nat.add_zero]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp]
  congr 1; omega

theorem wsl_add (o : Nat) (a c : Nat → Nat) (n A B : Nat) :
    wsl o a c n (A + B) = wsl o a c n A ++ wsl o a c (n + A) B := by
  induction A generalizing n with
  | zero => simp [wsl]
  | succ A ih =>
    rw [show A + 1 + B = (A + B) + 1 by omega, wsl_succ, ih, wsl_succ]
    rw [show n + 1 + A = n + (A + 1) by omega]; rfl

theorem wdec_wenc {lo b : Int} {tp : Int → Nat} (h2 : ∀ x, tp x < 2) {x : Int} (h1 : lo ≤ x) (hb : x ≤ b) :
    wdec lo b (wenc lo b tp) x = tp x := by
  unfold wdec wenc
  rw [dif_pos ⟨h1, hb⟩]
  simp only
  rw [show lo + (((x - lo).toNat : Nat) : Int) = x by omega]
  have := h2 x
  by_cases h : tp x = 1
  · simp [h]
  · have h0 : tp x = 0 := by omega
    simp [h0]

theorem wdec_out {lo b : Int} {τ : Fin (wW lo b) → Bool} {x : Int} (h : x < lo) : wdec lo b τ x = 0 := by
  unfold wdec; rw [dif_neg (by omega)]

/-- 窓の中にいる間、右の中身は変わらない。 -/
theorem rpart_const {tbl : List Quint} {c0 : QConf} {T : Nat} (hR : QHaltRun tbl c0 T) (b : Int) {t0 : Nat} :
    ∀ s, t0 + s ≤ T → (∀ u, t0 ≤ u → u < t0 + s → (qtr tbl c0 u).pos ≤ b) →
    rpart b (qtr tbl c0 (t0 + s)).tape = rpart b (qtr tbl c0 t0).tape
  | 0, _, _ => rfl
  | s + 1, hs, hb => by
    rw [← Nat.add_assoc, rpart_step b hR (by omega) (hb (t0 + s) (by omega) (by omega))]
    exact rpart_const hR b s (by omega) (fun u h1 h2 => hb u h1 (by omega))

section chain
variable {tbl : List Quint} {e r1 r2 o f' : Nat} {a c : Nat → Nat} (H : Cell tbl e r1 r2 o f' a c)
  {c0 : QConf} {T : Nat} (hR : QHaltRun tbl c0 T) {lo b : Int}
  (hzero : ∀ t, t ≤ T → ∀ x, x < lo → (qtr tbl c0 t).tape x = 0)
  (h2 : ∀ t, t ≤ T → ∀ x, (qtr tbl c0 t).tape x < 2)
include H hR hzero h2

/-- **実行と自動機械の対応**: 時刻 t0 に b 以下に居て右の中身が `pc n` なら、自動機械の連鎖は応答 wc n, wc (n+1), … を
    読んでちょうど V 個目で初めて「止まった」に入り、以後のヘッドは b+1+n+V 以下（V は残りの訪問の数）。 -/
theorem run_chain : ∀ m t0 n, T - t0 = m → t0 ≤ T → (qtr tbl c0 t0).pos ≤ b →
    rpart b (qtr tbl c0 t0).tape = pc o a c n →
    ∃ V, (wsl o a c n V).foldl (wdelta tbl lo b) (phase tbl lo b (qtr tbl c0 t0)) = none ∧
      (∀ i, i < V → (wsl o a c n i).foldl (wdelta tbl lo b) (phase tbl lo b (qtr tbl c0 t0)) ≠ none) ∧
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
  -- 出来事の前は b 以下で、実行は生きている
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
  have hph : phase tbl lo b (qtr tbl c0 t0) = wres lo b (qrun tbl (ts + 1) (qtr tbl c0 t0)) := by
    unfold phase; rw [dif_pos hE, ← hts]
  obtain ⟨hts1, hbts⟩ := hbelow (ts) le_rfl
  by_cases hT : t0 + ts + 1 ≤ T
  · -- 訪問が始まる
    rw [hrun (ts + 1) (by omega)] at hev hph
    obtain ⟨t1, ht1⟩ : ∃ t1, t1 = t0 + ts := ⟨_, rfl⟩
    have ht1' : t0 + (ts + 1) = t1 + 1 := by omega
    rw [ht1'] at hev hph
    have hbt1 : (qtr tbl c0 t1).pos ≤ b := by rw [ht1]; exact hbts
    obtain ⟨ρ, hρ, _, e1⟩ := qstep_some (hR.step t1 (by omega))
    have hd : ρ.d = Dir.R := by
      cases hrd : ρ.d with
      | L => rw [e1, hrd] at hev; simp [move] at hev; omega
      | Z => rw [e1, hrd] at hev; simp [move] at hev; omega
      | R => rfl
    have hpos1 : (qtr tbl c0 (t1 + 1)).pos = b + 1 := by
      have := hev; rw [e1, hd] at this ⊢; simp [move] at this ⊢; omega
    have hst1 : (qtr tbl c0 (t1 + 1)).st = e := by rw [e1]; exact H.hent ρ hρ hd
    have hq1 : qtr tbl c0 (t1 + 1) = ⟨e, b + 1, (qtr tbl c0 (t1 + 1)).tape⟩ := by
      rw [← hst1, ← hpos1]
    -- 右の中身は pc n のまま
    have hrp1 : rpart b (qtr tbl c0 (t1 + 1)).tape = pc o a c n := by
      have := rpart_const hR b (t0 := t0) (ts + 1) (by omega) (fun u h1 h2' => by
        have := (hbelow (u - t0) (by omega)).2
        rwa [show t0 + (u - t0) = u by omega] at this)
      rw [ht1'] at this; rw [this]; exact hrp
    obtain ⟨k, t', hk, hvis, hag, hr', hvpos⟩ := cell_visit H n b _ hrp1
    rw [← hq1] at hvis
    obtain ⟨hkT, hq2⟩ := qtr_of_run hR (by omega) hvis
    -- 帰納法
    obtain ⟨V', hV1, hV2, hV3⟩ := ih (T - (t1 + 1 + k)) (by omega) (t1 + 1 + k) (n + 1) rfl hkT
      (by rw [hq2]) (by rw [hq2]; exact hr')
    -- 自動機械の 1 歩は、戻った配置からの段
    have hstep : wdelta tbl lo b (phase tbl lo b (qtr tbl c0 t0)) (wc o a c n) =
        phase tbl lo b (qtr tbl c0 (t1 + 1 + k)) := by
      rw [hph]
      show phase tbl lo b ⟨wc o a c n, b, wdec lo b (wenc lo b (qtr tbl c0 (t1 + 1)).tape)⟩ = _
      apply phase_cut _ (le_refl b)
      rw [hq2]
      refine cut_eq_of (c₁ := ⟨wc o a c n, b, wdec lo b (wenc lo b (qtr tbl c0 (t1 + 1)).tape)⟩)
        (c₂ := ⟨wc o a c n, b, t'⟩) b rfl rfl ?_
      intro x hx
      show wdec lo b (wenc lo b (qtr tbl c0 (t1 + 1)).tape) x = t' x
      rw [hag x hx]
      by_cases hxl : lo ≤ x
      · exact wdec_wenc (h2 (t1 + 1) (by omega)) hxl hx
      · rw [wdec_out (by omega), hzero (t1 + 1) (by omega) x (by omega)]
    refine ⟨V' + 1, ?_, ?_, ?_⟩
    · rw [wsl_succ, List.foldl_cons, hstep]; exact hV1
    · intro i hi
      rcases Nat.eq_zero_or_pos i with h0 | hpos
      · subst h0; simp only [wsl, List.range_zero, List.map_nil, List.foldl_nil]
        rw [hph]; simp [wres]
      · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
        rw [wsl_succ, List.foldl_cons, hstep]; exact hV2 i' (by omega)
    · intro t htt0 htT
      by_cases hA : t ≤ t1
      · have := (hbelow (t - t0) (by omega)).2
        rw [show t0 + (t - t0) = t by omega] at this; omega
      · by_cases hB : t < t1 + 1 + k
        · have hr1 : qrun tbl (t - (t1 + 1)) ⟨e, b + 1, (qtr tbl c0 (t1 + 1)).tape⟩ = some (qtr tbl c0 t) := by
            rw [← hq1, hR.run_at (by omega)]; congr 1; congr 1; omega
          have := hvpos (t - (t1 + 1)) (by omega) _ hr1
          omega
        · have := hV3 t (by omega) htT
          push_cast at this ⊢; omega
  · -- 窓の中で止まる
    have hTe : t0 + ts = T := by omega
    rw [hdead (ts + 1) (by omega)] at hph
    refine ⟨0, ?_, fun i hi => absurd hi (by omega), ?_⟩
    · simp only [wsl, List.range_zero, List.map_nil, List.foldl_nil]; rw [hph]; rfl
    · intro t htt0 htT
      have := (hbelow (t - t0) (by omega)).2
      rw [show t0 + (t - t0) = t by omega] at this; omega

end chain

/-! ### 右側の有界性 -/

section assemble
variable {o r1 r2 : Nat} {a c : Nat → Nat}

/-- ブロックをつないだ列 V_J の要素は応答の列。 -/
theorem vblk_get (Hc1 : c r1 < 2) (Hc2 : c r2 < 2) (H1 : o = r1 ∨ o = r2) (Ha1 : a r1 = r1 ∨ a r1 = r2)
    (Ha2 : a r2 = r1 ∨ a r2 = r2) (J i : Nat) (hi : i < (vblk (cpsi o a c) o J).length) :
    (vblk (cpsi o a c) o J).getD i 0 = wc o a c i := by
  have hl : i < (ublk (cpsi o a c) o J).length := by
    rw [ublk_eq_vblk]
    show i < (vblk (cpsi o a c) o J ++ pw (cpsi o a c) J o).length
    rw [List.length_append]; omega
  rw [ublk_prefix Hc1 Hc2 H1 Ha1 Ha2 J i hl, ublk_eq_vblk]
  show (vblk (cpsi o a c) o J).getD i 0 = (vblk (cpsi o a c) o J ++ pw (cpsi o a c) J o).getD i 0
  rw [List.getD_append _ _ _ _ hi]

/-- 応答の列の先頭 V 個は V_J の先頭 V 個。 -/
theorem wsl_vblk (Hc1 : c r1 < 2) (Hc2 : c r2 < 2) (H1 : o = r1 ∨ o = r2) (Ha1 : a r1 = r1 ∨ a r1 = r2)
    (Ha2 : a r2 = r1 ∨ a r2 = r2) (J V : Nat) (hV : V ≤ (vblk (cpsi o a c) o J).length) :
    wsl o a c 0 V = (vblk (cpsi o a c) o J).take V := by
  apply List.ext_getElem
  · simp only [wsl, List.length_map, List.length_range, List.length_take]; omega
  · intro i h1 h2
    have hi : i < (vblk (cpsi o a c) o J).length := by
      simp only [wsl, List.length_map, List.length_range] at h1; omega
    simp only [wsl, List.getElem_map, List.getElem_range, List.getElem_take, Nat.zero_add]
    have := vblk_get Hc1 Hc2 H1 Ha1 Ha2 J i hi
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some] at this
    exact this.symm

end assemble

/-- 窓の自動機械の (状態, 文字ごとの変換) の組の数（窓の幅 W）。 -/
def cardI (W : Nat) : Nat := (2 ^ W + 2) * ((2 ^ W + 2) ^ (2 ^ W + 2)) ^ 3

theorem card_WS (lo b : Int) :
    Fintype.card (WS lo b × (Fin 3 → WS lo b → WS lo b)) = cardI (wW lo b) := by
  simp only [WS, Fintype.card_prod, Fintype.card_option, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin, cardI]

section rbound
variable {tbl : List Quint} {e r1 r2 o f' : Nat} {a c : Nat → Nat} (H : Cell tbl e r1 r2 o f' a c)
  {c0 : QConf} {T : Nat} (hR : QHaltRun tbl c0 T) {lo b : Int}
  (hzero : ∀ t, t ≤ T → ∀ x, x < lo → (qtr tbl c0 t).tape x = 0)
  (h2 : ∀ t, t ≤ T → ∀ x, (qtr tbl c0 t).tape x < 2)
include H hR hzero h2

/-- **右側の有界性（カウンタのセル）**: 初め b より右が空白なら、止まる実行のヘッドは b + 2 ^ cardI W 以下
    （W は窓 [lo, b] の幅）。自動機械の連鎖が止まった状態に入るのは、応答の列の先頭 |V_C| 個の中（`dfa_morph`）。 -/
theorem right_boundI (hb : c0.pos ≤ b) (hz : ∀ x, b < x → c0.tape x = 0) :
    ∀ t, t ≤ T → (qtr tbl c0 t).pos ≤ b + ((2 ^ cardI (wW lo b) : Nat) : Int) := by
  classical
  have hrp : rpart b (qtr tbl c0 0).tape = pc o a c 0 := by
    funext k
    show c0.tape (b + 1 + (k : Int)) = pc o a c 0 k
    rw [pc_zero, hz _ (by omega)]
  obtain ⟨V, hV1, hV2, hV3⟩ := run_chain H hR hzero h2 (T - 0) 0 0 rfl (Nat.zero_le _) hb hrp
  have hψ : ∀ q, 1 ≤ (cpsi o a c q).length ∧ (cpsi o a c q).length ≤ 2 := by
    intro q; unfold cpsi; split_ifs <;> simp
  have ho3 : o < 3 := by
    rcases H.ho with h | h <;> rw [h]
    · exact H.hr1
    · exact H.hr2
  have hψ2 : ∀ q, q < 3 → ∀ x ∈ cpsi o a c q, x < 3 := by
    intro q _ x hx
    unfold cpsi at hx
    split_ifs at hx
    · rw [List.mem_singleton] at hx; rw [hx]; exact H.ha3 q
    · rw [List.mem_cons, List.mem_singleton] at hx
      rcases hx with hx | hx <;> rw [hx]
      · exact H.ha3 q
      · exact ho3
  have habs : ∀ u : List Nat, u.foldl (wdelta tbl lo b) none = none := by
    intro u
    induction u with
    | nil => rfl
    | cons x u ih => exact ih
  have hJ : ∃ J, (vblk (cpsi o a c) o J).foldl (wdelta tbl lo b) (phase tbl lo b (qtr tbl c0 0)) = none := by
    refine ⟨V + 1, ?_⟩
    have hl := (vblk_len (cpsi o a c) hψ o (V + 1)).1
    rw [← List.take_append_drop V (vblk (cpsi o a c) o (V + 1)), List.foldl_append,
      ← wsl_vblk H.hc1 H.hc2 H.ho H.ha1 H.ha2 (V + 1) V (by omega), hV1, habs]
  have hC := dfa_morph (cpsi o a c) (wdelta tbl lo b) none (fun _ => rfl) o ho3 hψ2 _ hJ
  rw [card_WS] at hC
  have hL := (vblk_len (cpsi o a c) hψ o (cardI (wW lo b))).2
  have hVL : V ≤ (vblk (cpsi o a c) o (cardI (wW lo b))).length := by
    by_contra hlt
    apply hV2 (vblk (cpsi o a c) o (cardI (wW lo b))).length (by omega)
    rw [wsl_vblk H.hc1 H.hc2 H.ho H.ha1 H.ha2 _ _ le_rfl, List.take_length]
    exact hC
  have hVP : V < 2 ^ cardI (wW lo b) := lt_of_le_of_lt hVL hL
  intro t ht
  have := hV3 t (Nat.zero_le _) ht
  omega

end rbound

/-- 左右の上界があれば、止まる実行は `bound3` 歩以内に止まる（`halts_iff_bound3` の後半の写し）。 -/
theorem bound_of_window {tbl : List Quint} (hsrc : Src3 tbl) (hcl : QClosed tbl 2) {c : QConf} {T : Nat}
    (hR : QHaltRun tbl c T) (MR ML : Nat) (a b : Int) (hz : ∀ x, (x < a ∨ b < x) → c.tape x = 0)
    (h2 : ∀ x, c.tape x < 2) (hl : ∀ t, t ≤ T → a - ML ≤ (qtr tbl c t).pos)
    (hr : ∀ t, t ≤ T → (qtr tbl c t).pos ≤ b + MR) :
    qrun tbl (bound3 MR ML a b) c = none := by
  obtain ⟨W, hW⟩ : ∃ W : Nat, W = ((b + MR) - (a - ML) + 1).toNat := ⟨_, rfl⟩
  have hWi : (W : Int) = (b + MR) - (a - ML) + 1 := by
    have := hl 0 (Nat.zero_le _); have := hr 0 (Nat.zero_le _)
    rw [hW]; omega
  have hinw : ∀ t, t ≤ T → InWin 2 (a - ML) W (URTM.Three.toC2 (qtr tbl c t)) := by
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
        (fun t => ccode 2 (a - ML) W (URTM.Three.toC2 (qtr tbl c t))) (fun t ht => ccode_lt (hinw t (by omega)))
      have he := ccode_inj (hinw i (by omega)) (hinw j (by omega)) hq
      exfalso
      apply hR.no_repeat i j hij (by omega)
      have si := hR.st_lt hsrc i (by omega)
      have sj := hR.st_lt hsrc j (by omega)
      unfold URTM.Three.toC2 at he
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

/-- 右の上界（窓 [a − ML, b] の自動機械の大きさで決まる）。 -/
def mrI (ML : Nat) (a b : Int) : Nat := 2 ^ cardI ((b - a + ML + 1).toNat)

/-- **有界停止**（右がカウンタのセル、左が段階 1 の証明書。右の上界は `mrI`）。 -/
theorem halts_iff_boundI {tbl : List Quint} (hsrc : Src3 tbl) (hcl : QClosed tbl 2) (hdir : DirConsistent tbl)
    {e r1 r2 o f' : Nat} {A Cc : Nat → Nat} (H : Cell tbl e r1 r2 o f' A Cc)
    {CL : List (List Nat)} {ML : Nat} (hLc : closedR (mirTbl tbl) CL ML = true)
    (c : QConf) (a b : Int) (ha : a ≤ c.pos) (hb : c.pos ≤ b)
    (hz : ∀ x, (x < a ∨ b < x) → c.tape x = 0) (h2 : ∀ x, c.tape x < 2) :
    QHalts tbl c ↔ qrun tbl (bound3 (mrI ML a b) ML a b) c = none := by
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
    have hr := right_boundI H hR hzero (fun t ht => hR.tape_lt hcl h2 t ht) hb (fun x hx => hz x (Or.inr hx))
    have hW : wW (a - ML) b = (b - a + ML + 1).toNat := by unfold wW; congr 1; omega
    rw [hW] at hr
    exact bound_of_window hsrc hcl hR (mrI ML a b) ML a b hz h2 hl hr
  · intro h; exact ⟨_, h⟩

/-! ### Bool の検査 -/

/-- セルの規則が、要求の状態 e・応答の状態 r1, r2 と、o, f', a(r1), a(r2), c(r1), c(r2) で立つ。 -/
def cellWith (tbl : List Quint) (e r1 r2 o f' a1 a2 c1 c2 : Nat) : Bool :=
  decide (find? tbl e 0 = some ⟨e, 0, 1, Dir.L, o⟩) && decide (find? tbl e 1 = some ⟨e, 1, f', Dir.R, e⟩) &&
  decide (find? tbl r1 f' = some ⟨r1, f', c1, Dir.L, a1⟩) && decide (find? tbl r2 f' = some ⟨r2, f', c2, Dir.L, a2⟩) &&
  tbl.all fun ρ => decide (ρ.d = Dir.R → ρ.q = e)

/-- 要求の状態と応答の状態の割り当て（応答の 2 つは順不同なので小さい方を r1 に）。 -/
def cellRoles : List (Nat × Nat × Nat) := [(0, 1, 2), (1, 0, 2), (2, 0, 1)]

/-- **セルの規則の検査**: 割り当てと値の候補（有限個）のどれかで `cellWith` が立つ。 -/
def cellChk (tbl : List Quint) : Bool :=
  cellRoles.any fun r => [r.2.1, r.2.2].any fun o => [0, 1].any fun f' => [r.2.1, r.2.2].any fun a1 =>
    [r.2.1, r.2.2].any fun a2 => [0, 1].any fun c1 => [0, 1].any fun c2 =>
      cellWith tbl r.1 r.2.1 r.2.2 o f' a1 a2 c1 c2

theorem cellWith_spec {tbl : List Quint} {e r1 r2 o f' a1 a2 c1 c2 : Nat}
    (h : cellWith tbl e r1 r2 o f' a1 a2 c1 c2 = true) (hr : r1 ≠ r2) (hr1 : r1 < 3) (hr2 : r2 < 3)
    (ho : o = r1 ∨ o = r2) (ha1 : a1 = r1 ∨ a1 = r2) (ha2 : a2 = r1 ∨ a2 = r2) (hc1 : c1 < 2) (hc2 : c2 < 2) :
    Cell tbl e r1 r2 o f' (fun q => if q = r1 then a1 else a2) (fun q => if q = r1 then c1 else c2) := by
  unfold cellWith at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨h00, h01⟩, hq1⟩, hq2⟩, hent⟩ := h
  have hne : r2 ≠ r1 := fun h => hr h.symm
  exact {
    h00 := h00
    h01 := h01
    hq1 := by simp only; exact hq1
    hq2 := by simp only [if_neg hne]; exact hq2
    ho := ho
    ha1 := by simp only; exact ha1
    ha2 := by simp only [if_neg hne]; exact ha2
    ha3 := fun q => by
      split_ifs
      · rcases ha1 with h | h <;> omega
      · rcases ha2 with h | h <;> omega
    hc1 := by simp only; exact hc1
    hc2 := by simp only [if_neg hne]; exact hc2
    hr1 := hr1
    hr2 := hr2
    hent := fun ρ hρ hd => hent ρ hρ hd }

theorem cellChk_spec {tbl : List Quint} (h : cellChk tbl = true) :
    ∃ e r1 r2 o f' a c, Cell tbl e r1 r2 o f' a c := by
  unfold cellChk at h
  simp only [List.any_eq_true] at h
  obtain ⟨⟨e, r1, r2⟩, hR, o, ho, f', -, a1, ha1, a2, ha2, c1, hc1, c2, hc2, hw⟩ := h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho ha1 ha2 hc1 hc2
  have hroles : r1 ≠ r2 ∧ r1 < 3 ∧ r2 < 3 := by
    simp only [cellRoles, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hR
    rcases hR with ⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩ <;> decide
  exact ⟨_, _, _, _, _, _, _, cellWith_spec hw hroles.1 hroles.2.1 hroles.2.2 ho ha1 ha2
    (by omega) (by omega)⟩

/-- 右にカウンタのセル、左に段階 1 の証明書が立つ。 -/
def sideI (tbl : List Quint) : Bool := cellChk tbl && checkR (mirTbl tbl)

/-- **群 D のカウンタのセルの 12 類の検査**: 表か、その鏡像が `sideI`。 -/
def grpI (es : List Nat) (D : List Dir) : Bool :=
  sideI (URTM.Three.realize es D) || sideI (mirTbl (URTM.Three.realize es D))

/-- 段階 2e の 5 の例外: `isExcH` の表のうち、この 12 類に当たらない表。 -/
def isExcI (es : List Nat) (D : List Dir) : Bool := isExcH es D && !grpI es D

theorem sideI_bound {tbl : List Quint} (hsrc : Src3 tbl) (hcl : QClosed tbl 2) (hdir : DirConsistent tbl)
    (h : sideI tbl = true) :
    ∃ ML : Nat, ∀ (c : QConf) (a b : Int), a ≤ c.pos → c.pos ≤ b →
      (∀ x, (x < a ∨ b < x) → c.tape x = 0) → (∀ x, c.tape x < 2) →
      (QHalts tbl c ↔ qrun tbl (bound3 (mrI ML a b) ML a b) c = none) := by
  unfold sideI at h
  obtain ⟨hc, hL⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨CL, ML, hLc⟩ := checkR_spec hL
  obtain ⟨e, r1, r2, o, f', A, Cc, H⟩ := cellChk_spec hc
  exact ⟨ML, fun c a b ha hb hz h2 => halts_iff_boundI hsrc hcl hdir H hLc c a b ha hb hz h2⟩

theorem sideI_mir_bound {tbl : List Quint} (hsrc : Src3 tbl) (hcl : QClosed tbl 2) (hdir : DirConsistent tbl)
    (h : sideI (mirTbl tbl) = true) :
    ∃ ML : Nat, ∀ (c : QConf) (a b : Int), a ≤ c.pos → c.pos ≤ b →
      (∀ x, (x < a ∨ b < x) → c.tape x = 0) → (∀ x, c.tape x < 2) →
      (QHalts tbl c ↔ qrun tbl (bound3 (mrI ML a b) ML a b) c = none) := by
  rw [mirTbl_eq] at h
  obtain ⟨ML, hb⟩ := sideI_bound (src3_mir hsrc) (closed_mir hcl) (dirConsistent_mir hdir) h
  refine ⟨ML, fun c a b ha hb' hz h2 => ?_⟩
  have := hb (mirQ c) (-b) (-a) (by show -b ≤ -c.pos; omega) (by show -c.pos ≤ -a; omega)
    (fun x hx => by show c.tape (-x) = 0; exact hz (-x) (by omega)) (fun x => h2 (-x))
  rw [QHalts_mir, qrun_mir] at this
  have e1 : mrI ML (-b) (-a) = mrI ML a b := by
    unfold mrI; rw [show -a - -b + (ML : Int) + 1 = b - a + ML + 1 by omega]
  have e : bound3 (mrI ML a b) ML (-b) (-a) = bound3 (mrI ML a b) ML a b := by
    unfold bound3
    rw [show -a + ((mrI ML a b : Nat) : Int) - (-b - ML) + 1 = b + (mrI ML a b : Nat) - (a - ML) + 1 by omega]
  rw [e1, e] at this
  rw [this]
  cases qrun tbl (bound3 (mrI ML a b) ML a b) c <;> simp

/-- 窓の幅で書いた上界。 -/
def bndI (ML w : Nat) : Nat := bnd3N (2 ^ cardI (w + ML + 1)) ML w

theorem cardI_primrec : Primrec cardI := by
  have h2W : Primrec fun W : Nat => 2 ^ W + 2 :=
    Primrec.nat_add.comp (pow_primrec.comp (Primrec.const 2) Primrec.id) (Primrec.const 2)
  exact (Primrec.nat_mul.comp h2W (pow_primrec.comp (pow_primrec.comp h2W h2W) (Primrec.const 3))).of_eq
    fun W => rfl

theorem bndI_primrec (ML : Nat) : Primrec (bndI ML) := by
  have hMR : Primrec fun w : Nat => 2 ^ cardI (w + ML + 1) :=
    pow_primrec.comp (Primrec.const 2) (cardI_primrec.comp
      (Primrec.nat_add.comp (Primrec.nat_add.comp Primrec.id (Primrec.const ML)) (Primrec.const 1)))
  exact (Primrec.nat_add.comp (csize_primrec.comp (Primrec.const 2)
    (Primrec.nat_add.comp (Primrec.nat_add.comp (Primrec.nat_add.comp Primrec.id hMR)
      (Primrec.const ML)) (Primrec.const 1))) (Primrec.const 1)).of_eq fun w => rfl

theorem boundI_eq (ML m n : Nat) :
    bound3 (mrI ML (-(m : Int)) (n : Int)) ML (-(m : Int)) (n : Int) = bndI ML (m + n) := by
  unfold bndI
  rw [← bound3_eq]
  congr 1
  unfold mrI
  rw [show ((n : Int) - -(m : Int) + ML + 1).toNat = m + n + ML + 1 by omega]

section
variable {tbl : List Quint} {q₀ q₁ q₂ sg : Nat}

/-- **12 類の有界停止**（任意の表の正規形）。 -/
theorem okI_bound (H : RTM32 tbl q₀ q₁ q₂ sg)
    (hok : grpI (absCodes q₀ q₁ q₂ sg tbl) (absDirs q₀ q₁ q₂ tbl) = true) :
    ∃ ML : Nat, ∀ (c : QConf) (m n : ℕ), -(m : ℤ) ≤ c.pos → c.pos ≤ (n : ℤ) →
      (∀ x, (x < -(m : ℤ) ∨ (n : ℤ) < x) → c.tape x = 0) → (∀ x, c.tape x < 2) →
      (QHalts (normT (tbl := tbl) (q₀ := q₀) (q₁ := q₁) (q₂ := q₂) (σ := sg)) c ↔
        qrun (normT (tbl := tbl) (q₀ := q₀) (q₁ := q₁) (q₂ := q₂) (σ := sg)) (bndI ML (m + n)) c
          = none) := by
  have hsrc := realize_src3 (absCodes q₀ q₁ q₂ sg tbl) (absDirs q₀ q₁ q₂ tbl)
  have hcl := realize_closed (absCodes q₀ q₁ q₂ sg tbl) (absDirs q₀ q₁ q₂ tbl)
  have hdir := realize_dir (absCodes q₀ q₁ q₂ sg tbl) (absDirs q₀ q₁ q₂ tbl)
  unfold grpI at hok
  obtain ⟨ML, hb⟩ : ∃ ML : Nat, ∀ (c : QConf) (a b : Int), a ≤ c.pos → c.pos ≤ b →
      (∀ x, (x < a ∨ b < x) → c.tape x = 0) → (∀ x, c.tape x < 2) →
      (QHalts (URTM.Three.realize (absCodes q₀ q₁ q₂ sg tbl) (absDirs q₀ q₁ q₂ tbl)) c ↔
        qrun (URTM.Three.realize (absCodes q₀ q₁ q₂ sg tbl) (absDirs q₀ q₁ q₂ tbl))
          (bound3 (mrI ML a b) ML a b) c = none) := by
    rcases Bool.or_eq_true_iff.mp hok with h | h
    · exact sideI_bound hsrc hcl hdir h
    · exact sideI_mir_bound hsrc hcl hdir h
  refine ⟨ML, fun c m n ha hb' hz h2 => ?_⟩
  rw [← boundI_eq]
  exact hb c _ _ ha hb' hz h2

/-- **3 状態 2 記号の RTM の停止問題は、U の ID の上で計算可能**（`isExcI` の表を除く）。 -/
theorem three_halting_computable_I (H : RTM32 tbl q₀ q₁ q₂ sg)
    (hne : isExcI (absCodes q₀ q₁ q₂ sg tbl) (absDirs q₀ q₁ q₂ tbl) = false) :
    ∃ f : ZID → Bool, Computable f ∧
      ∀ z, (∀ a ∈ z.2.1 ++ z.2.2, a = 0 ∨ a ∈ [sg]) → (ZHalts tbl z ↔ f z = true) := by
  cases hH : isExcH (absCodes q₀ q₁ q₂ sg tbl) (absDirs q₀ q₁ q₂ tbl) with
  | false => exact three_halting_computable_H H hH
  | true =>
    have hI : grpI (absCodes q₀ q₁ q₂ sg tbl) (absDirs q₀ q₁ q₂ tbl) = true := by
      unfold isExcI at hne; rw [hH] at hne; simpa using hne
    obtain ⟨ML, hb⟩ := okI_bound H hI
    exact halting_computable_of_bound H (bndI_primrec ML) hb

/-- **定理（段階 2e の 5）: `isExcI` の表を除き、3 状態 2 記号の URTM は存在しない**（Morita Def. 7.1、
    U の記号集合 {0, sg} の上の ID への符号化）。 -/
theorem no_three_two_URTM_I (H : RTM32 tbl q₀ q₁ q₂ sg)
    (hne : isExcI (absCodes q₀ q₁ q₂ sg tbl) (absDirs q₀ q₁ q₂ tbl) = false) :
    ¬ IsUTM_MoritaOver tbl [sg] :=
  not_UTM_of_halting_computable (three_halting_computable_I H hne)

end

/-! ### 残る例外の数

段階 2e の 4 の例外の上界 336 表（`excHKeys`）のうち、`grpI` に当たる 144 表（12 類）の鍵を一覧 `i144Keys` に書き、
それらが `grpI` に当たることを kernel で確かめる。残る例外はその外の 192 表に**含まれる**（上界）。 -/

/-- `grpI` に当たる 144 表の鍵（Python で生成。下の `i144_grpI` が kernel で検査する）。 -/
def i144Keys : List Nat := [
  243396, 243443, 243445, 243492, 245748, 245846, 276371, 276373, 276420, 278774, 281222, 283574,
  287160, 287501, 287503, 287844, 289853, 289855, 290196, 303624, 304310, 306662, 323810, 340274,
  709455, 709456, 709648, 709651, 712048, 712052, 724209, 724216, 724384, 724405, 731409, 731416,
  731605, 741184, 741212, 748412, 776655, 776656, 776851, 779252, 786260, 788660, 798644, 815444,
  1030123, 1030124, 1032139, 1032140, 1032238, 1032286, 1034924, 1034925, 1034972, 1034974, 1036941, 1036990,
  1047205, 1047212, 1047445, 1047452, 1048138, 1048474, 1052000, 1052007, 1052247, 1052336, 1052350, 1052590,
  2206613, 2206614, 2208629, 2208630, 2208728, 2208776, 2211414, 2211415, 2211462, 2211464, 2213431, 2213480,
  2223695, 2223702, 2223935, 2223942, 2224628, 2224964, 2228490, 2228497, 2228737, 2228826, 2228840, 2229080,
  2356541, 2356542, 2356734, 2356737, 2359134, 2359138, 2371295, 2371302, 2371470, 2371491, 2378495, 2378502,
  2378691, 2388270, 2388298, 2395498, 2423741, 2423742, 2423937, 2426338, 2433346, 2435746, 2445730, 2462530,
  2831674, 2831721, 2831723, 2831770, 2834026, 2834124, 2864649, 2864651, 2864698, 2867052, 2869500, 2871852,
  2875438, 2875779, 2875781, 2876122, 2878131, 2878133, 2878474, 2891902, 2892588, 2894940, 2912088, 2928552
]

theorem i144_grpI : i144Keys.all (fun k => grpI (unkey k).1 (unkey k).2) = true := by decide +kernel

theorem i144_sub : i144Keys.all (fun k => excHKeys.contains k) = true := by decide +kernel

/-- 段階 2e の 5 の例外の鍵（の上界）。 -/
def excIKeys : List Nat := excHKeys.filter fun k => !i144Keys.contains k

/-- **段階 2e の 5 の例外の表（の上界）の一覧**。 -/
def excITables : List (List Nat × List Dir) := excIKeys.map unkey

/-- **主定理の仮定が外れる表は一覧に載る**（符号 6 つ・向き 3 つの表について）。 -/
theorem mem_excITables {es : List Nat} {D : List Dir} (h : ValidKey es D) (hx : isExcI es D = true) :
    (es, D) ∈ excITables := by
  unfold isExcI at hx
  obtain ⟨hH, hI⟩ := Bool.and_eq_true_iff.mp hx
  obtain ⟨k, hk, he⟩ := List.mem_map.mp (mem_excHTables h hH)
  refine List.mem_map.mpr ⟨k, List.mem_filter.mpr ⟨hk, ?_⟩, he⟩
  cases hc : i144Keys.contains k
  · rfl
  · exfalso
    have := List.all_eq_true.mp i144_grpI k (List.contains_iff_mem.mp hc)
    rw [he] at this
    simp only [this, Bool.not_true] at hI
    exact Bool.false_ne_true hI

/-- **段階 2e の 5 の例外は高々 192 表**（336 − 144。kernel の評価）。 -/
theorem excIKeys_length : excIKeys.length = 192 := by decide +kernel

theorem excITables_length : excITables.length = 192 := by
  unfold excITables; rw [List.length_map, excIKeys_length]

end URTM.Meta
