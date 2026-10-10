/-
  3 状態 2 記号 RTM の停止問題の決定可能性 その 7: **全列挙の健全性と、正規形の表の有界停止**。**手書き**。

    * `lvl0_sound` : `lvl0 f = true` なら、符号の並びが重ならないどの正規形の表 (es, D) でも `f es D = true`
    * `tableOK_bound` : `tableOK es D = true` なら、正規形の表 `realize es D` は、窓の外が空白で記号が 0, 1 の
      配置から止まるとき `bound3 MR ML a b` 歩以内に止まる（MR, ML は表ごとの定数）
-/
import URTM.ThreeDecide

namespace URTM.Three
open URTM URTM.TwoState

/-! ### 全列挙の健全性 -/

theorem or_not_true {b x : Bool} (h : (!b || x) = true) (hb : b = true) : x = true := by
  cases b <;> simp_all

theorem mem_dirList (d : Dir) : d ∈ dirList := by cases d <;> simp [dirList]

theorem lvl0_sound {f : List Nat → List Dir → Bool} (h : lvl0 f = true)
    {c0 c1 c2 c3 c4 c5 : Nat} (h0 : c0 < 7) (h1 : c1 < 7) (h2 : c2 < 7) (h3 : c3 < 7)
    (h4 : c4 < 7) (h5 : c5 < 7)
    (f1 : fresh [c0] c1 = true) (f2 : fresh [c0, c1] c2 = true) (f3 : fresh [c0, c1, c2] c3 = true)
    (f4 : fresh [c0, c1, c2, c3] c4 = true) (f5 : fresh [c0, c1, c2, c3, c4] c5 = true)
    (d0 d1 d2 : Dir) : f [c0, c1, c2, c3, c4, c5] [d0, d1, d2] = true := by
  have e1 : lvl1 c0 f = true := List.all_eq_true.mp h c0 (List.mem_range.mpr h0)
  have e2 : lvl2 c0 c1 f = true := or_not_true (List.all_eq_true.mp e1 c1 (List.mem_range.mpr h1)) f1
  have e3 : lvl3 c0 c1 c2 f = true := or_not_true (List.all_eq_true.mp e2 c2 (List.mem_range.mpr h2)) f2
  have e4 : lvl4 c0 c1 c2 c3 f = true :=
    or_not_true (List.all_eq_true.mp e3 c3 (List.mem_range.mpr h3)) f3
  have e5 := or_not_true (List.all_eq_true.mp e4 c4 (List.mem_range.mpr h4)) f4
  have e6 : allD [c0, c1, c2, c3, c4, c5] f = true :=
    or_not_true (List.all_eq_true.mp e5 c5 (List.mem_range.mpr h5)) f5
  unfold allD at e6
  exact List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp e6 d0 (mem_dirList d0))
    d1 (mem_dirList d1)) d2 (mem_dirList d2)

/-! ### 正規形の表の性質 -/

theorem mem_quintOf {D : List Dir} {i s c : Nat} {r : Quint} (h : r ∈ quintOf D i s c) :
    r.p = i ∧ r.s = s ∧ r.t < 2 ∧ c ≠ 0 ∧ r.q = (c - 1) / 2 ∧ r.d = D.getD r.q Dir.L := by
  unfold quintOf at h
  split at h
  · simp at h
  · rename_i hc
    simp only [List.mem_singleton] at h
    subst h
    exact ⟨rfl, rfl, Nat.mod_lt _ (by decide), hc, rfl, rfl⟩

theorem mem_realize {es : List Nat} {D : List Dir} {r : Quint} (h : r ∈ realize es D) :
    r.p < 3 ∧ r.t < 2 ∧ r.d = D.getD r.q Dir.L := by
  unfold realize at h
  simp only [List.mem_append] at h
  rcases h with ((((h | h) | h) | h) | h) | h <;>
    · obtain ⟨hp, _, ht, _, _, hd⟩ := mem_quintOf h; exact ⟨by omega, ht, hd⟩

theorem realize_dir (es : List Nat) (D : List Dir) : DirConsistent (realize es D) := by
  intro r hr r' hr' hq
  rw [(mem_realize hr).2.2, (mem_realize hr').2.2, hq]

theorem realize_src3 (es : List Nat) (D : List Dir) : Src3 (realize es D) :=
  fun _ hr => (mem_realize hr).1

theorem realize_closed (es : List Nat) (D : List Dir) : QClosed (realize es D) 2 :=
  fun _ hr _ => (mem_realize hr).2.1

/-- 正規形の表の表引き。 -/
theorem find?_realize (c0 c1 c2 c3 c4 c5 : Nat) (D : List Dir) (p s : Nat) (hp : p < 3) (hs : s < 2) :
    ∃ c, c = [c0, c1, c2, c3, c4, c5].getD (2 * p + s) 0 ∧
      find? (realize [c0, c1, c2, c3, c4, c5] D) p s =
        if c = 0 then none else some ⟨p, s, (c - 1) % 2, D.getD ((c - 1) / 2) Dir.L, (c - 1) / 2⟩ := by
  refine ⟨_, rfl, ?_⟩
  have : (p = 0 ∨ p = 1 ∨ p = 2) := by omega
  have : (s = 0 ∨ s = 1) := by omega
  rcases ‹p = 0 ∨ p = 1 ∨ p = 2› with rfl | rfl | rfl <;> rcases ‹s = 0 ∨ s = 1› with rfl | rfl <;>
    · simp only [realize, find?, List.find?_append, quintOf, List.getD_cons_zero, List.getD_cons_succ]
      by_cases e0 : c0 = 0 <;> by_cases e1 : c1 = 0 <;> by_cases e2 : c2 = 0 <;>
        by_cases e3 : c3 = 0 <;> by_cases e4 : c4 = 0 <;> by_cases e5 : c5 = 0 <;>
        simp [e0, e1, e2, e3, e4, e5, List.find?]

theorem total_of_noHalt {c0 c1 c2 c3 c4 c5 : Nat} (D : List Dir)
    (hc : ∀ c ∈ [c0, c1, c2, c3, c4, c5], c < 7) (h : noHalt [c0, c1, c2, c3, c4, c5] = true) :
    Total3 (realize [c0, c1, c2, c3, c4, c5] D) := by
  intro p s hp hs
  obtain ⟨c, hcdef, hf⟩ := find?_realize c0 c1 c2 c3 c4 c5 D p s hp hs
  have hmem : c ∈ [c0, c1, c2, c3, c4, c5] := by
    rw [hcdef]
    have : 2 * p + s < 6 := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using this)]
    exact List.getElem_mem _
  have hc0 : c ≠ 0 := by
    unfold noHalt at h
    have := List.all_eq_true.mp h c hmem
    simpa using this
  have hc7 := hc c hmem
  rw [if_neg hc0] at hf
  exact ⟨_, hf, by show (c - 1) / 2 < 3; omega⟩

theorem checkR_spec {tbl : List Quint} (h : checkR tbl = true) : ∃ C M, closedR tbl C M = true := by
  unfold checkR at h
  cases hc : closure tbl with
  | none => rw [hc] at h; simp at h
  | some CM => rw [hc] at h; exact ⟨CM.1, CM.2, h⟩

/-- **証明書の立つ正規形の表は有界停止**。 -/
theorem tableOK_bound {c0 c1 c2 c3 c4 c5 : Nat} (D : List Dir)
    (hc : ∀ c ∈ [c0, c1, c2, c3, c4, c5], c < 7) (h : tableOK [c0, c1, c2, c3, c4, c5] D = true) :
    ∃ MR ML : Nat, ∀ (c : QConf) (a b : Int), a ≤ c.pos → c.pos ≤ b →
      (∀ x, (x < a ∨ b < x) → c.tape x = 0) → (∀ x, c.tape x < 2) →
      (QHalts (realize [c0, c1, c2, c3, c4, c5] D) c ↔
        qrun (realize [c0, c1, c2, c3, c4, c5] D) (bound3 MR ML a b) c = none) := by
  unfold tableOK at h
  rcases Bool.or_eq_true_iff.mp h with hn | hk
  · refine ⟨0, 0, fun c a b _ _ _ h2 => ?_⟩
    exact halts_iff_total (realize_src3 _ _) (total_of_noHalt D hc hn) (realize_closed _ _) c h2 _
      (by unfold bound3; omega)
  · unfold check3 at hk
    obtain ⟨hR, hL⟩ := Bool.and_eq_true_iff.mp hk
    obtain ⟨CR, MR, hRc⟩ := checkR_spec hR
    obtain ⟨CL, ML, hLc⟩ := checkR_spec hL
    exact ⟨MR, ML, fun c a b ha hb hz h2 =>
      halts_iff_bound3 (realize_src3 _ _) (realize_closed _ _) (realize_dir _ _) hRc hLc c a b ha hb hz h2⟩

end URTM.Three
