/-
  3 状態 2 記号の URTM（段階 2b）その 4: **群 C（0 シフトで入られる状態がある表）**。**手書き**。

  状態 z へ入る規則がどれも 0 シフト（動かない）とする。z に入った直後は、いま書いた記号を同じマスで読むので、
  次の 1 歩は入る規則だけで決まる。そこで「z へ入る規則」と「z の中で続く規則」を 1 本にまとめ、z を消した表を作る
  （`elim`。符号で書くと、z へ入る符号を、z の中で規則をたどった先の符号で置き換えるだけ。高々 2 回たどる）。
  まとめた表は z へ入る規則を持たない（群 A の形）ので、`halts_noEntry` から有界停止が出る。
  元の表の実行は、まとめた表の 1 歩を 1〜3 歩で模倣する（`macro_step`）。

  検査 `okC es D z`（Bool）: z へ入る向きが 0 シフト、まとめた表の符号が重ならない（可逆）、z へ入る符号が残らない。
  主定理 `no_three_two_URTM_C`: `isExcC es D = isExc es D && !grpB es D && !grpC es D`。
-/
import URTMMeta.ThreeB

namespace URTM.Meta
open URTM URTM.TwoState URTM.Three

/-! ### 正規形の表の 1 歩（符号で書く） -/

/-- 符号 c の入る先の状態。 -/
def ctgt (c : Nat) : Nat := (c - 1) / 2

/-- 符号 c の書く記号。 -/
def cwr (c : Nat) : Nat := (c - 1) % 2

/-- 符号 c（≠ 0）の規則を配置 x に適用した結果。 -/
def capply (D : List Dir) (c : Nat) (x : QConf) : QConf :=
  ⟨ctgt c, move (D.getD (ctgt c) Dir.L) x.pos, write x.tape x.pos (cwr c)⟩

/-- 配置 x が読む欄の符号。 -/
def slot (es : List Nat) (x : QConf) : Nat := es.getD (2 * x.st + x.tape x.pos) 0

/-- 正規形の表の 1 歩。 -/
theorem qstep_realize6 (c0 c1 c2 c3 c4 c5 : Nat) (D : List Dir) (x : QConf) (hp : x.st < 3)
    (hs : x.tape x.pos < 2) :
    qstep (URTM.Three.realize [c0, c1, c2, c3, c4, c5] D) x =
      if slot [c0, c1, c2, c3, c4, c5] x = 0 then none
      else some (capply D (slot [c0, c1, c2, c3, c4, c5] x) x) := by
  obtain ⟨c, hc, hf⟩ := find?_realize c0 c1 c2 c3 c4 c5 D x.st (x.tape x.pos) hp hs
  unfold qstep slot
  rw [hf, ← hc]
  by_cases h0 : c = 0
  · simp [h0]
  · simp [h0, capply, ctgt, cwr]

/-! ### 状態 z を消す -/

/-- 状態 z の中で規則をたどった先の符号（z に留まるかぎり高々 2 回）。 -/
def resolve (es : List Nat) (z c : Nat) : Nat :=
  if c = 0 ∨ ctgt c ≠ z then c
  else if es.getD (2 * z + cwr c) 0 = 0 ∨ ctgt (es.getD (2 * z + cwr c) 0) ≠ z then
    es.getD (2 * z + cwr c) 0
  else es.getD (2 * z + cwr (es.getD (2 * z + cwr c) 0)) 0

/-- z を消した表の欄 i の符号: z の欄は空、ほかの欄は z の中の規則をたどった先。 -/
def elimAt (es : List Nat) (z i : Nat) : Nat := if i / 2 = z then 0 else resolve es z (es.getD i 0)

/-- z を消した表の符号。 -/
def elim (es : List Nat) (z : Nat) : List Nat :=
  [elimAt es z 0, elimAt es z 1, elimAt es z 2, elimAt es z 3, elimAt es z 4, elimAt es z 5]

/-- **群 C の検査**: z へ入る向きは 0 シフト、z を消した表は符号が重ならず（可逆）、z へ入る符号が残らない。 -/
def okC (es : List Nat) (D : List Dir) (z : Nat) : Bool :=
  D.getD z Dir.L == Dir.Z && injCodes (elim es z) &&
    (elim es z).all fun c => c == 0 || ctgt c != z

theorem injCodes_spec {es : List Nat} (h : injCodes es = true) : InjCodes es := by
  intro i j hi hj hne heq
  unfold injCodes at h
  have := List.all_eq_true.mp (List.all_eq_true.mp h i (List.mem_range.mpr hi)) j (List.mem_range.mpr hj)
  simp only [Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at this
  rcases this with (h1 | h1) | h1
  · exact h1
  · exact absurd h1 hne
  · exact absurd heq h1

theorem okC_spec {es : List Nat} {D : List Dir} {z : Nat} (h : okC es D z = true) :
    D.getD z Dir.L = Dir.Z ∧ InjCodes (elim es z) ∧ ∀ c ∈ elim es z, c = 0 ∨ ctgt c ≠ z := by
  unfold okC at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq] at h
  exact ⟨h.1.1, injCodes_spec h.1.2, h.2⟩

/-! ### 補助 -/

theorem write_write (t : Int → Nat) (p : Int) (v w : Nat) : write (write t p v) p w = write t p w := by
  funext x; unfold write; split <;> rfl

theorem write_at (t : Int → Nat) (p : Int) (v : Nat) : write t p v p = v := by
  unfold write; simp

theorem ctgt_lt {c : Nat} (h : c < 7) : ctgt c < 3 := by unfold ctgt; omega

theorem getD_lt7 {es : List Nat} (hlt : ∀ c ∈ es, c < 7) (i : Nat) : es.getD i 0 < 7 := by
  rw [List.getD_eq_getElem?_getD]
  cases h : es[i]? with
  | none => simp
  | some a => simpa using hlt a (List.mem_of_getElem? h)

theorem elim_getD (es : List Nat) (z : Nat) {i : Nat} (hi : i < 6) :
    (elim es z).getD i 0 = elimAt es z i := by
  unfold elim
  match i, hi with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | _ + 6, h => omega

theorem elimAt_mem (es : List Nat) (z : Nat) {i : Nat} (hi : i < 6) : elimAt es z i ∈ elim es z := by
  unfold elim
  match i, hi with
  | 0, _ => simp
  | 1, _ => simp
  | 2, _ => simp
  | 3, _ => simp
  | 4, _ => simp
  | 5, _ => simp
  | _ + 6, h => omega

theorem resolve_stay {es : List Nat} {z c : Nat} (h : c = 0 ∨ ctgt c ≠ z) : resolve es z c = c := by
  unfold resolve; rw [if_pos h]

theorem resolve_hop1 {es : List Nat} {z c : Nat} (h : ¬ (c = 0 ∨ ctgt c ≠ z))
    (h1 : es.getD (2 * z + cwr c) 0 = 0 ∨ ctgt (es.getD (2 * z + cwr c) 0) ≠ z) :
    resolve es z c = es.getD (2 * z + cwr c) 0 := by
  unfold resolve; rw [if_neg h, if_pos h1]

theorem resolve_hop2 {es : List Nat} {z c : Nat} (h : ¬ (c = 0 ∨ ctgt c ≠ z))
    (h1 : ¬ (es.getD (2 * z + cwr c) 0 = 0 ∨ ctgt (es.getD (2 * z + cwr c) 0) ≠ z)) :
    resolve es z c = es.getD (2 * z + cwr (es.getD (2 * z + cwr c) 0)) 0 := by
  unfold resolve; rw [if_neg h, if_neg h1]

theorem resolve_lt7 {es : List Nat} (hlt : ∀ c ∈ es, c < 7) (z : Nat) {c : Nat} (hc : c < 7) :
    resolve es z c < 7 := by
  unfold resolve
  split
  · exact hc
  · split
    · exact getD_lt7 hlt _
    · exact getD_lt7 hlt _

theorem elim_lt7 {es : List Nat} (hlt : ∀ c ∈ es, c < 7) (z : Nat) : ∀ c ∈ elim es z, c < 7 := by
  intro c hc
  have key : ∀ i, elimAt es z i < 7 := by
    intro i; unfold elimAt; split
    · omega
    · exact resolve_lt7 hlt z (getD_lt7 hlt i)
  unfold elim at hc
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> exact key _

/-- z へ 0 シフトで入る符号の 1 歩は、その場に留まって記号を書くだけ。 -/
theorem capply_z {D : List Dir} {z c : Nat} (hD : D.getD z Dir.L = Dir.Z) (hc : ctgt c = z) (x : QConf) :
    capply D c x = ⟨z, x.pos, write x.tape x.pos (cwr c)⟩ := by
  unfold capply; rw [hc, hD]; rfl

/-- 同じマスに書き直すだけなので、z を経由しても、直接その符号を適用したのと同じ配置になる。 -/
theorem capply_hop (D : List Dir) (c' z : Nat) (x : QConf) (v : Nat) :
    capply D c' ⟨z, x.pos, write x.tape x.pos v⟩ = capply D c' x := by
  unfold capply; simp only [write_write]

theorem capply_tape_lt (D : List Dir) (c : Nat) {x : QConf} (h2 : ∀ y, x.tape y < 2) :
    ∀ y, (capply D c x).tape y < 2 := by
  intro y
  show write x.tape x.pos (cwr c) y < 2
  unfold write; split
  · unfold cwr; omega
  · exact h2 y

section
variable {c0 c1 c2 c3 c4 c5 : Nat} {D : List Dir} {z : Nat}

/-- **まとめた表の 1 歩は、元の表の 1〜3 歩**（z 以外の働く状態から）。まとめた表が止まるなら、元の表は
    3 歩以内に止まる。 -/
theorem macro_step (hlt : ∀ c ∈ [c0, c1, c2, c3, c4, c5], c < 7) (hz : z < 3)
    (hok : okC [c0, c1, c2, c3, c4, c5] D z = true) (x : QConf) (hst : x.st < 3) (hne : x.st ≠ z)
    (h2 : ∀ y, x.tape y < 2) :
    (qstep (URTM.Three.realize (elim [c0, c1, c2, c3, c4, c5] z) D) x = none ∧
      qrun (URTM.Three.realize [c0, c1, c2, c3, c4, c5] D) 3 x = none) ∨
    (∃ x' j, qstep (URTM.Three.realize (elim [c0, c1, c2, c3, c4, c5] z) D) x = some x' ∧ 1 ≤ j ∧ j ≤ 3 ∧
      qrun (URTM.Three.realize [c0, c1, c2, c3, c4, c5] D) j x = some x' ∧
      x'.st < 3 ∧ x'.st ≠ z ∧ ∀ y, x'.tape y < 2) := by
  obtain ⟨hD, _, hall⟩ := okC_spec hok
  have hs := h2 x.pos
  have hT := fun (y : QConf) (h1 : y.st < 3) (h2 : y.tape y.pos < 2) =>
    qstep_realize6 c0 c1 c2 c3 c4 c5 D y h1 h2
  have hT' : qstep (URTM.Three.realize (elim [c0, c1, c2, c3, c4, c5] z) D) x =
      if slot (elim [c0, c1, c2, c3, c4, c5] z) x = 0 then none
      else some (capply D (slot (elim [c0, c1, c2, c3, c4, c5] z) x) x) :=
    qstep_realize6 _ _ _ _ _ _ D x hst hs
  have hi6 : 2 * x.st + x.tape x.pos < 6 := by omega
  have hslot : slot (elim [c0, c1, c2, c3, c4, c5] z) x =
      resolve [c0, c1, c2, c3, c4, c5] z (slot [c0, c1, c2, c3, c4, c5] x) := by
    unfold slot
    rw [elim_getD _ _ hi6]
    unfold elimAt
    rw [if_neg (by omega)]
  have hres : resolve [c0, c1, c2, c3, c4, c5] z (slot [c0, c1, c2, c3, c4, c5] x) = 0 ∨
      ctgt (resolve [c0, c1, c2, c3, c4, c5] z (slot [c0, c1, c2, c3, c4, c5] x)) ≠ z := by
    have := hall _ (elimAt_mem [c0, c1, c2, c3, c4, c5] z hi6)
    unfold elimAt at this
    rw [if_neg (by omega)] at this
    exact this
  rw [hslot] at hT'
  have hTx := hT x hst hs
  obtain ⟨c, hc⟩ : ∃ c, c = slot [c0, c1, c2, c3, c4, c5] x := ⟨_, rfl⟩
  rw [← hc] at hT' hTx hres
  have hc7 : c < 7 := by rw [hc]; exact getD_lt7 hlt _
  by_cases h0 : c = 0
  · -- 規則なし: どちらもすぐ止まる
    left
    rw [resolve_stay (Or.inl h0)] at hT'
    exact ⟨by rw [hT', if_pos h0],
      qrun_none_mono _ x 1 3 (qrun_succ_none _ 0 (by rw [hTx, if_pos h0])) (by omega)⟩
  by_cases h1 : ctgt c ≠ z
  · -- z へ入らない: 同じ 1 歩
    right
    rw [resolve_stay (Or.inr h1)] at hT'
    refine ⟨capply D c x, 1, by rw [hT', if_neg h0], by omega, by omega, ?_, ctgt_lt hc7, h1,
      capply_tape_lt D c h2⟩
    rw [qrun_succ_some _ 0 (by rw [hTx, if_neg h0])]; rfl
  -- z へ入る（0 シフト）: 1 歩目
  have h1' : ctgt c = z := Classical.not_not.mp h1
  have hn01 : ¬ (c = 0 ∨ ctgt c ≠ z) := fun h => h.elim h0 h1
  have hy1 : qstep (URTM.Three.realize [c0, c1, c2, c3, c4, c5] D) x =
      some ⟨z, x.pos, write x.tape x.pos (cwr c)⟩ := by rw [hTx, if_neg h0, capply_z hD h1']
  have hTy1 := hT ⟨z, x.pos, write x.tape x.pos (cwr c)⟩ hz
    (by show write x.tape x.pos (cwr c) x.pos < 2; rw [write_at]; unfold cwr; omega)
  have hs1 : slot [c0, c1, c2, c3, c4, c5] ⟨z, x.pos, write x.tape x.pos (cwr c)⟩ =
      [c0, c1, c2, c3, c4, c5].getD (2 * z + cwr c) 0 := by
    show [c0, c1, c2, c3, c4, c5].getD (2 * z + write x.tape x.pos (cwr c) x.pos) 0 = _
    rw [write_at]
  rw [hs1, capply_hop] at hTy1
  obtain ⟨d, hd⟩ : ∃ d, d = [c0, c1, c2, c3, c4, c5].getD (2 * z + cwr c) 0 := ⟨_, rfl⟩
  have hd7 : d < 7 := by rw [hd]; exact getD_lt7 hlt _
  by_cases h10 : d = 0
  · -- z の中で規則なし: 2 歩目で止まる
    left
    rw [resolve_hop1 hn01 (Or.inl (hd ▸ h10)), ← hd] at hT'
    refine ⟨by rw [hT', if_pos h10], ?_⟩
    have h2n : qrun (URTM.Three.realize [c0, c1, c2, c3, c4, c5] D) 2 x = none := by
      rw [qrun_succ_some _ 1 hy1]
      exact qrun_succ_none _ 0 (by rw [hTy1, ← hd, if_pos h10])
    exact qrun_none_mono _ x 2 3 h2n (by omega)
  by_cases h11 : ctgt d ≠ z
  · -- 2 歩目で z を出る
    right
    rw [resolve_hop1 hn01 (Or.inr (hd ▸ h11)), ← hd] at hT'
    refine ⟨capply D d x, 2, by rw [hT', if_neg h10], by omega, by omega, ?_, ctgt_lt hd7, h11,
      capply_tape_lt D d h2⟩
    rw [qrun_succ_some _ 1 hy1, qrun_succ_some _ 0 (by rw [hTy1, ← hd, if_neg h10])]; rfl
  -- 2 歩目も z に留まる
  have h11' : ctgt d = z := Classical.not_not.mp h11
  have hn11 : ¬ ([c0, c1, c2, c3, c4, c5].getD (2 * z + cwr c) 0 = 0 ∨
      ctgt ([c0, c1, c2, c3, c4, c5].getD (2 * z + cwr c) 0) ≠ z) := by
    rw [← hd]; exact fun h => h.elim h10 h11
  have hy2 : qstep (URTM.Three.realize [c0, c1, c2, c3, c4, c5] D) ⟨z, x.pos, write x.tape x.pos (cwr c)⟩ =
      some ⟨z, x.pos, write x.tape x.pos (cwr d)⟩ := by
    rw [hTy1, ← hd, if_neg h10, capply_z hD h11']
  have hTy2 := hT ⟨z, x.pos, write x.tape x.pos (cwr d)⟩ hz
    (by show write x.tape x.pos (cwr d) x.pos < 2; rw [write_at]; unfold cwr; omega)
  have hs2 : slot [c0, c1, c2, c3, c4, c5] ⟨z, x.pos, write x.tape x.pos (cwr d)⟩ =
      [c0, c1, c2, c3, c4, c5].getD (2 * z + cwr d) 0 := by
    show [c0, c1, c2, c3, c4, c5].getD (2 * z + write x.tape x.pos (cwr d) x.pos) 0 = _
    rw [write_at]
  rw [hs2, capply_hop] at hTy2
  rw [resolve_hop2 hn01 hn11, ← hd] at hT' hres
  obtain ⟨g, hg⟩ : ∃ g, g = [c0, c1, c2, c3, c4, c5].getD (2 * z + cwr d) 0 := ⟨_, rfl⟩
  rw [← hg] at hT' hres hTy2
  have hg7 : g < 7 := by rw [hg]; exact getD_lt7 hlt _
  by_cases h20 : g = 0
  · -- 3 歩目で止まる
    left
    refine ⟨by rw [hT', if_pos h20], ?_⟩
    rw [qrun_succ_some _ 2 hy1, qrun_succ_some _ 1 hy2]
    exact qrun_succ_none _ 0 (by rw [hTy2, if_pos h20])
  · -- 3 歩目で z を出る（検査から、まとめた符号は z へ入らない）
    right
    have h21 : ctgt g ≠ z := hres.resolve_left h20
    refine ⟨capply D g x, 3, by rw [hT', if_neg h20], by omega, by omega, ?_, ctgt_lt hg7, h21,
      capply_tape_lt D g h2⟩
    rw [qrun_succ_some _ 2 hy1, qrun_succ_some _ 1 hy2,
      qrun_succ_some _ 0 (by rw [hTy2, if_neg h20])]; rfl

/-- まとめた表が n 歩で止まるなら、元の表は 3n 歩で止まる。 -/
theorem sim_fwd (hlt : ∀ c ∈ [c0, c1, c2, c3, c4, c5], c < 7) (hz : z < 3)
    (hok : okC [c0, c1, c2, c3, c4, c5] D z = true) :
    ∀ n (x : QConf), x.st < 3 → x.st ≠ z → (∀ y, x.tape y < 2) →
      qrun (URTM.Three.realize (elim [c0, c1, c2, c3, c4, c5] z) D) n x = none →
      qrun (URTM.Three.realize [c0, c1, c2, c3, c4, c5] D) (3 * n) x = none := by
  intro n
  induction n with
  | zero => intro x _ _ _ h; simp [qrun] at h
  | succ n ih =>
    intro x hst hne h2 h
    rcases macro_step hlt hz hok x hst hne h2 with ⟨_, h3⟩ | ⟨x', j, hq, hj1, hj3, hrun, hst', hne', h2'⟩
    · exact qrun_none_mono _ x 3 _ h3 (by omega)
    · rw [qrun_succ_some _ n hq] at h
      have h4 : qrun (URTM.Three.realize [c0, c1, c2, c3, c4, c5] D) (j + 3 * n) x = none := by
        rw [qrun_add, hrun]; exact ih x' hst' hne' h2' h
      exact qrun_none_mono _ x _ _ h4 (by omega)

/-- 元の表が止まるなら、まとめた表も止まる。 -/
theorem sim_bwd (hlt : ∀ c ∈ [c0, c1, c2, c3, c4, c5], c < 7) (hz : z < 3)
    (hok : okC [c0, c1, c2, c3, c4, c5] D z = true) :
    ∀ n (x : QConf), x.st < 3 → x.st ≠ z → (∀ y, x.tape y < 2) →
      qrun (URTM.Three.realize [c0, c1, c2, c3, c4, c5] D) n x = none →
      QHalts (URTM.Three.realize (elim [c0, c1, c2, c3, c4, c5] z) D) x := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro x hst hne h2 h
    rcases macro_step hlt hz hok x hst hne h2 with ⟨h0, _⟩ | ⟨x', j, hq, hj1, hj3, hrun, hst', hne', h2'⟩
    · exact ⟨1, qrun_succ_none _ 0 h0⟩
    · rcases Nat.lt_or_ge n j with hlt' | hge
      · have := qrun_none_mono _ x n j h (by omega)
        rw [hrun] at this; cases this
      · have h4 : qrun (URTM.Three.realize [c0, c1, c2, c3, c4, c5] D) (n - j) x' = none := by
          have h5 : qrun (URTM.Three.realize [c0, c1, c2, c3, c4, c5] D) (j + (n - j)) x = none := by
            rw [show j + (n - j) = n by omega]; exact h
          rw [qrun_add, hrun] at h5; exact h5
        obtain ⟨m, hm⟩ := ih (n - j) (by omega) x' hst' hne' h2' h4
        exact ⟨m + 1, by rw [qrun_succ_some _ m hq]; exact hm⟩

/-- z 以外の状態から始めた停止は、まとめた表（群 A の形）の上界の 3 倍の歩数で決まる。 -/
theorem halts_elim_off (hlt : ∀ c ∈ [c0, c1, c2, c3, c4, c5], c < 7) (hz : z < 3)
    (hok : okC [c0, c1, c2, c3, c4, c5] D z = true) (a b : Int) (x : QConf) (hne : x.st ≠ z)
    (h2 : ∀ y, x.tape y < 2) (ha : a ≤ x.pos) (hb : x.pos ≤ b)
    (hsupp : ∀ y, (y < a ∨ b < y) → x.tape y = 0)
    (hH : QHalts (URTM.Three.realize [c0, c1, c2, c3, c4, c5] D) x) :
    qrun (URTM.Three.realize [c0, c1, c2, c3, c4, c5] D) (3 * (1 + (bnd 2 (a - 1) (b + 1) + 1))) x = none := by
  obtain ⟨hD, hinj, hall⟩ := okC_spec hok
  by_cases hst : x.st < 3
  · obtain ⟨n, hn⟩ := hH
    have hH' := sim_bwd hlt hz hok n x hst hne h2 hn
    obtain ⟨qa, qb, hT'⟩ := realize_twoState (D := D) (elim_lt7 hlt z) hinj hz
    have hno : ∀ r ∈ URTM.Three.realize (elim [c0, c1, c2, c3, c4, c5] z) D, r.q ≠ z := by
      intro r hr
      obtain ⟨i, s, c, _, _, _, hm, hc0, rfl⟩ := mem_realize6 hr
      rcases hall c hm with h | h
      · exact absurd h hc0
      · exact h
    have hb' := (halts_noEntry hT' hno (realize_closed _ _) a b x h2 ha hb hsupp).mp hH'
    exact sim_fwd hlt hz hok _ x hst hne h2 hb'
  · -- 働かない状態からは規則が無い
    have hs : qstep (URTM.Three.realize [c0, c1, c2, c3, c4, c5] D) x = none := by
      unfold qstep
      cases hf : find? (URTM.Three.realize [c0, c1, c2, c3, c4, c5] D) x.st (x.tape x.pos) with
      | none => rfl
      | some r =>
        obtain ⟨hm, hp, _⟩ := find?_spec hf
        have := realize_src3 _ _ r hm
        rw [hp] at this; exact absurd this hst
    exact qrun_none_mono _ x 1 _ (qrun_succ_none _ 0 hs) (by omega)

/-- **群 C の有界停止**（正規形の表、`QConf` の上）: `okC` が通れば、窓 [a, b] の外が空白で記号が 0, 1 の配置から
    止まる実行は `2 + 3 * (1 + (bnd 2 (a − 3) (b + 3) + 1))` 歩以内に止まる（始状態は任意。z から始めても
    2 歩以内に z を離れる）。 -/
theorem halts_okC (hlt : ∀ c ∈ [c0, c1, c2, c3, c4, c5], c < 7) (hz : z < 3)
    (hok : okC [c0, c1, c2, c3, c4, c5] D z = true) (a b : Int) (c : QConf)
    (h2 : ∀ y, c.tape y < 2) (ha : a ≤ c.pos) (hb : c.pos ≤ b)
    (hsupp : ∀ y, (y < a ∨ b < y) → c.tape y = 0) :
    QHalts (URTM.Three.realize [c0, c1, c2, c3, c4, c5] D) c ↔
      qrun (URTM.Three.realize [c0, c1, c2, c3, c4, c5] D)
        (2 + 3 * (1 + (bnd 2 (a - 2 - 1) (b + 2 + 1) + 1))) c = none := by
  constructor
  · intro hH
    obtain ⟨hD, _, _⟩ := okC_spec hok
    obtain ⟨Tm, hR⟩ := qhalts_haltRun hH
    rcases Nat.lt_or_ge Tm 2 with hlt2 | hge2
    · exact qrun_none_mono _ c (Tm + 1) _ hR.dead (by omega)
    · -- 2 歩以内に z を離れる（z に 3 つの時刻で居続けると止まらない）
      have hk : ∃ k, k ≤ 2 ∧ (qtr (URTM.Three.realize [c0, c1, c2, c3, c4, c5] D) c k).st ≠ z := by
        apply Classical.byContradiction
        intro hno
        have hst : ∀ k, k ≤ 2 → (qtr (URTM.Three.realize [c0, c1, c2, c3, c4, c5] D) c k).st = z :=
          fun k hk => Classical.byContradiction fun h => hno ⟨k, hk, h⟩
        obtain ⟨r₀, hr₀, _, he₀⟩ := qstep_some (hR.step 0 (by omega))
        have hq₀ : r₀.q = z := by have := hst 1 (by omega); rw [he₀] at this; exact this
        have hd₀ : r₀.d = Dir.Z := by rw [(mem_realize hr₀).2.2, hq₀, hD]
        exact stay_zero (realize_dir _ _) (realize_closed _ _) hR h2 hge2 hst hr₀ hq₀ hd₀
      obtain ⟨k, hk2, hkz⟩ := hk
      have hrun := hR.run k (by omega)
      obtain ⟨g1, g2, g3⟩ := qrun_window k hrun ha hb hsupp
      have hH' : QHalts (URTM.Three.realize [c0, c1, c2, c3, c4, c5] D)
          (qtr (URTM.Three.realize [c0, c1, c2, c3, c4, c5] D) c k) := ⟨_, hR.run_from k (by omega)⟩
      have h := halts_elim_off hlt hz hok (a - 2) (b + 2) _ hkz
        (qrun_tape_lt (realize_closed _ _) k hrun h2) (by omega) (by omega)
        (fun y hy => g3 y (by omega)) hH'
      have h4 : qrun (URTM.Three.realize [c0, c1, c2, c3, c4, c5] D)
          (k + 3 * (1 + (bnd 2 (a - 2 - 1) (b + 2 + 1) + 1))) c = none := by
        rw [qrun_add, hrun]; exact h
      exact qrun_none_mono _ c _ _ h4 (by omega)
  · intro h; exact ⟨_, h⟩

end

section
variable {tbl : List Quint} {q₀ q₁ q₂ sg : Nat}

/-- 窓の幅だけで書いた群 C の上界。 -/
def bndC (w : Nat) : Nat := 2 + 3 * (1 + (bndN 2 (w + 6) + 1))

theorem bndC_primrec : Primrec bndC := by
  have h := Primrec.nat_add.comp (Primrec.const 2)
    (Primrec.nat_mul.comp (Primrec.const 3)
      (Primrec.nat_add.comp (Primrec.const 1)
        (Primrec.nat_add.comp
          (bndN_primrec.comp (Primrec.const 2) (Primrec.nat_add.comp Primrec.id (Primrec.const 6)))
          (Primrec.const 1))))
  exact h.of_eq fun w => rfl

/-- **群 C の有界停止**（任意の表の正規形）。 -/
theorem okC_bound (H : RTM32 tbl q₀ q₁ q₂ sg) {z : Nat} (hz : z < 3)
    (hok : okC (absCodes q₀ q₁ q₂ sg tbl) (absDirs q₀ q₁ q₂ tbl) z = true)
    (c : QConf) (m n : ℕ) (ha : -(m : ℤ) ≤ c.pos) (hb : c.pos ≤ (n : ℤ))
    (hsupp : ∀ x, (x < -(m : ℤ) ∨ (n : ℤ) < x) → c.tape x = 0) (h2 : ∀ x, c.tape x < 2) :
    QHalts (normT (tbl := tbl) (q₀ := q₀) (q₁ := q₁) (q₂ := q₂) (σ := sg)) c ↔
      qrun (normT (tbl := tbl) (q₀ := q₀) (q₁ := q₁) (q₂ := q₂) (σ := sg)) (bndC (m + n)) c = none := by
  have h := halts_okC (D := absDirs q₀ q₁ q₂ tbl) (absCodes_lt H) hz hok (-(m : ℤ)) (n : ℤ) c h2 ha hb hsupp
  have e1 : -(m : ℤ) - 2 - 1 = -((m + 3 : ℕ) : ℤ) := by omega
  have e2 : (n : ℤ) + 2 + 1 = ((n + 3 : ℕ) : ℤ) := by omega
  have e3 : m + 3 + (n + 3) = m + n + 6 := by omega
  rw [e1, e2, bnd_eq, e3] at h
  exact h

/-- 正規形の表 (es, D) に、0 シフトで入られ、まとめて消せる状態がある（群 C）。 -/
def grpC (es : List Nat) (D : List Dir) : Bool := (List.range 3).any fun z => okC es D z

/-- 段階 2b（群 C まで）の例外: 段階 2a の例外のうち、群 B（群 A を含む）にも群 C にも当たらない表。 -/
def isExcC (es : List Nat) (D : List Dir) : Bool := isExc es D && !grpB es D && !grpC es D

/-- **3 状態 2 記号の RTM の停止問題は、U の ID の上で計算可能**（`isExcC` の表を除く）。 -/
theorem three_halting_computable_C (H : RTM32 tbl q₀ q₁ q₂ sg)
    (hne : isExcC (absCodes q₀ q₁ q₂ sg tbl) (absDirs q₀ q₁ q₂ tbl) = false) :
    ∃ f : ZID → Bool, Computable f ∧
      ∀ z, (∀ a ∈ z.2.1 ++ z.2.2, a = 0 ∨ a ∈ [sg]) → (ZHalts tbl z ↔ f z = true) := by
  cases hexc : isExc (absCodes q₀ q₁ q₂ sg tbl) (absDirs q₀ q₁ q₂ tbl) with
  | false => exact three_halting_computable H hexc
  | true =>
    cases hB : grpB (absCodes q₀ q₁ q₂ sg tbl) (absDirs q₀ q₁ q₂ tbl) with
    | true =>
      refine three_halting_computable_B H ?_
      unfold isExcB; rw [hexc, hB]; rfl
    | false =>
      have hC : grpC (absCodes q₀ q₁ q₂ sg tbl) (absDirs q₀ q₁ q₂ tbl) = true := by
        unfold isExcC at hne
        rw [hexc, hB] at hne
        simpa using hne
      obtain ⟨z, hz, hok⟩ := List.any_eq_true.mp hC
      exact halting_computable_of_bound H bndC_primrec (okC_bound H (List.mem_range.mp hz) hok)

/-- **定理（段階 2b、群 A・B・C）: `isExcC` の表を除き、3 状態 2 記号の URTM は存在しない**（Morita Def. 7.1、
    U の記号集合 {0, sg} の上の ID への符号化）。 -/
theorem no_three_two_URTM_C (H : RTM32 tbl q₀ q₁ q₂ sg)
    (hne : isExcC (absCodes q₀ q₁ q₂ sg tbl) (absDirs q₀ q₁ q₂ tbl) = false) :
    ¬ IsUTM_MoritaOver tbl [sg] :=
  not_UTM_of_halting_computable (three_halting_computable_C H hne)

end

end URTM.Meta
