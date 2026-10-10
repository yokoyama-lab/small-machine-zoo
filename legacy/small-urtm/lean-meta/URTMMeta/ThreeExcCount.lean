/-
  **段階 2b の例外の数を kernel で確定する**（2026-10-04）。

  主定理 `no_three_two_URTM_C` の仮定は `isExcC es D = false`。ここでは、仮定が満たされない正規形の表
  （`isExcC es D = true`）が**ちょうど 816 個**であることを、kernel の評価（`decide +kernel`）で示す。
  それまでは `#eval` と Python でしか数えていなかった（§12.8.7）。

  全列挙（359,829 表）の上で `isExcC` を評価すると、`isExc` が鍵の一覧を線形に探すうえ表ごとに `realize`
  などを作るので重い（以前の試みは 20 GB で打ち切り）。ここでは逆に、`isExc` が真になる表の鍵は一覧
  `excKeys`（2,280 個）に載ることを使い、`excKeys` の上だけで `grpB`・`grpC` を評価する。
  一覧の外の表で `isExcC` が真にならないことは、鍵から表を戻す関数 `unkey` が `key` の逆であること
  （`unkey_key`、一般の証明）から出る。

  * `excCTables`: 例外の表の一覧（`excKeys` を `!grpB && !grpC` で絞り、`unkey` で表に戻したもの）。
  * `mem_excCTables`: 符号 6 つ（各 7 未満）・向き 3 つの表 (es, D) について、
    `isExcC es D = true ↔ (es, D) ∈ excCTables`。
  * `excCTables_length`: 長さ 816。`excCTables_nodup`: 重複なし。
  * `excCTables_inj`: 一覧の表はどれも 0 でない符号が重ならない（可逆な正規形）。
  類の数（68）は対称性の軌道の数で、ここでは数えていない。
-/
import URTMMeta.ThreeC

namespace URTM.Meta
open URTM URTM.TwoState URTM.Three

/-- 鍵から表へ（`key` の逆）。 -/
def unkey (k : Nat) : List Nat × List Dir :=
  ([k % 7, k / 7 % 7, k / 49 % 7, k / 343 % 7, k / 2401 % 7, k / 16807 % 7],
   [dirList.getD (k / 117649 % 3) Dir.L, dirList.getD (k / 117649 / 3 % 3) Dir.L,
    dirList.getD (k / 117649 / 9 % 3) Dir.L])

theorem dnum3_lt (d : Dir) : dnum3 d < 3 := by cases d <;> decide

theorem dirList_dnum3 (d : Dir) : dirList.getD (dnum3 d) Dir.L = d := by cases d <;> rfl

/-- 符号 6 つ（各 7 未満）と向き 3 つの表。 -/
def ValidKey (es : List Nat) (D : List Dir) : Prop :=
  es.length = 6 ∧ (∀ c ∈ es, c < 7) ∧ D.length = 3

/-- **`unkey` は `key` の逆**。 -/
theorem unkey_key {es : List Nat} {D : List Dir} (h : ValidKey es D) : unkey (key es D) = (es, D) := by
  obtain ⟨h6, h7, h3⟩ := h
  match es, D, h6, h3 with
  | [a, b, c, d, e, f], [x, y, z], _, _ =>
    have ha := h7 a (by simp); have hb := h7 b (by simp); have hc := h7 c (by simp)
    have hd := h7 d (by simp); have he := h7 e (by simp); have hf := h7 f (by simp)
    have hx := dnum3_lt x; have hy := dnum3_lt y; have hz := dnum3_lt z
    have hK : key [a, b, c, d, e, f] [x, y, z] =
        a + 7 * (b + 7 * (c + 7 * (d + 7 * (e + 7 * (f + 7 * (dnum3 x + 3 * (dnum3 y + 3 * dnum3 z))))))) := rfl
    generalize key [a, b, c, d, e, f] [x, y, z] = K at hK
    unfold unkey
    rw [show K / 117649 % 3 = dnum3 x by omega, show K / 117649 / 3 % 3 = dnum3 y by omega,
      show K / 117649 / 9 % 3 = dnum3 z by omega, dirList_dnum3, dirList_dnum3, dirList_dnum3]
    simp only [Prod.mk.injEq, List.cons.injEq, and_true]
    omega

/-! ### 例外の表の一覧 -/

/-- 段階 2b の例外（群 B・C に当たらない）の鍵。 -/
def excCKeys : List Nat :=
  excKeys.filter fun k => !grpB (unkey k).1 (unkey k).2 && !grpC (unkey k).1 (unkey k).2

/-- **例外の表の一覧**。 -/
def excCTables : List (List Nat × List Dir) := excCKeys.map unkey

/-- 一覧の鍵は `unkey` で表に戻り、`key` で元の鍵に戻る（kernel の評価）。 -/
theorem excKeys_roundtrip : excKeys.all (fun k => key (unkey k).1 (unkey k).2 == k) = true := by
  decide +kernel

theorem unkey_valid (k : Nat) : ValidKey (unkey k).1 (unkey k).2 := by
  refine ⟨rfl, fun c hc => ?_, rfl⟩
  simp only [unkey, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> exact Nat.mod_lt _ (by decide)

theorem key_unkey_of_mem {k : Nat} (hk : k ∈ excKeys) : key (unkey k).1 (unkey k).2 = k := by
  have := List.all_eq_true.mp excKeys_roundtrip k hk
  simpa using this

/-- **例外の表はちょうど一覧のもの**: 符号 6 つ（各 7 未満）・向き 3 つの表について、
    主定理の仮定が外れる（`isExcC = true`）のは一覧に載る表だけで、一覧の表はどれも外れる。 -/
theorem mem_excCTables {es : List Nat} {D : List Dir} (h : ValidKey es D) :
    isExcC es D = true ↔ (es, D) ∈ excCTables := by
  constructor
  · intro hc
    unfold isExcC isExc at hc
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.contains_iff_mem] at hc
    obtain ⟨⟨hk, hB⟩, hC⟩ := hc
    refine List.mem_map.mpr ⟨key es D, List.mem_filter.mpr ⟨hk, ?_⟩, unkey_key h⟩
    rw [unkey_key h]; simp [hB, hC]
  · intro hm
    obtain ⟨k, hk, he⟩ := List.mem_map.mp hm
    obtain ⟨hk1, hk2⟩ := List.mem_filter.mp hk
    obtain ⟨rfl, rfl⟩ : (unkey k).1 = es ∧ (unkey k).2 = D := by rw [he]; exact ⟨rfl, rfl⟩
    unfold isExcC isExc
    rw [key_unkey_of_mem hk1]
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hk2
    simp [List.contains_iff_mem, hk1, hk2.1, hk2.2]

/-- **例外の表は 816 個**（kernel の評価）。 -/
theorem excCKeys_length : excCKeys.length = 816 := by decide +kernel

theorem excCTables_length : excCTables.length = 816 := by
  unfold excCTables; rw [List.length_map, excCKeys_length]

/-- 狭義単調増加（線形時間の Bool 検査）。 -/
def ascB : List Nat → Bool
  | a :: b :: l => decide (a < b) && ascB (b :: l)
  | _ => true

theorem ascB_tail {a : Nat} {l : List Nat} (h : ascB (a :: l) = true) : ascB l = true := by
  cases l with
  | nil => rfl
  | cons b l => simp only [ascB, Bool.and_eq_true] at h; exact h.2

theorem ascB_head : ∀ {a : Nat} {l : List Nat}, ascB (a :: l) = true → ∀ y ∈ l, a < y
  | _, [], _, y, hy => by simp at hy
  | a, b :: l, h, y, hy => by
    simp only [ascB, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases List.mem_cons.mp hy with rfl | hy
    · exact h.1
    · exact Nat.lt_trans h.1 (ascB_head h.2 y hy)

theorem ascB_pairwise : ∀ (l : List Nat), ascB l = true → l.Pairwise (· < ·)
  | [], _ => List.Pairwise.nil
  | a :: l, h => List.Pairwise.cons (ascB_head h) (ascB_pairwise l (ascB_tail h))

theorem excKeys_asc : ascB excKeys = true := by decide +kernel

theorem excKeys_nodup : excKeys.Nodup :=
  (ascB_pairwise _ excKeys_asc).imp (fun h => Nat.ne_of_lt h)

/-- 一覧に重複は無い（鍵が相異なり、`unkey` は一覧の鍵の上で単射）。 -/
theorem excCTables_nodup : excCTables.Nodup := by
  unfold excCTables
  refine List.Nodup.map_on (fun k hk k' hk' he => ?_) (excKeys_nodup.filter _)
  have h1 := key_unkey_of_mem (List.mem_filter.mp hk).1
  have h2 := key_unkey_of_mem (List.mem_filter.mp hk').1
  rw [← h1, ← h2, he]

/-- 一覧の表はどれも 0 でない符号が重ならない（可逆な正規形）。 -/
theorem excCTables_inj : excCTables.all (fun t => injCodes t.1) = true := by decide +kernel

end URTM.Meta
