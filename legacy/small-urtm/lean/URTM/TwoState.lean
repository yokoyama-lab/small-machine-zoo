/-
  2 状態 RTM の構造定理。**手書き**。キュー R10（森田 B3 の探索空間を確定させる）。

  背景: Morita 2017 は「2 状態 RTM が任意の RTM を模倣できるかは未解決」
  （§5.3.4）「2 状態 URTM があるかは未解決」（§7.4）と書いている。
  同節は障害も説明している — 可逆性から**状態ごとに入ってくるシフト方向が一意**なので、
  Shannon の方法では「方向あたり 2 状態」要り、両方向で 4 状態（Theorem 5.5）、
  情報流を一方向に制限して 3 状態（Lemma 5.10）になる。

  ここでは、その観察を**特定の構成法に依らない形**（＝任意の 2 状態 RTM についての定理）
  にして機械証明する。得られるのは探索空間の確定:

    * (A) 可逆性 ⇒ 同じ次状態へ入る規則は**方向が同一**
    * (B) 2 状態で左シフト・右シフトの両方が現れるなら **0 シフト規則は存在しない**
    * (C) 規則は **(書込記号, 次状態) の組で一意**に決まる（δ の単射性）

  (A)+(B) から「状態 ＝ 直前の移動方向」が出る（2 状態なら状態と方向が 1 対 1）。
  (C) と合わせると δ は {状態}×S → S×{状態} の部分単射で、全域なら **2n 元集合の置換**。

  ⚠ **これは非存在の証明ではない。** 探索空間を狭めるだけ。
-/
import URTM.Quotient

namespace URTM

/-! ## (A) 同じ次状態へ入る規則は方向が同一 -/

/-- 可逆性条件から取り出す実用形。相異なる 2 規則でも同一規則でもよい。 -/
theorem rev_sound {tbl : List Quint} (H : reversible tbl = true)
    {a b : Quint} (ha : a ∈ tbl) (hb : b ∈ tbl) (hq : a.q = b.q) :
    a.d = b.d ∧ (a = b ∨ a.t ≠ b.t) := by
  rcases allPairs_sound H ha hb with rfl | hf | hf
  · exact ⟨rfl, Or.inl rfl⟩
  · -- revPair a b = !(a.q == b.q) || ((a.d == b.d) && !(a.t == b.t))
    have h1 : revPair a b = true := hf
    unfold revPair at h1
    have hqb : (a.q == b.q) = true := by simp [hq]
    rw [hqb] at h1
    simp only [Bool.not_true, Bool.false_or] at h1
    obtain ⟨hd, ht⟩ := and_true_split h1
    refine ⟨eq_of_beq hd, Or.inr ?_⟩
    intro he
    rw [he] at ht
    simp at ht
  · have h1 : revPair b a = true := hf
    unfold revPair at h1
    have hqb : (b.q == a.q) = true := by simp [hq]
    rw [hqb] at h1
    simp only [Bool.not_true, Bool.false_or] at h1
    obtain ⟨hd, ht⟩ := and_true_split h1
    refine ⟨(eq_of_beq hd).symm, Or.inr ?_⟩
    intro he
    rw [he] at ht
    simp at ht

/-- (A) 同じ次状態へ入る規則は方向が同一。**状態 → 入方向は写像として定まる**。 -/
theorem same_next_state_same_dir {tbl : List Quint} (H : reversible tbl = true)
    {a b : Quint} (ha : a ∈ tbl) (hb : b ∈ tbl) (hq : a.q = b.q) : a.d = b.d :=
  (rev_sound H ha hb hq).1

/-- (C) 規則は (書込記号, 次状態) で一意に決まる（δ の単射性）。 -/
theorem rule_unique_of_write_next {tbl : List Quint} (H : reversible tbl = true)
    {a b : Quint} (ha : a ∈ tbl) (hb : b ∈ tbl) (hq : a.q = b.q) (ht : a.t = b.t) :
    a = b := by
  rcases (rev_sound H ha hb hq).2 with he | hne
  · exact he
  · exact absurd ht hne

/-! ## (B) 2 状態なら 0 シフト規則は存在しない -/

/-- (B) 状態が 2 つしかなく、左シフトで入る状態と右シフトで入る状態が
    **どちらも存在する**なら、0 シフト規則は 1 本も存在しない。

    直観: 可逆性から「状態 → 入方向」は写像。2 状態しかないので、左用と右用で
    使い切ってしまい、0 シフトで入る状態の置き場が無い。 -/
theorem no_zero_shift_of_two_states {tbl : List Quint} (H : reversible tbl = true)
    {qL qR : Nat}
    (hstates : ∀ r ∈ tbl, r.q = qL ∨ r.q = qR)
    {a b : Quint} (ha : a ∈ tbl) (hb : b ∈ tbl)
    (haq : a.q = qL) (had : a.d = Dir.L)
    (hbq : b.q = qR) (hbd : b.d = Dir.R) :
    ∀ r ∈ tbl, r.d ≠ Dir.Z := by
  intro r hr hz
  rcases hstates r hr with h | h
  · -- r は qL へ入る ⇒ 方向は a と同じ ＝ L。しかし Z。矛盾
    have : r.d = a.d := same_next_state_same_dir H hr ha (by rw [h, haq])
    rw [hz, had] at this
    exact Dir.noConfusion this
  · have : r.d = b.d := same_next_state_same_dir H hr hb (by rw [h, hbq])
    rw [hz, hbd] at this
    exact Dir.noConfusion this

/-- (B の系) 2 状態のとき、**状態が直前の移動方向を決める**。
    qL へ入る規則はすべて左シフト、qR へ入る規則はすべて右シフト。 -/
theorem state_determines_dir {tbl : List Quint} (H : reversible tbl = true)
    {qL qR : Nat} {a b : Quint} (ha : a ∈ tbl) (hb : b ∈ tbl)
    (haq : a.q = qL) (had : a.d = Dir.L)
    (hbq : b.q = qR) (hbd : b.d = Dir.R) :
    (∀ r ∈ tbl, r.q = qL → r.d = Dir.L) ∧ (∀ r ∈ tbl, r.q = qR → r.d = Dir.R) := by
  constructor
  · intro r hr h
    have := same_next_state_same_dir H hr ha (by rw [h, haq])
    rw [this, had]
  · intro r hr h
    have := same_next_state_same_dir H hr hb (by rw [h, hbq])
    rw [this, hbd]

/-- 上の 2 つから: 2 状態 RTM で左右が両方現れるなら、**すべての規則の方向は
    次状態だけで決まり、0 シフトは無い**。探索空間はこの形に限られる。 -/
theorem two_state_shape {tbl : List Quint} (H : reversible tbl = true)
    {qL qR : Nat}
    (hstates : ∀ r ∈ tbl, r.q = qL ∨ r.q = qR)
    {a b : Quint} (ha : a ∈ tbl) (hb : b ∈ tbl)
    (haq : a.q = qL) (had : a.d = Dir.L)
    (hbq : b.q = qR) (hbd : b.d = Dir.R) :
    (∀ r ∈ tbl, r.d ≠ Dir.Z) ∧
    (∀ r ∈ tbl, r.q = qL → r.d = Dir.L) ∧
    (∀ r ∈ tbl, r.q = qR → r.d = Dir.R) :=
  ⟨no_zero_shift_of_two_states H hstates ha hb haq had hbq hbd,
   (state_determines_dir H ha hb haq had hbq hbd).1,
   (state_determines_dir H ha hb haq had hbq hbd).2⟩

/-! ## 空虚でないことの確認（具体の 2 状態 RTM に当てる） -/

/-- 最小の 2 状態 2 記号 RTM。状態 0 は左シフトで入られ、状態 1 は右シフトで入られる。 -/
def demoTbl : List Quint := [⟨0, 0, 1, Dir.R, 1⟩, ⟨1, 0, 0, Dir.L, 0⟩]

theorem demo_det : deterministic demoTbl = true := by decide
theorem demo_rev : reversible demoTbl = true := by decide

/-- 構造定理をこの表に当てたもの。仮説がすべて外れることを見せる
    （＝定理が空虚でない）。 -/
theorem demo_shape :
    (∀ r ∈ demoTbl, r.d ≠ Dir.Z) ∧
    (∀ r ∈ demoTbl, r.q = 0 → r.d = Dir.L) ∧
    (∀ r ∈ demoTbl, r.q = 1 → r.d = Dir.R) :=
  two_state_shape demo_rev
    (qL := 0) (qR := 1)
    (by decide)
    (a := ⟨1, 0, 0, Dir.L, 0⟩) (b := ⟨0, 0, 1, Dir.R, 1⟩)
    (by decide) (by decide) rfl rfl rfl rfl

end URTM
