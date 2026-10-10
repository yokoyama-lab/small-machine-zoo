/-
  有限 ID の zipper 表現と、両側無限テープの実行（本体の `qrun`）との 1 歩ずつの一致。

  Morita の ID は有限の記述（非空白部分が有限）なので、`ZID = (状態, 左の中身, 右の中身)` で表す。
  左はヘッドの 1 つ左から遠ざかる順、右はヘッドの位置から右へ。末尾より先は空白（記号 0）。
  計算可能性（`Computable.lean`）はこの表現の上で述べる。mathlib には依存しない。
-/
import URTMMeta.Bounded

namespace URTM.Meta
open URTM URTM.TwoState

/-- 有限 ID: (状態, ヘッドの左の中身（近い順）, ヘッドから右の中身)。 -/
abbrev ZID := Nat × List Nat × List Nat

/-- 方向の番号（L=0, Z=1, R=2）。 -/
def dnum : Dir → Nat
  | .L => 0
  | .Z => 1
  | .R => 2

/-- 規則の右辺（書く記号, 方向の番号, 次状態）。 -/
def rhs (r : Quint) : Nat × Nat × Nat := (r.t, dnum r.d, r.q)

/-- 表引き（`find?` と同じ先頭一致）を番号の組で返す。 -/
def look : List Quint → Nat → Nat → Option (Nat × Nat × Nat)
  | [], _, _ => none
  | r :: tbl, q, s => if r.p = q ∧ r.s = s then some (rhs r) else look tbl q s

theorem look_eq (tbl : List Quint) (q s : Nat) : look tbl q s = (find? tbl q s).map rhs := by
  induction tbl with
  | nil => rfl
  | cons r tbl ih =>
    unfold look
    unfold find? at ih ⊢
    rw [List.find?_cons]
    by_cases h : r.p = q ∧ r.s = s
    · rw [if_pos h]; simp [h.1, h.2]
    · rw [if_neg h, ih]
      have : (r.p == q && r.s == s) = false := by
        cases h1 : (r.p == q) <;> cases h2 : (r.s == s) <;> simp_all
      rw [this]

/-- 右辺を当てて動く。 -/
def mv (o : Nat × Nat × Nat) (z : ZID) : ZID :=
  if o.2.1 = 0 then (o.2.2, z.2.1.tail, z.2.1.headD 0 :: o.1 :: z.2.2.tail)
  else if o.2.1 = 1 then (o.2.2, z.2.1, o.1 :: z.2.2.tail)
  else (o.2.2, o.1 :: z.2.1, z.2.2.tail)

/-- zipper の 1 歩。規則が無ければ停止（`none`）。 -/
def zstep (tbl : List Quint) (z : ZID) : Option ZID :=
  (look tbl z.1 (z.2.2.headD 0)).map (fun o => mv o z)

def zrun (tbl : List Quint) : Nat → ZID → Option ZID
  | 0, z => some z
  | n + 1, z =>
    match zstep tbl z with
    | none => none
    | some z' => zrun tbl n z'

/-- zipper で止まる。 -/
def ZHalts (tbl : List Quint) (z : ZID) : Prop := ∃ n, zrun tbl n z = none

/-- 位置 p にヘッドがあるときの両側無限テープ。 -/
def tapeOf (p : Int) (L R : List Nat) : Int → Nat := fun x =>
  if p ≤ x then R.getD (x - p).toNat 0 else L.getD (p - 1 - x).toNat 0

/-- zipper を位置 p に置いた配置。 -/
def realize (p : Int) (z : ZID) : QConf := ⟨z.1, p, tapeOf p z.2.1 z.2.2⟩

theorem getD_tail (l : List Nat) (n : Nat) : l.tail.getD n 0 = l.getD (n + 1) 0 := by
  cases l <;> simp

theorem getD_zero (l : List Nat) : l.getD 0 0 = l.headD 0 := by
  cases l <;> rfl

theorem tape_Z (p : Int) (L R : List Nat) (t : Nat) :
    write (tapeOf p L R) p t = tapeOf p L (t :: R.tail) := by
  funext x
  unfold write tapeOf
  by_cases hx : x = p
  · subst hx; simp
  · rw [if_neg hx]
    by_cases hpx : p ≤ x
    · have hk : (x - p).toNat = (x - p - 1).toNat + 1 := by omega
      rw [if_pos hpx, if_pos hpx, hk, List.getD_cons_succ, getD_tail]
    · rw [if_neg hpx, if_neg hpx]

theorem tape_R (p : Int) (L R : List Nat) (t : Nat) :
    write (tapeOf p L R) p t = tapeOf (p + 1) (t :: L) R.tail := by
  funext x
  unfold write tapeOf
  by_cases hx : x = p
  · subst hx
    rw [if_pos rfl, if_neg (by omega)]
    have : (x + 1 - 1 - x).toNat = 0 := by omega
    rw [this]; rfl
  · rw [if_neg hx]
    by_cases hpx : p ≤ x
    · have hpx' : p + 1 ≤ x := by omega
      have hk : (x - p).toNat = (x - (p + 1)).toNat + 1 := by omega
      rw [if_pos hpx, if_pos hpx', hk, getD_tail]
    · have hpx' : ¬ p + 1 ≤ x := by omega
      have hk : (p + 1 - 1 - x).toNat = (p - 1 - x).toNat + 1 := by omega
      rw [if_neg hpx, if_neg hpx', hk, List.getD_cons_succ]

theorem tape_L (p : Int) (L R : List Nat) (t : Nat) :
    write (tapeOf p L R) p t = tapeOf (p - 1) L.tail (L.headD 0 :: t :: R.tail) := by
  funext x
  unfold write tapeOf
  by_cases hx : x = p
  · subst hx
    rw [if_pos rfl, if_pos (by omega)]
    have : (x - (x - 1)).toNat = 0 + 1 := by omega
    rw [this, List.getD_cons_succ]; rfl
  · rw [if_neg hx]
    by_cases hpx : p ≤ x
    · have hpx' : p - 1 ≤ x := by omega
      have hk : (x - (p - 1)).toNat = (x - p - 1).toNat + 1 + 1 := by omega
      have hk' : (x - p).toNat = (x - p - 1).toNat + 1 := by omega
      rw [if_pos hpx, if_pos hpx', hk, hk', List.getD_cons_succ, List.getD_cons_succ, getD_tail]
    · by_cases hx1 : x = p - 1
      · subst hx1
        rw [if_neg hpx, if_pos (by omega)]
        have h0 : (p - 1 - (p - 1)).toNat = 0 := by omega
        rw [h0, List.getD_cons_zero, getD_zero]
      · have hpx' : ¬ p - 1 ≤ x := by omega
        have hk : (p - 1 - x).toNat = (p - 1 - 1 - x).toNat + 1 := by omega
        rw [if_neg hpx, if_neg hpx', hk, getD_tail]

theorem qstep_realize_eq (tbl : List Quint) (p : Int) (z : ZID) :
    qstep tbl (realize p z) = (find? tbl z.1 (z.2.2.headD 0)).map
      (fun r => (⟨r.q, move r.d p, write (tapeOf p z.2.1 z.2.2) p r.t⟩ : QConf)) := by
  have hread : (realize p z).tape (realize p z).pos = z.2.2.headD 0 := by
    show tapeOf p z.2.1 z.2.2 p = _
    unfold tapeOf; rw [if_pos (Int.le_refl p), Int.sub_self]; exact getD_zero _
  unfold qstep
  rw [hread]
  show (match find? tbl z.1 (z.2.2.headD 0) with
    | none => none
    | some r => some (⟨r.q, move r.d p, write (tapeOf p z.2.1 z.2.2) p r.t⟩ : QConf)) = _
  cases find? tbl z.1 (z.2.2.headD 0) <;> rfl

theorem zstep_eq (tbl : List Quint) (z : ZID) :
    zstep tbl z = (find? tbl z.1 (z.2.2.headD 0)).map (fun r => mv (rhs r) z) := by
  unfold zstep; rw [look_eq, Option.map_map]; rfl

theorem realize_mv (p : Int) (r : Quint) (z : ZID) :
    ∃ p', realize p' (mv (rhs r) z) = ⟨r.q, move r.d p, write (tapeOf p z.2.1 z.2.2) p r.t⟩ := by
  obtain ⟨st, L, R⟩ := z
  cases hd : r.d with
  | L => exact ⟨p - 1, by simp [realize, mv, rhs, dnum, hd, move, tape_L]⟩
  | Z => exact ⟨p, by simp [realize, mv, rhs, dnum, hd, move, tape_Z]⟩
  | R => exact ⟨p + 1, by simp [realize, mv, rhs, dnum, hd, move, tape_R]⟩

/-- 1 歩の一致: 両側無限テープの 1 歩は zipper の 1 歩に対応する（位置は動く）。 -/
theorem qstep_realize (tbl : List Quint) (p : Int) (z : ZID) :
    (zstep tbl z = none → qstep tbl (realize p z) = none) ∧
    (∀ z', zstep tbl z = some z' → ∃ p', qstep tbl (realize p z) = some (realize p' z')) := by
  rw [zstep_eq, qstep_realize_eq]
  cases find? tbl z.1 (z.2.2.headD 0) with
  | none => exact ⟨fun _ => rfl, fun z' h' => by simp at h'⟩
  | some r =>
    refine ⟨fun h' => by simp at h', fun z' h' => ?_⟩
    simp only [Option.map_some, Option.some.injEq] at h'
    subst h'
    obtain ⟨p', hp'⟩ := realize_mv p r z
    exact ⟨p', by rw [hp']; rfl⟩

/-- 実行の一致（止まるかどうか）。 -/
theorem qrun_realize (tbl : List Quint) :
    ∀ n (p : Int) (z : ZID), qrun tbl n (realize p z) = none ↔ zrun tbl n z = none := by
  intro n
  induction n with
  | zero => intro p z; simp [qrun, zrun]
  | succ n ih =>
    intro p z
    have hs := qstep_realize tbl p z
    cases h : zstep tbl z with
    | none =>
      rw [qrun_succ_none tbl n (hs.1 h)]
      simp [zrun, h]
    | some z' =>
      obtain ⟨p', hp'⟩ := hs.2 z' h
      rw [qrun_succ_some tbl n hp', ih p' z']
      simp [zrun, h]

theorem ZHalts_iff (tbl : List Quint) (z : ZID) : ZHalts tbl z ↔ QHalts tbl (realize 0 z) := by
  constructor
  · rintro ⟨n, hn⟩; exact ⟨n, (qrun_realize tbl n 0 z).mpr hn⟩
  · rintro ⟨n, hn⟩; exact ⟨n, (qrun_realize tbl n 0 z).mp hn⟩

end URTM.Meta

namespace URTM.Meta
open URTM URTM.TwoState

/-! ### 配置から計算できる上界 -/

/-- リストの最大値（空なら 0）。 -/
def lmax (l : List Nat) : Nat := l.foldr max 0

theorem getD_le_lmax : ∀ (l : List Nat) (n : Nat), l.getD n 0 ≤ lmax l
  | [], _ => by simp [lmax]
  | a :: l, 0 => by simp only [lmax, List.foldr_cons, List.getD_cons_zero]; exact Nat.le_max_left _ _
  | a :: l, n + 1 => by
    have := getD_le_lmax l n
    simp only [List.getD_cons_succ, lmax, List.foldr_cons] at this ⊢
    omega

theorem getD_len (l : List Nat) (n : Nat) (h : l.length ≤ n) : l.getD n 0 = 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]; rfl

/-- 表が書く記号の最大値。 -/
def tmax (tbl : List Quint) : Nat := lmax (tbl.map Quint.t)

theorem t_le_tmax {tbl : List Quint} {r : Quint} (hr : r ∈ tbl) : r.t ≤ tmax tbl := by
  unfold tmax lmax
  induction tbl with
  | nil => simp at hr
  | cons a tbl ih =>
    rcases List.mem_cons.mp hr with h | h
    · subst h; simp only [List.map_cons, List.foldr_cons]; exact Nat.le_max_left _ _
    · have := ih h; simp only [List.map_cons, List.foldr_cons]; omega

/-- 記号数の上界: 表の書く記号と初期テープの記号のどちらよりも大きい。 -/
def nsymOf (tbl : List Quint) (z : ZID) : Nat := max (tmax tbl + 1) (lmax (z.2.1 ++ z.2.2) + 1)

/-- 停止の判定に回す歩数（配置と表から計算できる）。 -/
def zbound (tbl : List Quint) (z : ZID) : Nat :=
  bnd (nsymOf tbl z) (-(z.2.1.length : Int)) (z.2.2.length : Int) + 1

theorem lmax_append_left (l m : List Nat) : lmax l ≤ lmax (l ++ m) := by
  induction l with
  | nil => simp [lmax]
  | cons a l ih => simp only [lmax, List.cons_append, List.foldr_cons] at ih ⊢; omega

theorem lmax_append_right (l m : List Nat) : lmax m ≤ lmax (l ++ m) := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [lmax, List.cons_append, List.foldr_cons] at ih ⊢; omega

/-- **有限 ID 上の有界停止**: 2 状態 RTM が zipper z から止まる ⟺ `zbound` 歩で止まっている。 -/
theorem zhalts_iff_bound {tbl : List Quint} {q₀ q₁ qf : Nat} (hT : TwoStateRTM tbl q₀ q₁ qf)
    (z : ZID) : ZHalts tbl z ↔ zrun tbl (zbound tbl z) z = none := by
  obtain ⟨st, L, R⟩ := z
  rw [ZHalts_iff, zbound, ← qrun_realize tbl _ 0]
  have hL := lmax_append_left L R
  have hR := lmax_append_right L R
  apply bounded_halting hT (nsymOf tbl (st, L, R))
  · intro r _ _
    have := t_le_tmax (by assumption : r ∈ tbl)
    unfold nsymOf; omega
  · intro x
    show tapeOf 0 L R x < max (tmax tbl + 1) (lmax (L ++ R) + 1)
    unfold tapeOf
    split
    · have := getD_le_lmax R (x - 0).toNat; omega
    · have := getD_le_lmax L (0 - 1 - x).toNat; omega
  · simp only; omega
  · show -(L.length : Int) ≤ 0; omega
  · show (0 : Int) ≤ R.length; omega
  · intro x hx
    have hx' : x < -(L.length : Int) ∨ (R.length : Int) < x := hx
    show tapeOf 0 L R x = 0
    unfold tapeOf
    split
    · exact getD_len R _ (by omega)
    · exact getD_len L _ (by omega)

end URTM.Meta
