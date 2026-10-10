/-
  **文字列上の ID（Morita の αqβ）の側の Def. 7.1**: legacy lean-meta の定義の写し（docs/28）。

  lean-univ は legacy の lean-meta を import できない（lean-meta は同名パッケージ `urtm` の legacy 版に
  依存する）ので、`legacy/small-urtm/lean-meta/URTMMeta/{Zipper,NoURTM,Morita}.lean` の定義を
  **字句どおりに**写す（名前空間も `URTM.Meta` のまま）。各定義の本文（`def`/`abbrev` の行から次の空行まで）が
  原本と一致することを `tests/morita_defs.py`（check.sh の層 (1b)）が検査する。証明は写さない。

  `ZID = (状態, 左の中身（ヘッドに近い順）, ヘッドから右の中身)` は、Morita の ID αqβ
  （α, β ∈ Γ*、q ∈ Q。ヘッドは β の先頭を読む）の α を逆順に持ったもの。ヘッドの位置は持たない。
  ID は両端の空白の付け外しを除いて同一視する（`ZSame`）。
-/
import Mathlib.Computability.Primrec.List
import Mathlib.Computability.Partrec
import URTM.Basic

namespace URTM.Meta
open URTM

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

/-- U が止まって配置 z に着く。 -/
def ZHaltsAt (tbl : List Quint) (z₀ z : ZID) : Prop :=
  ∃ n, zrun tbl n z₀ = some z ∧ zstep tbl z = none

/-- 方向の復号（0 = −, 1 = 0, それ以外 = +）。 -/
def dirOf : ℕ → Dir
  | 0 => .L
  | 1 => .Z
  | _ => .R

/-- 数の 5 つ組 (p, s, t, d, q) を五つ組に。 -/
def quintOf (x : ℕ × ℕ × ℕ × ℕ × ℕ) : Quint :=
  ⟨x.1, x.2.1, x.2.2.1, dirOf x.2.2.2.1, x.2.2.2.2⟩

/-- **TM の列挙 Tₙ**。 -/
def tmOf (n : ℕ) : List Quint := (Denumerable.ofNat (List (ℕ × ℕ × ℕ × ℕ × ℕ)) n).map quintOf

/-- 表に現れる状態（五つ組の p と q）。 -/
def statesOf (T : List Quint) : List Nat := T.flatMap fun r => [r.p, r.q]

/-- 表に現れる記号（五つ組の s と t）。空白 0 は別に許す。 -/
def symsOf (T : List Quint) : List Nat := T.flatMap fun r => [r.s, r.t]

/-- **α ∈ ID(T)**（Def. 5.5）: 状態は T の状態、テープの記号は空白か T の記号。 -/
def IDOf (T : List Quint) (z : ZID) : Prop :=
  z.1 ∈ statesOf T ∧ ∀ a ∈ z.2.1 ++ z.2.2, a = 0 ∨ a ∈ symsOf T

/-- 有限 ID の同一視（状態が同じで、テープの中身が両端の空白を除いて同じ）。 -/
def ZSame (z z' : ZID) : Prop :=
  z.1 = z'.1 ∧ (∀ i, z.2.1.getD i 0 = z'.2.1.getD i 0) ∧ (∀ i, z.2.2.getD i 0 = z'.2.2.getD i 0)

/-- 列挙 E の TM をすべて（番号つきで、α ∈ ID(E n) について）模倣する。 -/
def SimulatesEnum (tbl : List Quint) (E : ℕ → List Quint) : Prop :=
  ∃ (c : ℕ × ZID → ZID) (d : ZID → Option ZID), Computable c ∧ Computable d ∧
    ∀ n α, IDOf (E n) α → (∀ β, ZHaltsAt (E n) α β →
        ∃ γ, ZHaltsAt tbl (c (n, α)) γ ∧ ∃ β', d γ = some β' ∧ ZSame β' β) ∧
      (¬ ZHalts (E n) α → ¬ ZHalts tbl (c (n, α)))

/-- **Morita Def. 7.1（UTM）**: TM の実効的な列挙 Tₙ（`tmOf`）のすべてを、各 α ∈ ID(Tₙ) で模倣する。 -/
def IsUTM_Morita (tbl : List Quint) : Prop := SimulatesEnum tbl tmOf

end URTM.Meta
