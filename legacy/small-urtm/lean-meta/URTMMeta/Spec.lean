/-
  **仕様**: 2 状態 URTM の非存在の主張を読むのに要る定義の**すべて**。

  このファイルは定義だけを持ち、証明を含まない。依存するのは Mathlib と
  `URTM.Basic` の `Dir`・`Quint`（五つ組。状態と記号は自然数の番号）だけである。
  計算向けの表現（リストの先頭一致の表引き、Bool の検査、zipper）は使わず、
  Morita (2017) の定義をそのまま Prop で書く。主定理は `SpecThm.lean` の末尾にあり、
  このファイルの言葉だけで述べられている。

  Morita の定義との対応:
  * 五つ組 `[p, s, t, d, q]` = `Quint`、TM = 五つ組の有限集合（ここでは列 `List Quint`。
    意味は `∈` だけを通して決まるので、列の順序と重複は意味を持たない）
  * ID（Def. 5.5）= `ID`（両側無限テープ、記号 0 が空白）、1 歩 = `Step`、停止 = `Halts`
  * 決定性と可逆性（Def. 5.4。五つ組形式）= `Deterministic`、`Reversible`
  * UTM（Def. 7.1）= `IsUTM`、模倣（Def. 5.8）= `Simulates`
-/
import Mathlib.Computability.Halting
import Mathlib.Logic.Relation
import Mathlib.Data.Set.Finite.Basic
import URTM.Basic

namespace URTM.Spec
open URTM

/-! ### 機械と実行 -/

/-- 計算状況（ID）: 状態、ヘッドの位置、両側無限のテープ（記号 0 が空白）。 -/
structure ID where
  st : ℕ
  pos : ℤ
  tape : ℤ → ℕ

/-- 有限な ID: 空白でないセルが有限個。 -/
def ID.Finite (c : ID) : Prop := {x : ℤ | c.tape x ≠ 0}.Finite

/-- 向きの変位（`L` = −1、`Z` = 0、`R` = +1）。 -/
def shift : Dir → ℤ
  | .L => -1
  | .Z => 0
  | .R => 1

/-- 五つ組 `r` を ID `c` に当てられる（状態と、ヘッドの下の記号が一致する）。 -/
def Applicable (r : Quint) (c : ID) : Prop := r.p = c.st ∧ r.s = c.tape c.pos

/-- 五つ組 `r` を当てた結果（`t` を書き、`d` へ動き、状態 `q` に移る）。 -/
def apply (r : Quint) (c : ID) : ID :=
  ⟨r.q, c.pos + shift r.d, Function.update c.tape c.pos r.t⟩

/-- 1 歩: 表 `T` のある五つ組を当てる。 -/
def Step (T : List Quint) (c c' : ID) : Prop := ∃ r ∈ T, Applicable r c ∧ c' = apply r c

/-- 停止 ID: 当てられる五つ組が無い。 -/
def Halted (T : List Quint) (c : ID) : Prop := ∀ r ∈ T, ¬ Applicable r c

/-- `c` から有限の歩数で停止 ID `c'` に着く。 -/
def HaltsAt (T : List Quint) (c c' : ID) : Prop := Relation.ReflTransGen (Step T) c c' ∧ Halted T c'

/-- `c` から停止する。 -/
def Halts (T : List Quint) (c : ID) : Prop := ∃ c', HaltsAt T c c'

/-! ### 決定性・可逆性・2 状態（Morita Def. 5.4） -/

/-- 決定性: 状態と読む記号が同じ五つ組は同一。 -/
def Deterministic (T : List Quint) : Prop :=
  ∀ r₁ ∈ T, ∀ r₂ ∈ T, r₁.p = r₂.p → r₁.s = r₂.s → r₁ = r₂

/-- 可逆性: 相異なる五つ組の先の状態が同じなら、向きは同じで書く記号は異なる。 -/
def Reversible (T : List Quint) : Prop :=
  ∀ r₁ ∈ T, ∀ r₂ ∈ T, r₁ ≠ r₂ → r₁.q = r₂.q → r₁.d = r₂.d ∧ r₁.t ≠ r₂.t

/-- 2 状態の RTM: 決定的かつ可逆で、五つ組は状態 `q₀, q₁` から出て `q₀, q₁` か
    停止用の疑似状態 `qf`（状態数に数えない。出ていく五つ組は無い）へ入る。 -/
structure TwoStateRTM (T : List Quint) (q₀ q₁ qf : ℕ) : Prop where
  det : Deterministic T
  rev : Reversible T
  ne : q₀ ≠ q₁
  f0 : qf ≠ q₀
  f1 : qf ≠ q₁
  src : ∀ r ∈ T, r.p = q₀ ∨ r.p = q₁
  dst : ∀ r ∈ T, r.q = q₀ ∨ r.q = q₁ ∨ r.q = qf

/-! ### 有限 ID の符号 -/

/-- 有限 ID の符号: (状態, ヘッドの 1 つ左から左へ向かう列, ヘッドから右へ向かう列)。
    列の先は空白。 -/
abbrev Code := ℕ × List ℕ × List ℕ

/-- 符号 `z` を、ヘッドを位置 `p` に置いて ID に戻す。 -/
def toID (p : ℤ) (z : Code) : ID :=
  ⟨z.1, p, fun x => if p ≤ x then z.2.2.getD (x - p).toNat 0 else z.2.1.getD (p - 1 - x).toNat 0⟩

/-! ### 万能性（Morita Def. 5.5, 5.8, 7.1） -/

/-- 表に現れる状態と記号。 -/
def states (T : List Quint) : List ℕ := T.flatMap fun r => [r.p, r.q]
def symbols (T : List Quint) : List ℕ := T.flatMap fun r => [r.s, r.t]

/-- `c ∈ ID(T)`: 有限で、状態は `T` の状態、テープの記号は空白か `T` の記号。 -/
def IsIDOf (T : List Quint) (c : ID) : Prop :=
  c.Finite ∧ c.st ∈ states T ∧ ∀ x, c.tape x = 0 ∨ c.tape x ∈ symbols T

/-- 自然数の 5 つ組を五つ組と読む（向きは 0 = `L`、1 = `Z`、それ以外 = `R`）。 -/
def quintOfNat (x : ℕ × ℕ × ℕ × ℕ × ℕ) : Quint :=
  ⟨x.1, x.2.1, x.2.2.1, match x.2.2.2.1 with | 0 => .L | 1 => .Z | _ => .R, x.2.2.2.2⟩

open Classical in
/-- **TM の列挙 `T n`**: 番号 `n` を Mathlib の標準の全単射で自然数の 5 つ組の列に復号し、
    五つ組の表と読む。決定的でなければ空の表とする（列挙されるのは決定的な TM だけ）。 -/
noncomputable def tm (n : ℕ) : List Quint :=
  let T := (Denumerable.ofNat (List (ℕ × ℕ × ℕ × ℕ × ℕ)) n).map quintOfNat
  if Deterministic T then T else []

/-- **模倣（Def. 5.8、TM どうし）**: 全域の計算可能な符号化 `c` と復号 `d` があって、
    `T` の各有限 ID `toID 0 a ∈ ID(T)` について、
    `T` が停止 ID `β` に着くなら `U` は `c a` から停止し、その停止 ID を `d` で読むと `β` に戻り、
    `T` が停止しないなら `U` も `c a` から停止しない。 -/
def Simulates (U T : List Quint) : Prop :=
  ∃ (c : Code → Code) (d : Code → Option Code), Computable c ∧ Computable d ∧
    ∀ a, IsIDOf T (toID 0 a) →
      (∀ β, HaltsAt T (toID 0 a) β →
        ∃ γ, HaltsAt U (toID 0 (c a)) γ ∧
          ∃ g b, toID γ.pos g = γ ∧ d g = some b ∧ toID β.pos b = β) ∧
      (¬ Halts T (toID 0 a) → ¬ Halts U (toID 0 (c a)))

/-- **UTM（Def. 7.1）**: 列挙 `tm` のすべての TM を、番号 `n` と有限 ID の組から
    計算可能に符号化して模倣する。 -/
def IsUTM (U : List Quint) : Prop :=
  ∃ (c : ℕ × Code → Code) (d : Code → Option Code), Computable c ∧ Computable d ∧
    ∀ n a, IsIDOf (tm n) (toID 0 a) →
      (∀ β, HaltsAt (tm n) (toID 0 a) β →
        ∃ γ, HaltsAt U (toID 0 (c (n, a))) γ ∧
          ∃ g b, toID γ.pos g = γ ∧ d g = some b ∧ toID β.pos b = β) ∧
      (¬ Halts (tm n) (toID 0 a) → ¬ Halts U (toID 0 (c (n, a))))

end URTM.Spec
