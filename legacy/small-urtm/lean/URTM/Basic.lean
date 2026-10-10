/-
  1 テープ五つ組形式のチューリング機械と、可逆性条件（Morita 2017, Def. 5.4）。

  ここは「機械の性質を Lean の項として書き、カーネルに検算させる」ための最小の土台。
  mathlib には依存しない（ビルドを軽く保つ）。

  層の区別:
  * `decide` で閉じるもの（決定性・可逆性）はカーネル検証。これが層1の土台。
  * 具体配置の実行（コーパス再現）は有界全数検査なので `native_decide` を使い、
    使ったことを明示する。
-/

namespace URTM

/-- ヘッドの移動方向。`Z` は 0 シフト（停止規則で使われる）。 -/
inductive Dir where
  | L
  | Z
  | R
  deriving DecidableEq, Repr, Inhabited

/-- 五つ組 `[p, s, t, d, q]`: 状態 `p` で記号 `s` を読み、`t` を書き、`d` へ動き、`q` へ移る。
    状態・記号は通し番号（`Nat`）で表す。記述ファイルからの生成器が番号を割り当てる。 -/
structure Quint where
  p : Nat
  s : Nat
  t : Nat
  d : Dir
  q : Nat
  deriving DecidableEq, Repr, Inhabited

/-- 決定性: 相異なる五つ組で現状態が同じなら読込記号は相異なる。 -/
def detPair (a b : Quint) : Bool :=
  !(a.p == b.p) || !(a.s == b.s)

/-- 可逆性条件: 相異なる五つ組で次状態が同じなら、方向は同一で書込記号は相異なる。
    `(q₁ = q₂) → (d₁ = d₂ ∧ t₁ ≠ t₂)` -/
def revPair (a b : Quint) : Bool :=
  !(a.q == b.q) || ((a.d == b.d) && !(a.t == b.t))

/-- 相異なる 2 要素すべてに述語が成り立つか。 -/
def allPairs (f : Quint → Quint → Bool) : List Quint → Bool
  | [] => true
  | x :: xs => xs.all (f x) && allPairs f xs

def deterministic (tbl : List Quint) : Bool := allPairs detPair tbl

def reversible (tbl : List Quint) : Bool := allPairs revPair tbl

/-- 計算状況。テープは片側無限で、`tape` の右端より先はすべて空白。 -/
structure Conf where
  st : Nat
  pos : Nat
  tape : Array Nat
  deriving Repr, Inhabited

/-- 表引き。決定性が成り立つ表では高々 1 本しか一致しない。 -/
def find? (tbl : List Quint) (p s : Nat) : Option Quint :=
  tbl.find? (fun r => r.p == p && r.s == s)

/-- 位置 `i` の記号。テープの外は空白。 -/
def readAt (blank : Nat) (t : Array Nat) (i : Nat) : Nat :=
  if h : i < t.size then t[i] else blank

/-- 位置 `i` へ書き込む。必要なら空白で右へ伸ばす。 -/
def writeAt (blank : Nat) (t : Array Nat) (i v : Nat) : Array Nat :=
  let t := if i < t.size then t else
    (List.range (i + 1 - t.size)).foldl (fun acc _ => acc.push blank) t
  t.set! i v

/-- 1 ステップ。規則が無ければ停止（`none`）。左端から落ちる場合も停止扱い。 -/
def step (tbl : List Quint) (blank : Nat) (c : Conf) : Option Conf :=
  match find? tbl c.st (readAt blank c.tape c.pos) with
  | none => none
  | some r =>
      let tape := writeAt blank c.tape c.pos r.t
      match r.d with
      | Dir.L => if c.pos = 0 then none else some { st := r.q, pos := c.pos - 1, tape }
      | Dir.Z => some { st := r.q, pos := c.pos, tape }
      | Dir.R => some { st := r.q, pos := c.pos + 1, tape }

/-- `n` ステップ以内に停止するか。停止したときのステップ数を返す。 -/
def haltsIn (tbl : List Quint) (blank : Nat) : Nat → Conf → Option Nat
  | 0, _ => none
  | n + 1, c =>
      match step tbl blank c with
      | none => some 0
      | some c' => (haltsIn tbl blank n c').map (· + 1)

/-- 停止時のテープ（`n` ステップ以内に停止しなければ `none`）。 -/
def finalTape (tbl : List Quint) (blank : Nat) : Nat → Conf → Option (Array Nat)
  | 0, _ => none
  | n + 1, c =>
      match step tbl blank c with
      | none => some c.tape
      | some c' => finalTape tbl blank n c'

end URTM
