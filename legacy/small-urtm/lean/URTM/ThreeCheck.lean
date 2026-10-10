/-
  3 状態 2 記号 RTM の停止問題の決定可能性 その 1: **検査関数**（計算だけ。証明は持たない）。**手書き**。

  窓 [a, b] の右側 (b, ∞) は初め空白。ヘッドが b から b+1 へ入ってから b へ戻るまでを**訪問**と呼ぶ。
  訪問の振る舞いは、入ったときの状態と (b, ∞) の中身（模様）だけで決まる。
  ここでは模様を有限の列（セル b+1, b+2, … の記号）で持ち、訪問を有限歩だけ模倣して
    * `ret` : b へ戻った（戻ったときの状態・模様・歩数・訪問中の最も右の位置）
    * `halt` : 訪問の中で止まった
    * `div` : 並進周期に入った（二度と b へ戻らず、止まらない。健全性は `ThreeVisit`）
    * `unk` : 決まらなかった
  のどれかを返す。`closedR` は「空の模様から始めて、戻ったときの模様がいつも有限集合 C に入る」
  ことを確かめる。左側は鏡像（`mirT`）の右側として同じ関数で扱う。
-/
import URTM.Basic

namespace URTM.Three
open URTM

/-! ### 訪問の配置（セルの番号は 1 から。0 は「b へ戻った」） -/

/-- 訪問中の配置: 状態、ヘッドのセル番号（b からの距離）、セル 1, 2, … の中身。 -/
structure VConf where
  st : Nat
  pos : Nat
  tape : List Nat
  deriving DecidableEq, Repr

/-- 列の i 番目に書く（足りなければ空白で伸ばす）。 -/
def setPad (l : List Nat) (i v : Nat) : List Nat :=
  if i < l.length then l.set i v else l ++ List.replicate (i - l.length) 0 ++ [v]

def vmove : Dir → Nat → Nat
  | Dir.L, p => p - 1
  | Dir.Z, p => p
  | Dir.R, p => p + 1

/-- 訪問の 1 歩（セル番号 `pos ≥ 1` で使う）。規則が無ければ `none`。 -/
def vstep (tbl : List Quint) (c : VConf) : Option VConf :=
  match find? tbl c.st (c.tape.getD (c.pos - 1) 0) with
  | none => none
  | some r => some ⟨r.q, vmove r.d c.pos, setPad c.tape (c.pos - 1) r.t⟩

/-- 末尾の空白を落とす。 -/
def trim (l : List Nat) : List Nat := (l.reverse.dropWhile (· == 0)).reverse

/-- 並進周期の判定: 過去の配置 `x₁` から今の配置 `x₂` まで、ヘッドが `lo` 以上に居続け、
    状態が同じで、`x₂` が `δ ≥ 0` だけ右にずれ、`lo` から右の中身がずれて一致する。 -/
def shiftMatch (x₁ x₂ : VConf) (lo : Nat) : Bool :=
  x₁.st == x₂.st && x₁.pos ≤ x₂.pos && 1 ≤ lo && lo ≤ x₁.pos &&
    (let δ := x₂.pos - x₁.pos
     let n := max (x₁.tape.length + 1) (x₂.tape.length + 1)
     (List.range n).all fun i => x₁.tape.getD (lo - 1 + i) 0 == x₂.tape.getD (lo - 1 + δ + i) 0)

/-- 履歴（新しい順）。各項は (過去の配置, その時刻から今までのヘッドの最小位置)。 -/
abbrev Hist := List (VConf × Nat)

def histUpdate (h : Hist) (p : Nat) : Hist := h.map fun e => (e.1, min e.2 p)

def histHit (h : Hist) (x : VConf) : Bool := h.any fun e => shiftMatch e.1 x (min e.2 x.pos)

inductive VOut where
  /-- 戻った: 状態 q、模様 P（末尾の空白は落とす）、歩数 k、訪問中の最も右のセル mp。 -/
  | ret (q : Nat) (P : List Nat) (k mp : Nat)
  /-- 止まった: k 歩目の配置で規則が無い。mp は最も右のセル。 -/
  | halt (k mp : Nat)
  | div
  | unk
  deriving DecidableEq, Repr

/-- 訪問を `fuel` 歩まで模倣する。`k` はここまでの歩数、`mp` は最も右のセル。 -/
def visitAux (tbl : List Quint) : Nat → VConf → Hist → Nat → Nat → VOut
  | 0, _, _, _, _ => VOut.unk
  | fuel + 1, x, h, k, mp =>
    match vstep tbl x with
    | none => VOut.halt k mp
    | some y =>
      if y.pos = 0 then VOut.ret y.st (trim y.tape) (k + 1) mp
      else
        let h' := histUpdate ((x, x.pos) :: h) y.pos
        if histHit h' y then VOut.div
        else visitAux tbl fuel y h' (k + 1) (max mp y.pos)

def visitFuel : Nat := 16

/-- 状態 `e` で模様 `P` の (b, ∞) にセル 1 から入った訪問。 -/
def visit (tbl : List Quint) (e : Nat) (P : List Nat) : VOut :=
  visitAux tbl visitFuel ⟨e, 1, P⟩ [] 0 1

/-- 右へ動いて入る状態（訪問はこのどれかで始まる）。 -/
def entR (tbl : List Quint) : List Nat := (tbl.filter fun r => r.d == Dir.R).map (·.q)

/-- 状態 e へ入る規則はどれも e から出る（e は初めにしか居られない）。 -/
def selfOnly (tbl : List Quint) (e : Nat) : Bool := tbl.all fun r => r.q != e || r.p == e

/-- 入り口状態 e で模様 P の訪問が起こりうる: e が初めにしか居られない状態なら、模様は空に限る
    （初めからずっと e で右へ動いてきたので、窓の右側はまだ空白）。 -/
def entOK (tbl : List Quint) (e : Nat) (P : List Nat) : Bool := !(selfOnly tbl e) || P.isEmpty

/-! ### 模様の集合が閉じていることの検査 -/

/-- 1 つの訪問の結果が C と M に収まる。 -/
def outOK (C : List (List Nat)) (M : Nat) : VOut → Bool
  | VOut.ret _ P _ mp => C.contains P && mp ≤ M
  | VOut.halt _ mp => mp ≤ M
  | VOut.div => true
  | VOut.unk => false

/-- **閉包の検査**: 空の模様が C にあり、C のどの模様・どの入り口状態の訪問も C と M に収まる。 -/
def closedR (tbl : List Quint) (C : List (List Nat)) (M : Nat) : Bool :=
  C.contains [] && C.all fun P => P.length ≤ M &&
    (entR tbl).all fun e => !(entOK tbl e P) || outOK C M (visit tbl e P)

/-- 結果から最も右のセルを取り出す（閉包の計算用）。 -/
def outMp : VOut → Nat
  | VOut.ret _ _ _ mp => mp
  | VOut.halt _ mp => mp
  | _ => 0

/-- 閉包を作る（作業列つき。`fuel` 回で打ち切り）。返すのは (C, M)。 -/
def closureAux (tbl : List Quint) : Nat → List (List Nat) → List (List Nat) → Nat →
    Option (List (List Nat) × Nat)
  | 0, _, _, _ => none
  | _ + 1, [], C, M => some (C, M)
  | fuel + 1, P :: work, C, M =>
    let outs := ((entR tbl).filter fun e => entOK tbl e P).map fun e => visit tbl e P
    if outs.any (· == VOut.unk) then none
    else
      let new := (outs.filterMap fun o => match o with
        | VOut.ret _ P' _ _ => if C.contains P' then none else some P'
        | _ => none).eraseDups
      let M' := (outs.map outMp).foldl max (max M P.length)
      closureAux tbl fuel (work ++ new) (C ++ new) M'

def closureFuel : Nat := 12

def closure (tbl : List Quint) : Option (List (List Nat) × Nat) :=
  closureAux tbl closureFuel [[]] [[]] 1

/-- 右側の検査（閉包を作ってから、閉じていることを確かめ直す）。 -/
def checkR (tbl : List Quint) : Bool :=
  match closure tbl with
  | none => false
  | some (C, M) => closedR tbl C M

/-! ### 鏡像（左側を右側として扱う） -/

def flipDir : Dir → Dir
  | Dir.L => Dir.R
  | Dir.Z => Dir.Z
  | Dir.R => Dir.L

def mirTbl (tbl : List Quint) : List Quint := tbl.map fun r => { r with d := flipDir r.d }

/-- 両側の検査。 -/
def check3 (tbl : List Quint) : Bool := checkR tbl && checkR (mirTbl tbl)

end URTM.Three
