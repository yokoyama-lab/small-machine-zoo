/-
  3 状態 2 記号 RTM の停止問題の決定可能性 その 2: **正規形の表と、その全列挙**（計算だけ）。**手書き**。

  正規形: 働く状態は 0, 1, 2、記号は 0, 1。表は 6 つの欄（状態 i・記号 s の欄は 2i+s 番目）の符号で持つ。
  符号 0 は「規則が無い（または働かない状態へ入る＝次で止まる）」、符号 c ≥ 1 は c-1 = 2j+t として
  「t を書き、状態 j へ入る」。状態 j へ入るときの向きは `D[j]`（可逆性から状態ごとに 1 つ）。
  可逆性は「(j, t) の組が欄どうしで重ならない」ことになる。
-/
import URTM.ThreeCheck

namespace URTM.Three
open URTM

def dirList : List Dir := [Dir.L, Dir.Z, Dir.R]

/-- 欄の符号から五つ組を作る（符号 0 なら無し）。 -/
def quintOf (D : List Dir) (i s c : Nat) : List Quint :=
  if c = 0 then [] else [⟨i, s, (c - 1) % 2, D.getD ((c - 1) / 2) Dir.L, (c - 1) / 2⟩]

/-- 正規形の表。 -/
def realize (es : List Nat) (D : List Dir) : List Quint :=
  quintOf D 0 0 (es.getD 0 0) ++ quintOf D 0 1 (es.getD 1 0) ++
  quintOf D 1 0 (es.getD 2 0) ++ quintOf D 1 1 (es.getD 3 0) ++
  quintOf D 2 0 (es.getD 4 0) ++ quintOf D 2 1 (es.getD 5 0)

/-- 0 でない符号が重ならない（可逆性）。 -/
def injCodes (es : List Nat) : Bool :=
  (List.range 6).all fun i => (List.range 6).all fun j =>
    i == j || es.getD i 0 == 0 || es.getD i 0 != es.getD j 0

/-- 止まる欄が無い（働く状態からは決して止まらない）。 -/
def noHalt (es : List Nat) : Bool := es.all (· != 0)

/-- 1 つの表の合否。 -/
def tableOK (es : List Nat) (D : List Dir) : Bool := noHalt es || check3 (realize es D)

/-- 符号の並び 6 つと向き 3 つを全部回す（重なる並びは途中で枝刈り）。 -/
def allD (es : List Nat) (f : List Nat → List Dir → Bool) : Bool :=
  dirList.all fun d0 => dirList.all fun d1 => dirList.all fun d2 => f es [d0, d1, d2]

def fresh (pre : List Nat) (c : Nat) : Bool := c == 0 || !pre.contains c

/-! ### 全列挙（先頭の欄から順に。重なる並びは枝刈り） -/

def lvl4 (c0 c1 c2 c3 : Nat) (f : List Nat → List Dir → Bool) : Bool :=
  (List.range 7).all fun c4 => !(fresh [c0, c1, c2, c3] c4) ||
  (List.range 7).all fun c5 => !(fresh [c0, c1, c2, c3, c4] c5) ||
  allD [c0, c1, c2, c3, c4, c5] f

def lvl3 (c0 c1 c2 : Nat) (f : List Nat → List Dir → Bool) : Bool :=
  (List.range 7).all fun c3 => !(fresh [c0, c1, c2] c3) || lvl4 c0 c1 c2 c3 f

def lvl2 (c0 c1 : Nat) (f : List Nat → List Dir → Bool) : Bool :=
  (List.range 7).all fun c2 => !(fresh [c0, c1] c2) || lvl3 c0 c1 c2 f

def lvl1 (c0 : Nat) (f : List Nat → List Dir → Bool) : Bool :=
  (List.range 7).all fun c1 => !(fresh [c0] c1) || lvl2 c0 c1 f

def lvl0 (f : List Nat → List Dir → Bool) : Bool :=
  (List.range 7).all fun c0 => lvl1 c0 f

/-! ### 表の鍵（例外の列挙用） -/

def dnum3 : Dir → Nat
  | Dir.L => 0
  | Dir.Z => 1
  | Dir.R => 2

/-- 表 (es, D) の番号: Σ es[i]·7^i + 7^6·(D[0] + 3·D[1] + 9·D[2])。 -/
def key (es : List Nat) (D : List Dir) : Nat :=
  es.getD 0 0 + 7 * (es.getD 1 0 + 7 * (es.getD 2 0 + 7 * (es.getD 3 0 + 7 * (es.getD 4 0 +
    7 * (es.getD 5 0 + 7 * (dnum3 (D.getD 0 Dir.L) + 3 * (dnum3 (D.getD 1 Dir.L) +
    3 * dnum3 (D.getD 2 Dir.L))))))))

end URTM.Three
