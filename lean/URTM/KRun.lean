/-
  `KState` の機械（`Machine Q P S`、両側無限テープの `Cfg`）を有限のジッパーで実行する検査器 `check` と、
  その健全性 `halts_of_check`。

  具体的な計算（「初期配置から**ちょうど** n ステップで停止し、停止配置はこれ」）を
  **カーネルの評価**（`decide +kernel`）で照合するための橋。`native_decide` を使わないので、
  信頼の基盤はカーネルだけ（コンパイラ・`implemented_by` を含まない）。

  * `Zip` — 状態・ヘッドより左（近い順）・ヘッドの記号・右。`Zip.cfg bk` で `CTSHSim.zc` に写す
    （位置 0 がテープの左端 = リストの先頭。範囲外は空白 `bk`）。
  * `zstep` — 1 ステップ。左端（位置 0）から左へ出る場合は表せないので `none`（検査が失敗するだけ）。
  * `halted` — 状態が疑似状態か、(状態, 読んだ記号) に一致する規則が無い。
  * `check T n z e` — `zstep` をちょうど n 回適用すると `e` になり、`e` が停止配置である。

  mathlib 非依存。未証明の穴・新規公理・native_decide を使わない。
-/
import URTM.KState
import URTM.CTSHSim

namespace URTM.KState.Run

open URTM URTM.KState URTM.CTSH.Sim

/-- ジッパー: `l` はヘッドより左を近い順、`h` はヘッドの記号、`r` は右側（その先は空白）。 -/
structure Zip (Q P S : Type) where
  st : Tgt Q P
  l : List S
  h : S
  r : List S
  deriving DecidableEq

theorem zr_headD {Q P S : Type} (bk : S) (q : Tgt Q P) (l R : List S) :
    zr bk q l R = zc bk q l (R.headD bk) R.tail := by
  cases R <;> rfl

variable {Q P S : Type} [DecidableEq Q] [DecidableEq P] [DecidableEq S]

/-- ジッパーが表す配置（ヘッド位置は `l.length`）。 -/
def Zip.cfg (bk : S) (z : Zip Q P S) : Cfg Q P S := zc bk z.st z.l z.h z.r

/-- (状態, 読んだ記号) に一致する最初の規則。 -/
def lookup (T : Machine Q P S) (p : Q) (s : S) : Option (Rule Q P S) :=
  T.find? (fun r => decide (r.p = p) && decide (r.s = s))

/-- 1 ステップ。停止配置・左端からの逸脱では `none`。 -/
def zstep (bk : S) (T : Machine Q P S) (z : Zip Q P S) : Option (Zip Q P S) :=
  match z.st with
  | .halt _ => none
  | .go p =>
    match lookup T p z.h with
    | none => none
    | some r =>
      match r.d, z.l with
      | .R, l => some ⟨r.q, r.t :: l, z.r.headD bk, z.r.tail⟩
      | .Z, l => some ⟨r.q, l, r.t, z.r⟩
      | .L, y :: l => some ⟨r.q, l, y, r.t :: z.r⟩
      | .L, [] => none

/-- 停止配置の判定（疑似状態、または一致する規則が無い）。 -/
def halted (T : Machine Q P S) (z : Zip Q P S) : Bool :=
  match z.st with
  | .halt _ => true
  | .go p => (lookup T p z.h).isNone

/-- ちょうど `n` ステップの実行（途中で進めなくなれば `none`）。 -/
def zrun (bk : S) (T : Machine Q P S) : Nat → Zip Q P S → Option (Zip Q P S)
  | 0, z => some z
  | n + 1, z =>
    match zstep bk T z with
    | none => none
    | some z' => zrun bk T n z'

/-- 検査器: `z` から `zstep` をちょうど `n` 回で `e` に達し、`e` は停止配置。 -/
def check (bk : S) (T : Machine Q P S) (n : Nat) (z e : Zip Q P S) : Bool :=
  match zrun bk T n z with
  | none => false
  | some z' => decide (z' = e) && halted T z'

/-- 途中までの検査器: `z` から `zstep` をちょうど `n` 回で `m` に達する（長い実行を分割してカーネルに渡す）。 -/
def reach (bk : S) (T : Machine Q P S) (n : Nat) (z m : Zip Q P S) : Bool :=
  match zrun bk T n z with
  | none => false
  | some z' => decide (z' = m)

/-! ## 健全性 -/

omit [DecidableEq P] in
theorem lookup_some {T : Machine Q P S} {p : Q} {s : S} {r : Rule Q P S}
    (h : lookup T p s = some r) : r ∈ T ∧ r.p = p ∧ r.s = s := by
  unfold lookup at h
  have hm := List.mem_of_find?_eq_some h
  have hp := List.find?_some h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
  exact ⟨hm, hp.1, hp.2⟩

omit [DecidableEq P] in
theorem lookup_none {T : Machine Q P S} {p : Q} {s : S}
    (h : lookup T p s = none) : ∀ r ∈ T, ¬ (r.p = p ∧ r.s = s) := by
  unfold lookup at h
  intro r hr ⟨h1, h2⟩
  have := List.find?_eq_none.1 h r hr
  simp [h1, h2] at this

omit [DecidableEq P] in
theorem zstep_sound {bk : S} {T : Machine Q P S} {z z' : Zip Q P S}
    (h : zstep bk T z = some z') : Step T (z.cfg bk) (z'.cfg bk) := by
  obtain ⟨st, l, hd, rr⟩ := z
  cases st with
  | halt _ => simp [zstep] at h
  | go p =>
    simp only [zstep] at h
    split at h
    · cases h
    · rename_i r hl
      obtain ⟨hmem, hp, hs⟩ := lookup_some hl
      obtain ⟨rp, rs, rt, rd, rq⟩ := r
      simp only at hp hs
      subst hp hs
      cases rd with
      | R =>
        simp only [Option.some.injEq] at h; subst h
        have := stepR' (bk := bk) hmem l rr
        rw [zr_headD] at this
        exact this
      | Z =>
        simp only [Option.some.injEq] at h; subst h
        exact stepZ hmem l rr
      | L =>
        cases l with
        | nil => simp at h
        | cons y l =>
          simp only [Option.some.injEq] at h; subst h
          exact stepL hmem y l rr

omit [DecidableEq P] in
theorem halted_sound {bk : S} {T : Machine Q P S} {z : Zip Q P S}
    (h : halted T z = true) : Halted T (z.cfg bk) := by
  intro c' ⟨r, hr, hst, hs, _⟩
  obtain ⟨st, l, hd, rr⟩ := z
  have hread := zc_read (bk := bk) st l hd rr
  simp only [Zip.cfg] at hst hs
  rw [hread] at hs
  simp only [zc] at hst
  subst hst
  simp only [halted, Option.isNone_iff_eq_none] at h
  exact lookup_none h r hr ⟨rfl, hs.symm⟩

omit [DecidableEq P] in
theorem zrun_sound {bk : S} {T : Machine Q P S} :
    ∀ (n : Nat) {z e : Zip Q P S}, zrun bk T n z = some e → StepN T n (z.cfg bk) (e.cfg bk)
  | 0, z, e, h => by
    simp only [zrun, Option.some.injEq] at h; subst h; exact .refl _
  | n + 1, z, e, h => by
    simp only [zrun] at h
    split at h
    · cases h
    · rename_i z' hz
      exact .cons (zstep_sound hz) (zrun_sound n h)

/-- **健全性**: 検査器が通れば、`z` の表す配置からちょうど `n` ステップで停止配置 `e` に達する。 -/
theorem halts_of_check {bk : S} {T : Machine Q P S} {n : Nat} {z e : Zip Q P S}
    (h : check bk T n z e = true) : HaltsIn T n (z.cfg bk) (e.cfg bk) := by
  simp only [check] at h
  split at h
  · cases h
  · rename_i z' hz
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨rfl, hh⟩ := h
    exact ⟨zrun_sound n hz, halted_sound hh⟩

/-- 分割した実行の合成: 前半を `reach`、残りを停止まで検査したものをつなぐ。 -/
theorem halts_of_reach {bk : S} {T : Machine Q P S} {a b : Nat} {z m e : Zip Q P S}
    (h : reach bk T a z m = true) (h' : HaltsIn T b (m.cfg bk) (e.cfg bk)) :
    HaltsIn T (a + b) (z.cfg bk) (e.cfg bk) := by
  simp only [reach] at h
  split at h
  · cases h
  · rename_i z' hz
    simp only [decide_eq_true_eq] at h
    subst h
    have := (zrun_sound a hz).trans h'.1
    exact ⟨this, h'.2⟩

/-! ## 他の書き方の配置との照合 -/

omit [DecidableEq Q] [DecidableEq P] [DecidableEq S] in
/-- 末尾の空白は `tp` の値を変えない。 -/
theorem tp_pad (bk : S) (L : List S) : ∀ k, CTSH.Sim.tp bk (L ++ List.replicate k bk) = CTSH.Sim.tp bk L
  | 0 => by simp
  | k + 1 => by
    rw [List.replicate_succ', ← List.append_assoc, CTSH.Sim.tp_trail, tp_pad bk L k]

omit [DecidableEq Q] [DecidableEq P] [DecidableEq S] in
/-- 状態・ヘッド位置・テープ（`CTSH.Sim.tp bk L`、末尾の空白の差は問わない）が一致すれば、配置はジッパーの表すものに等しい。
    具体例では前 2 つと `hL` を `decide`、`ht` を `rfl` で閉じる。 -/
theorem cfg_eq_of {bk : S} {c : Cfg Q P S} {z : Zip Q P S} (L : List S) (k : Nat)
    (hst : c.st = z.st) (hpos : c.pos = (z.l.length : Int)) (ht : c.tape = CTSH.Sim.tp bk L)
    (hL : z.l.reverse ++ z.h :: z.r = L ++ List.replicate k bk) : c = z.cfg bk := by
  obtain ⟨st, pos, tape⟩ := c
  simp only at hst hpos ht
  subst hst hpos ht
  simp only [Zip.cfg, zc, hL, tp_pad]

end URTM.KState.Run
