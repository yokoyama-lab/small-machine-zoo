/-
  3 状態 2 記号の URTM（段階 2e の 8）: **群 D のうち、z の右へ動く規則が「源」になる 8 類**
  （class 38, 39, 40, 41, 47, 55, 56, 58、96 表）。**手書き**。

  向き: 開いている側を右にそろえる。状態は z（左へ動いて入る状態）と要求の状態 r1, r2。z の規則は
  L1 = (z, f') → (0, L, z) と、**源の規則** R3 = (z, 1−f') → (1−f', R, s)（読んだ記号をそのまま書く）。
  r1, r2 の規則はセルの動作 `act`（吸収 = 1 を書いて z で戻る、転送 = f' を書いて右へ、停止）で書ける（`CellG`）。
  動作は 3 型（`actQ`・`actR`・`actS`）。Pavlotskaya (1978) §6 の型 III（補題 4 の y1 ≠ y2 の枝）に当たる。

  実行は「初めの訪問（初めの状態が要求なら）→ z の掃引（f' を 0 にしながら左へ、1−f' に会うまで）→ 源」の 3 段。
  源のセル c は R3 のあとも 1−f' のままなので、z で戻るたびに同じ要求 s を出し直す。右は**同じ入力を受け続ける
  カスケード**（`srcIt`）になる。型ごとに、止まる実行では右の中身の長さが高々 2 しか伸びないことを示す
  （`hlenQ`・`hlenR`・`hlenS`）。よって止まる実行のヘッドは [a−1, b+6] に収まり（`bnd_main`）、
  `bound_of_window` で有界停止になる（`halts_iff_boundL`）。左の証明書は使わない。
-/
import URTMMeta.ThreeK

namespace URTM.Meta
open URTM URTM.TwoState URTM.Three

/-! ### 実行の範囲 -/

/-- 実行の先頭 k 歩（時刻 0..k−1）のヘッドが [lo, up] にある。 -/
def VB (tbl : List Quint) (d : QConf) (k : Nat) (lo up : Int) : Prop :=
  ∀ i, i < k → ∀ d', qrun tbl i d = some d' → lo ≤ d'.pos ∧ d'.pos ≤ up

/-- 実行の全体のヘッドが [lo, up] にある。 -/
def AB (tbl : List Quint) (d : QConf) (lo up : Int) : Prop :=
  ∀ i d', qrun tbl i d = some d' → lo ≤ d'.pos ∧ d'.pos ≤ up

theorem VB_zero {tbl : List Quint} {d : QConf} {lo up : Int} : VB tbl d 0 lo up :=
  fun _ hi _ _ => absurd hi (Nat.not_lt_zero _)

theorem VB_one {tbl : List Quint} {st : Nat} {p : Int} {t : Int → Nat} {lo up : Int} (h1 : lo ≤ p) (h2 : p ≤ up) :
    VB tbl ⟨st, p, t⟩ 1 lo up := by
  intro i hi d' hd
  obtain rfl : i = 0 := by omega
  simp only [qrun, Option.some.injEq] at hd; subst hd; exact ⟨h1, h2⟩

theorem VB_mono {tbl : List Quint} {d : QConf} {k : Nat} {lo up lo' up' : Int} (h : VB tbl d k lo up)
    (hl : lo' ≤ lo) (hh : up ≤ up') : VB tbl d k lo' up' := by
  intro i hi d' hd; have := h i hi d' hd; constructor <;> omega

theorem VB_cat {tbl : List Quint} {d e : QConf} {k1 k2 : Nat} {lo up : Int} (h1 : VB tbl d k1 lo up)
    (he : qrun tbl k1 d = some e) (h2 : VB tbl e k2 lo up) : VB tbl d (k1 + k2) lo up := by
  intro i hik d' hd
  rcases Nat.lt_or_ge i k1 with h | h
  · exact h1 i h d' hd
  · obtain ⟨j, rfl⟩ : ∃ j, i = k1 + j := ⟨i - k1, by omega⟩
    rw [qrun_add, he, Option.bind_some] at hd
    exact h2 j (by omega) d' hd

theorem AB_cat {tbl : List Quint} {d e : QConf} {k : Nat} {lo up : Int} (h1 : VB tbl d k lo up)
    (he : qrun tbl k d = some e) (h2 : AB tbl e lo up) : AB tbl d lo up := by
  intro i d' hd
  rcases Nat.lt_or_ge i k with h | h
  · exact h1 i h d' hd
  · obtain ⟨j, rfl⟩ : ∃ j, i = k + j := ⟨i - k, by omega⟩
    rw [qrun_add, he, Option.bind_some] at hd
    exact h2 j d' hd

theorem AB_halt {tbl : List Quint} {d : QConf} {k : Nat} {lo up : Int} (h1 : VB tbl d k lo up)
    (he : qrun tbl k d = none) : AB tbl d lo up := by
  intro i d' hd
  rcases Nat.lt_or_ge i k with h | h
  · exact h1 i h d' hd
  · rw [qrun_none_mono tbl d k i he h] at hd; cases hd

theorem AB_mono {tbl : List Quint} {d : QConf} {lo up lo' up' : Int} (h : AB tbl d lo up)
    (hl : lo' ≤ lo) (hh : up ≤ up') : AB tbl d lo' up' := by
  intro i d' hd; have := h i d' hd; constructor <;> omega

/-- 途中で生きている配置から先も止まる。 -/
theorem run_split {tbl : List Quint} {d e : QConf} {k n : Nat} (h1 : qrun tbl k d = some e)
    (h2 : qrun tbl n d = none) : k < n ∧ qrun tbl (n - k) e = none := by
  have hk : k < n := by
    by_contra hc
    rw [qrun_none_mono tbl d n k h2 (by omega)] at h1; cases h1
  refine ⟨hk, ?_⟩
  rw [show n = k + (n - k) by omega, qrun_add, h1, Option.bind_some] at h2
  exact h2

/-! ### 1 歩 -/

theorem step_R {tbl : List Quint} {st x w st' : Nat} {p : Int} {t : Int → Nat} (hx : t p = x)
    (hf : find? tbl st x = some ⟨st, x, w, Dir.R, st'⟩) :
    qrun tbl 1 ⟨st, p, t⟩ = some ⟨st', p + 1, write t p w⟩ := by
  have hs : qstep tbl ⟨st, p, t⟩ = some ⟨st', p + 1, write t p w⟩ := by
    rw [qstep_of_find (by simp only; rw [hx]; exact hf)]; rfl
  rw [qrun_succ_some tbl 0 hs]; rfl

theorem step_Lm {tbl : List Quint} {st x w st' : Nat} {p : Int} {t : Int → Nat} (hx : t p = x)
    (hf : find? tbl st x = some ⟨st, x, w, Dir.L, st'⟩) :
    qrun tbl 1 ⟨st, p, t⟩ = some ⟨st', p - 1, write t p w⟩ := by
  have hs : qstep tbl ⟨st, p, t⟩ = some ⟨st', p - 1, write t p w⟩ := by
    rw [qstep_of_find (by simp only; rw [hx]; exact hf)]; rfl
  rw [qrun_succ_some tbl 0 hs]; rfl

theorem step_L {tbl : List Quint} {st x w st' : Nat} {p : Int} {t : Int → Nat} (hx : t (p + 1) = x)
    (hf : find? tbl st x = some ⟨st, x, w, Dir.L, st'⟩) :
    qrun tbl 1 ⟨st, p + 1, t⟩ = some ⟨st', p, write t (p + 1) w⟩ := by
  have := step_Lm hx hf
  rw [show p + 1 - 1 = p by omega] at this
  exact this

theorem step_none {tbl : List Quint} {st x : Nat} {p : Int} {t : Int → Nat} (hx : t p = x)
    (hf : find? tbl st x = none) : qrun tbl 1 ⟨st, p, t⟩ = none :=
  qrun_succ_none tbl 0 (qstep_none_of_find (by simp only; rw [hx]; exact hf))

/-! ### 右の中身 -/

/-- 中身はいつも 0 か 1。 -/
def Bin (cs : List Nat) : Prop := ∀ k, cs.getD k 0 < 2

/-- b より右の中身が列 cs を表す（セル b+1+k は cs の k 番目、先は 0）。 -/
def RepQ (b : Int) (t : Int → Nat) (cs : List Nat) : Prop := ∀ k : Nat, t (b + 1 + k) = cs.getD k 0

theorem RepQ.head {b : Int} {t : Int → Nat} {x : Nat} {cs : List Nat} (h : RepQ b t (x :: cs)) :
    t (b + 1) = x := by
  have := h 0
  rw [List.getD_cons_zero] at this
  rw [← this]; congr 1; omega

theorem RepQ.zero {b : Int} {t : Int → Nat} (h : RepQ b t []) : ∀ x, b + 1 ≤ x → t x = 0 := by
  intro x hx
  have := h (x - (b + 1)).toNat
  rw [show b + 1 + ((x - (b + 1)).toNat : Int) = x by omega, List.getD_nil] at this
  exact this

theorem RepQ.of_zero {b : Int} {t : Int → Nat} (h : ∀ x, b + 1 ≤ x → t x = 0) : RepQ b t [] := by
  intro k; rw [List.getD_nil]; exact h _ (by omega)

theorem RepQ.shift {b : Int} {t : Int → Nat} {x : Nat} {cs : List Nat} (h : RepQ b t (x :: cs)) :
    RepQ (b + 1) t cs := by
  intro k
  have := h (k + 1)
  rw [List.getD_cons_succ] at this
  rw [← this]; congr 1; push_cast; omega

theorem RepQ.write_le {b : Int} {t : Int → Nat} {cs : List Nat} (h : RepQ b t cs) {p : Int} (hp : p ≤ b)
    (v : Nat) : RepQ b (write t p v) cs := by
  intro k; rw [write_off _ _ _ (by omega)]; exact h k

theorem RepQ.cons {b : Int} {t : Int → Nat} {cs : List Nat} (h : RepQ (b + 1) t cs) (v : Nat) :
    RepQ b (write t (b + 1) v) (v :: cs) := by
  intro k
  cases k with
  | zero =>
    rw [List.getD_cons_zero]
    simp [write]
  | succ k =>
    rw [write_off _ _ _ (by omega), List.getD_cons_succ, ← h k]
    congr 1; push_cast; omega

/-- 長さ n の列（k 番目は f k）。 -/
def listOf (f : Nat → Nat) : Nat → List Nat
  | 0 => []
  | n + 1 => f 0 :: listOf (fun i => f (i + 1)) n

theorem listOf_length : ∀ (f : Nat → Nat) (n : Nat), (listOf f n).length = n
  | _, 0 => rfl
  | f, n + 1 => by simp only [listOf, List.length_cons, listOf_length _ n]

theorem listOf_getD : ∀ (f : Nat → Nat) (n i : Nat), (listOf f n).getD i 0 = if i < n then f i else 0
  | _, 0, i => by rw [listOf, List.getD_nil, if_neg (show ¬ (i < 0) by omega)]
  | f, n + 1, 0 => by rw [listOf, List.getD_cons_zero, if_pos (show 0 < n + 1 by omega)]
  | f, n + 1, i + 1 => by
    rw [listOf, List.getD_cons_succ, listOf_getD _ n i]
    by_cases h : i < n
    · rw [if_pos h, if_pos (show i + 1 < n + 1 by omega)]
    · rw [if_neg h, if_neg (show ¬ (i + 1 < n + 1) by omega)]

/-! ### セルの動作とカスケード -/

/-- セルの動作: 吸収（1 を書いて z で戻る）、転送（f' を書いて右へ、要求 a'）、停止。 -/
inductive CAct where
  | ab
  | fw (a : Bool)
  | ht
  deriving DecidableEq

/-- 訪問の結果: 戻る（右の中身 cs）、止まる、戻らずに右へ走り続ける。 -/
inductive COut where
  | ret (cs : List Nat)
  | halt
  | div
  deriving DecidableEq

/-- 転送したセルの結果（戻れば先頭に 0 が付く）。 -/
def COut.cons0 : COut → COut
  | .ret cs => .ret (0 :: cs)
  | .halt => .halt
  | .div => .div

theorem cons0_eq_ret {o : COut} {cs : List Nat} (h : o.cons0 = .ret cs) : ∃ cs', o = .ret cs' ∧ cs = 0 :: cs' := by
  cases o with
  | ret cs' => simp only [COut.cons0, COut.ret.injEq] at h; exact ⟨cs', rfl, h.symm⟩
  | halt => simp [COut.cons0] at h
  | div => simp [COut.cons0] at h

theorem cons0_eq_halt {o : COut} (h : o.cons0 = .halt) : o = .halt := by
  cases o <;> simp_all [COut.cons0]

/-- 空白の上の 2 段目（要求 a で空白のセルに入る）。 -/
def cgB1 (act : Bool → Nat → CAct) (a : Bool) : COut :=
  match act a 0 with
  | .ab => .ret [1]
  | .ht => .halt
  | .fw _ => .div

/-- 空白のカスケードに要求 a を送った結果。転送が 2 段続けば状態が繰り返すので走り続ける。 -/
def cgB (act : Bool → Nat → CAct) (a : Bool) : COut :=
  match act a 0 with
  | .ab => .ret [1]
  | .ht => .halt
  | .fw a' => if a' = a then .div else (cgB1 act a').cons0

/-- 中身の列 cs のカスケードに要求 a を 1 つ送った結果。 -/
def cg (act : Bool → Nat → CAct) : List Nat → Bool → COut
  | [], a => cgB act a
  | x :: cs, a =>
    match act a x with
    | .ab => .ret (1 :: cs)
    | .ht => .halt
    | .fw a' => (cg act cs a').cons0

/-- 源が同じ要求 s を n 回送った結果。 -/
def srcIt (act : Bool → Nat → CAct) (s : Bool) : List Nat → Nat → COut
  | cs, 0 => .ret cs
  | cs, n + 1 =>
    match cg act cs s with
    | .ret cs' => srcIt act s cs' n
    | .halt => .halt
    | .div => .div

theorem cg_len {act : Bool → Nat → CAct} : ∀ {cs : List Nat} {a : Bool} {cs' : List Nat},
    cg act cs a = .ret cs' → cs'.length ≤ cs.length + 2
  | [], a, cs', h => by
    simp only [cg, cgB] at h
    split at h
    · simp only [COut.ret.injEq] at h; subst h; simp
    · cases h
    · split at h
      · cases h
      · obtain ⟨c1, h1, rfl⟩ := cons0_eq_ret h
        simp only [cgB1] at h1
        split at h1
        · simp only [COut.ret.injEq] at h1; subst h1; simp
        · cases h1
        · cases h1
  | x :: cs, a, cs', h => by
    simp only [cg] at h
    split at h
    · simp only [COut.ret.injEq] at h; subst h; simp
    · cases h
    · obtain ⟨c1, h1, rfl⟩ := cons0_eq_ret h
      have := cg_len h1
      simp only [List.length_cons]; omega

theorem cg_bin {act : Bool → Nat → CAct} : ∀ {cs : List Nat} {a : Bool} {cs' : List Nat},
    Bin cs → cg act cs a = .ret cs' → Bin cs'
  | [], a, cs', _, h => by
    simp only [cg, cgB] at h
    split at h
    · simp only [COut.ret.injEq] at h; subst h
      intro k; rcases k with _ | k <;> simp
    · cases h
    · split at h
      · cases h
      · obtain ⟨c1, h1, rfl⟩ := cons0_eq_ret h
        simp only [cgB1] at h1
        split at h1
        · simp only [COut.ret.injEq] at h1; subst h1
          intro k; rcases k with _ | _ | k <;> simp
        · cases h1
        · cases h1
  | x :: cs, a, cs', hb, h => by
    have hbs : Bin cs := fun k => by have := hb (k + 1); rwa [List.getD_cons_succ] at this
    simp only [cg] at h
    split at h
    · simp only [COut.ret.injEq] at h; subst h
      intro k; cases k with
      | zero => simp
      | succ k => rw [List.getD_cons_succ]; exact hbs k
    · cases h
    · obtain ⟨c1, h1, rfl⟩ := cons0_eq_ret h
      have := cg_bin hbs h1
      intro k; cases k with
      | zero => simp
      | succ k => rw [List.getD_cons_succ]; exact this k

/-! ### セルの規則と訪問 -/

/-- 動作から決まる r1, r2 の規則。 -/
def cellRule (z r1 r2 f' : Nat) (a : Bool) (x : Nat) : CAct → Option Quint
  | .ab => some ⟨sP r1 r2 a, x, 1, Dir.L, z⟩
  | .fw a' => some ⟨sP r1 r2 a, x, f', Dir.R, sP r1 r2 a'⟩
  | .ht => none

/-- 右側のセルの規則（動作 act による）と、z が f' の上で左へ戻る規則。 -/
structure CellG (tbl : List Quint) (z r1 r2 f' : Nat) (act : Bool → Nat → CAct) : Prop where
  hc : ∀ (a : Bool) (x : Nat), x < 2 → find? tbl (sP r1 r2 a) x = cellRule z r1 r2 f' a x (act a x)
  hZ : find? tbl z f' = some ⟨z, f', 0, Dir.L, z⟩

/-- 訪問の仕様: 結果 o に応じて、z で b に戻る・止まる・走り続ける（訪問中のヘッドは [b+1, up]）。 -/
def VSpec (tbl : List Quint) (z : Nat) (b : Int) (t : Int → Nat) (d : QConf) (up : Int) : COut → Prop
  | .ret cs' => ∃ k t', VB tbl d k (b + 1) up ∧ qrun tbl k d = some ⟨z, b, t'⟩ ∧
      (∀ x, x ≤ b → t' x = t x) ∧ RepQ b t' cs'
  | .halt => ∃ k, VB tbl d k (b + 1) up ∧ qrun tbl k d = none
  | .div => ∀ n, qrun tbl n d ≠ none

theorem VSpec.mono {tbl : List Quint} {z : Nat} {b : Int} {t : Int → Nat} {d : QConf} {up up' : Int}
    (h : up ≤ up') : ∀ {o : COut}, VSpec tbl z b t d up o → VSpec tbl z b t d up' o
  | .ret _, ⟨k, t', hv, hr, ha, hrep⟩ => ⟨k, t', VB_mono hv le_rfl h, hr, ha, hrep⟩
  | .halt, ⟨k, hv, hr⟩ => ⟨k, VB_mono hv le_rfl h, hr⟩
  | .div, hd => hd

theorem bool_two {a a' a'' : Bool} (h : a' ≠ a) : a'' = a ∨ a'' = a' := by
  revert h; revert a a' a''; decide

section visitPieces
variable {tbl : List Quint} {z f' : Nat}

/-- 吸収: 1 を書いて z で b に戻る。 -/
theorem vspec_ab' {st x : Nat} {b : Int} {t : Int → Nat} {rest : List Nat} (hx : t (b + 1) = x)
    (hf : find? tbl st x = some ⟨st, x, 1, Dir.L, z⟩) (hrest : RepQ (b + 1) t rest) {up : Int} (hup : b + 1 ≤ up) :
    VSpec tbl z b t ⟨st, b + 1, t⟩ up (.ret (1 :: rest)) :=
  ⟨1, write t (b + 1) 1, VB_one le_rfl hup, step_L hx hf, fun y hy => write_off _ _ _ (by omega),
    RepQ.cons hrest 1⟩

/-- 規則が無い: その場で止まる。 -/
theorem vspec_ht' {st x : Nat} {b : Int} {t : Int → Nat} (hx : t (b + 1) = x) (hf : find? tbl st x = none)
    {up : Int} (hup : b + 1 ≤ up) : VSpec tbl z b t ⟨st, b + 1, t⟩ up .halt :=
  ⟨1, VB_one le_rfl hup, step_none hx hf⟩

/-- 転送: f' を書いて右の訪問へ。戻れば z が f' を読んで 0 を書き、b に戻る。 -/
theorem vspec_fwd' (hZ : find? tbl z f' = some ⟨z, f', 0, Dir.L, z⟩) {st st' x : Nat} {b : Int} {t : Int → Nat}
    (hx : t (b + 1) = x) (hf : find? tbl st x = some ⟨st, x, f', Dir.R, st'⟩) {up : Int} (hup : b + 1 ≤ up)
    {o : COut} (hin : VSpec tbl z (b + 1) (write t (b + 1) f') ⟨st', b + 1 + 1, write t (b + 1) f'⟩ up o) :
    VSpec tbl z b t ⟨st, b + 1, t⟩ up o.cons0 := by
  have e1 : qrun tbl 1 ⟨st, b + 1, t⟩ = some ⟨st', b + 1 + 1, write t (b + 1) f'⟩ := step_R hx hf
  cases o with
  | ret cs'' =>
    obtain ⟨k1, t2, hv, hr, hag, hrep⟩ := hin
    have ht2 : t2 (b + 1) = f' := by rw [hag _ le_rfl]; simp [write]
    have e2 : qrun tbl 1 ⟨z, b + 1, t2⟩ = some ⟨z, b, write t2 (b + 1) 0⟩ := step_L ht2 hZ
    refine ⟨1 + (k1 + 1), write t2 (b + 1) 0, ?_, ?_, ?_, RepQ.cons hrep 0⟩
    · exact VB_cat (VB_one le_rfl hup) e1 (VB_cat (VB_mono hv (by omega) le_rfl) hr (VB_one le_rfl hup))
    · rw [qrun_add, e1, Option.bind_some, qrun_add, hr, Option.bind_some, e2]
    · intro y hy
      rw [write_off _ _ _ (by omega), hag y (by omega), write_off _ _ _ (by omega)]
  | halt =>
    obtain ⟨k1, hv, hr⟩ := hin
    refine ⟨1 + k1, VB_cat (VB_one le_rfl hup) e1 (VB_mono hv (by omega) le_rfl), ?_⟩
    rw [qrun_add, e1, Option.bind_some, hr]
  | div =>
    intro n
    cases n with
    | zero => simp [qrun]
    | succ n =>
      rw [show n + 1 = 1 + n by omega, qrun_add, e1, Option.bind_some]
      exact hin n

/-- 前置き: k 歩（ヘッドは [b+1, up]、b 以下のテープは変えない）で d' に着くなら、d' の仕様は d の仕様。 -/
theorem vspec_pre {b : Int} {t t' : Int → Nat} {d d' : QConf} {k : Nat} {up : Int} (hrun : qrun tbl k d = some d')
    (hvb : VB tbl d k (b + 1) up) (hag : ∀ x, x ≤ b → t' x = t x) {o : COut} (h : VSpec tbl z b t' d' up o) :
    VSpec tbl z b t d up o := by
  cases o with
  | ret cs =>
    obtain ⟨k2, t2, hv2, hr2, hag2, hrep⟩ := h
    exact ⟨k + k2, t2, VB_cat hvb hrun hv2, by rw [qrun_add, hrun, Option.bind_some, hr2],
      fun x hx => by rw [hag2 x hx, hag x hx], hrep⟩
  | halt =>
    obtain ⟨k2, hv2, hr2⟩ := h
    exact ⟨k + k2, VB_cat hvb hrun hv2, by rw [qrun_add, hrun, Option.bind_some, hr2]⟩
  | div =>
    intro n hn
    rcases Nat.lt_or_ge n k with hlt | hge
    · rw [qrun_none_mono tbl d n k hn (by omega)] at hrun; cases hrun
    · rw [show n = k + (n - k) by omega, qrun_add, hrun, Option.bind_some] at hn
      exact h (n - k) hn

end visitPieces

section visitG
variable {tbl : List Quint} {z r1 r2 f' : Nat} {act : Bool → Nat → CAct} (H : CellG tbl z r1 r2 f' act)
include H

/-- 空白の上で転送が続く（状態の集合 S が転送で閉じる）なら、止まらない。 -/
theorem blank_div {S : Bool → Prop} (hS : ∀ a, S a → ∃ a', act a 0 = .fw a' ∧ S a') :
    ∀ (n : Nat) (a : Bool) (p : Int) (t : Int → Nat), S a → (∀ x, p ≤ x → t x = 0) →
      qrun tbl n ⟨sP r1 r2 a, p, t⟩ ≠ none := by
  intro n
  induction n with
  | zero => intro a p t _ _; simp [qrun]
  | succ n ih =>
    intro a p t ha hz
    obtain ⟨a', hact, ha'⟩ := hS a ha
    have hf : find? tbl (sP r1 r2 a) 0 = some ⟨sP r1 r2 a, 0, f', Dir.R, sP r1 r2 a'⟩ := by
      rw [H.hc a 0 (by decide), hact]; rfl
    rw [show n + 1 = 1 + n by omega, qrun_add, step_R (hz p le_rfl) hf, Option.bind_some]
    exact ih a' (p + 1) _ ha' (fun x hx => by rw [write_off _ _ _ (by omega)]; exact hz x (by omega))

theorem vspec_ab {a : Bool} {x : Nat} {b : Int} {t : Int → Nat} {rest : List Nat} (hx : t (b + 1) = x)
    (hx2 : x < 2) (hA : act a x = .ab) (hrest : RepQ (b + 1) t rest) {up : Int} (hup : b + 1 ≤ up) :
    VSpec tbl z b t ⟨sP r1 r2 a, b + 1, t⟩ up (.ret (1 :: rest)) := by
  have hf : find? tbl (sP r1 r2 a) x = some ⟨sP r1 r2 a, x, 1, Dir.L, z⟩ := by rw [H.hc a x hx2, hA]; rfl
  exact vspec_ab' hx hf hrest hup

theorem vspec_ht {a : Bool} {x : Nat} {b : Int} {t : Int → Nat} (hx : t (b + 1) = x) (hx2 : x < 2)
    (hA : act a x = .ht) {up : Int} (hup : b + 1 ≤ up) :
    VSpec tbl z b t ⟨sP r1 r2 a, b + 1, t⟩ up .halt := by
  have hf : find? tbl (sP r1 r2 a) x = none := by rw [H.hc a x hx2, hA]; rfl
  exact vspec_ht' hx hf hup

theorem vspec_fwd {a a' : Bool} {x : Nat} {b : Int} {t : Int → Nat} (hx : t (b + 1) = x) (hx2 : x < 2)
    (hA : act a x = .fw a') {up : Int} (hup : b + 1 ≤ up) {o : COut}
    (hin : VSpec tbl z (b + 1) (write t (b + 1) f') ⟨sP r1 r2 a', b + 1 + 1, write t (b + 1) f'⟩ up o) :
    VSpec tbl z b t ⟨sP r1 r2 a, b + 1, t⟩ up o.cons0 := by
  have hf : find? tbl (sP r1 r2 a) x = some ⟨sP r1 r2 a, x, f', Dir.R, sP r1 r2 a'⟩ := by
    rw [H.hc a x hx2, hA]; rfl
  exact vspec_fwd' H.hZ hx hf hup hin

/-- **カスケードの訪問**: 右の中身が cs を表すとき、要求 a で b+1 に入った訪問の結果は `cg act cs a`。
    訪問中のヘッドは b+1 から b+2+|cs|。 -/
theorem visitG : ∀ (cs : List Nat) (b : Int) (t : Int → Nat), Bin cs → RepQ b t cs → ∀ a : Bool,
    VSpec tbl z b t ⟨sP r1 r2 a, b + 1, t⟩ (b + 2 + cs.length) (cg act cs a) := by
  intro cs
  induction cs with
  | nil =>
    intro b t _ hr a
    have hz := hr.zero
    have h0 : t (b + 1) = 0 := hz _ le_rfl
    have hup : b + 1 ≤ b + 2 + (([] : List Nat).length : Int) := by simp
    show VSpec tbl z b t _ _ (cgB act a)
    unfold cgB
    cases hA : act a 0 with
    | ab => exact vspec_ab H h0 (by decide) hA (RepQ.of_zero (fun x hx => hz x (by omega))) hup
    | ht => exact vspec_ht H h0 (by decide) hA hup
    | fw a' =>
      by_cases haa : a' = a
      · show VSpec tbl z b t _ _ (if a' = a then COut.div else (cgB1 act a').cons0)
        rw [if_pos haa]
        intro n
        exact blank_div H (S := fun y => y = a) (fun y hy => by subst hy; exact ⟨a', hA, haa⟩) n a (b + 1) t rfl hz
      · show VSpec tbl z b t _ _ (if a' = a then COut.div else (cgB1 act a').cons0)
        rw [if_neg haa]
        apply vspec_fwd H h0 (by decide) hA hup
        have hz' : ∀ x, b + 1 + 1 ≤ x → write t (b + 1) f' x = 0 := fun x hx => by
          rw [write_off _ _ _ (by omega)]; exact hz x (by omega)
        have h0' : write t (b + 1) f' (b + 1 + 1) = 0 := hz' _ le_rfl
        have hup' : b + 1 + 1 ≤ b + 2 + (([] : List Nat).length : Int) := by simp; omega
        unfold cgB1
        cases hB : act a' 0 with
        | ab => exact vspec_ab H h0' (by decide) hB (RepQ.of_zero (fun x hx => hz' x (by omega))) hup'
        | ht => exact vspec_ht H h0' (by decide) hB hup'
        | fw a'' =>
          intro n
          refine blank_div H (S := fun y => y = a ∨ y = a') ?_ n a' _ _ (Or.inr rfl) hz'
          intro y hy
          rcases hy with rfl | rfl
          · exact ⟨a', hA, Or.inr rfl⟩
          · exact ⟨a'', hB, bool_two haa⟩
  | cons x cs ih =>
    intro b t hb hr a
    have hx := hr.head
    have hx2 : x < 2 := by have := hb 0; rwa [List.getD_cons_zero] at this
    have hbs : Bin cs := fun k => by have := hb (k + 1); rwa [List.getD_cons_succ] at this
    have hup : b + 1 ≤ b + 2 + ((x :: cs).length : Int) := by simp; omega
    cases hA : act a x with
    | ab =>
      have hc : cg act (x :: cs) a = .ret (1 :: cs) := by simp only [cg, hA]
      rw [hc]; exact vspec_ab H hx hx2 hA hr.shift hup
    | ht =>
      have hc : cg act (x :: cs) a = .halt := by simp only [cg, hA]
      rw [hc]; exact vspec_ht H hx hx2 hA hup
    | fw a' =>
      have hc : cg act (x :: cs) a = (cg act cs a').cons0 := by simp only [cg, hA]
      rw [hc]
      apply vspec_fwd H hx hx2 hA hup
      have := ih (b + 1) (write t (b + 1) f') hbs (hr.shift.write_le le_rfl f') a'
      refine VSpec.mono ?_ this
      simp only [List.length_cons]; push_cast; omega

end visitG

/-! ### 源と掃引 -/

section sweep
variable {tbl : List Quint} {z f' : Nat} (hZ : find? tbl z f' = some ⟨z, f', 0, Dir.L, z⟩)
include hZ

/-- **掃引**: z が y に居れば、f' の上を 0 にしながら左へ進み、1−f' のセル c に着く（止まる実行なら必ず着く）。 -/
theorem sweep_run (hf2 : f' < 2) : ∀ (n : Nat) (y : Int) (t : Int → Nat), (∀ x, t x < 2) →
    qrun tbl n ⟨z, y, t⟩ = none →
    ∃ c k t', c ≤ y ∧ qrun tbl k ⟨z, y, t⟩ = some ⟨z, c, t'⟩ ∧ VB tbl ⟨z, y, t⟩ k c y ∧ t c = 1 - f' ∧
      (∀ x, c < x → x ≤ y → t x = f') ∧ (∀ x, c < x → x ≤ y → t' x = 0) ∧
      (∀ x, (x ≤ c ∨ y < x) → t' x = t x) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro y t h2 hn
  by_cases hy : t y = f'
  · have e1 : qrun tbl 1 ⟨z, y, t⟩ = some ⟨z, y - 1, write t y 0⟩ := step_Lm hy hZ
    obtain ⟨hlt, hn'⟩ := run_split e1 hn
    have h2' : ∀ x, write t y 0 x < 2 := fun x => by
      unfold write
      by_cases h : x = y
      · rw [if_pos h]; omega
      · rw [if_neg h]; exact h2 x
    obtain ⟨c, k, t', hcy, hrun, hvb, hc, hfx, hzero, hag⟩ := ih (n - 1) (by omega) (y - 1) _ h2' hn'
    have hcy' : c ≠ y := by omega
    refine ⟨c, 1 + k, t', by omega, by rw [qrun_add, e1, Option.bind_some, hrun], ?_, ?_, ?_, ?_, ?_⟩
    · exact VB_cat (VB_one (by omega) le_rfl) e1 (VB_mono hvb le_rfl (by omega))
    · rw [write_off _ _ _ hcy'] at hc; exact hc
    · intro x h1 h2x
      by_cases hxy : x = y
      · rw [hxy]; exact hy
      · have := hfx x h1 (by omega); rw [write_off _ _ _ hxy] at this; exact this
    · intro x h1 h2x
      by_cases hxy : x = y
      · rw [hag x (Or.inr (by omega)), hxy]; simp [write]
      · exact hzero x h1 (by omega)
    · intro x hx
      rw [hag x (by omega), write_off _ _ _ (by omega)]
  · have hy' : t y = 1 - f' := by have := h2 y; omega
    exact ⟨y, 0, t, le_rfl, rfl, VB_zero, hy', fun x h1 h2x => absurd h2x (by omega),
      fun x h1 h2x => absurd h2x (by omega), fun x _ => rfl⟩

end sweep

section srcRun
variable {tbl : List Quint} {z r1 r2 f' : Nat} {act : Bool → Nat → CAct} {s : Bool}
  (H : CellG tbl z r1 r2 f' act)
  (hS : find? tbl z (1 - f') = some ⟨z, 1 - f', 1 - f', Dir.R, sP r1 r2 s⟩)
include H hS

/-- **源**: z が 1−f' のセル c に居て右の中身が cs なら、止まる実行では源の列 `srcIt` が止まり、
    ヘッドは c から c + 2 + （途中の中身の長さの上界）までにある。 -/
theorem src_run : ∀ (n : Nat) (cs : List Nat) (c : Int) (t : Int → Nat), t c = 1 - f' → RepQ c t cs → Bin cs →
    qrun tbl n ⟨z, c, t⟩ = none →
    (∃ N, srcIt act s cs N = .halt) ∧
    ∀ L : Nat, (∀ m cs', srcIt act s cs m = .ret cs' → cs'.length ≤ L) → AB tbl ⟨z, c, t⟩ c (c + 2 + L) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro cs c t hc hr hb hn
  have hw : write t c (1 - f') = t := by
    funext x; unfold write
    by_cases h : x = c
    · rw [if_pos h, h, hc]
    · rw [if_neg h]
  have e0 : qrun tbl 1 ⟨z, c, t⟩ = some ⟨sP r1 r2 s, c + 1, t⟩ := by
    have := step_R (tbl := tbl) hc hS
    rw [hw] at this; exact this
  have hv := visitG H cs c t hb hr s
  cases ho : cg act cs s with
  | ret cs' =>
    rw [ho] at hv
    obtain ⟨k, t', hvb, hrun, hag, hrep⟩ := hv
    have e1 : qrun tbl (1 + k) ⟨z, c, t⟩ = some ⟨z, c, t'⟩ := by
      rw [qrun_add, e0, Option.bind_some, hrun]
    obtain ⟨hlt, hn'⟩ := run_split e1 hn
    have hc' : t' c = 1 - f' := by rw [hag c le_rfl, hc]
    obtain ⟨⟨N, hN⟩, hab⟩ := ih (n - (1 + k)) (by omega) cs' c t' hc' hrep (cg_bin hb ho) hn'
    refine ⟨⟨N + 1, by simp only [srcIt, ho, hN]⟩, fun L hL => ?_⟩
    have hL0 : cs.length ≤ L := hL 0 cs rfl
    have hL' : ∀ m cs'', srcIt act s cs' m = .ret cs'' → cs''.length ≤ L :=
      fun m cs'' h => hL (m + 1) cs'' (by simp only [srcIt, ho, h])
    exact AB_cat (VB_cat (VB_one le_rfl (by omega)) e0 (VB_mono hvb (by omega) (by omega))) e1 (hab L hL')
  | halt =>
    rw [ho] at hv
    obtain ⟨k, hvb, hrun⟩ := hv
    refine ⟨⟨1, by simp only [srcIt, ho]⟩, fun L hL => ?_⟩
    have hL0 : cs.length ≤ L := hL 0 cs rfl
    exact AB_halt (VB_cat (VB_one le_rfl (by omega)) e0 (VB_mono hvb (by omega) (by omega)))
      (by rw [qrun_add, e0, Option.bind_some, hrun])
  | div =>
    rw [ho] at hv
    exfalso
    cases n with
    | zero => simp [qrun] at hn
    | succ n =>
      rw [show n + 1 = 1 + n by omega, qrun_add, e0, Option.bind_some] at hn
      exact hv n hn

/-- 止まる実行で、右の中身の長さが高々 2 しか伸びない（型ごとに示す）。 -/
def HLen (act : Bool → Nat → CAct) (s : Bool) : Prop :=
  ∀ cs, Bin cs → (∃ N, srcIt act s cs N = .halt) → ∀ m cs', srcIt act s cs m = .ret cs' →
    cs'.length ≤ cs.length + 2

/-- **z から**: 窓の左端より 1 つ左から b までに z が居て、中身が [a, b+2] の外で 0 なら、止まる実行のヘッドは
    [a−1, b+6] にある。 -/
theorem from_z (hf2 : f' < 2) (hlen : HLen act s) (a b y : Int) (t : Int → Nat) (hy1 : a - 1 ≤ y) (hy2 : y ≤ b)
    (h2 : ∀ x, t x < 2) (hlo : ∀ x, x < a → t x = 0) (hhi : ∀ x, b + 2 < x → t x = 0)
    (n : Nat) (hn : qrun tbl n ⟨z, y, t⟩ = none) : AB tbl ⟨z, y, t⟩ (a - 1) (b + 6) := by
  obtain ⟨c, k, t', hcy, hrun, hvb, hc, hfx, hzero, hag⟩ := sweep_run H.hZ hf2 n y t h2 hn
  have hca : a - 1 ≤ c := by
    by_contra hlt
    rcases (by omega : f' = 0 ∨ f' = 1) with h0 | h1
    · rw [hlo c (by omega), h0] at hc; omega
    · have := hfx (a - 1) (by omega) hy1
      rw [hlo (a - 1) (by omega), h1] at this; omega
  obtain ⟨_, hn'⟩ := run_split hrun hn
  have h2' : ∀ x, t' x < 2 := by
    intro x
    by_cases hx : x ≤ c ∨ y < x
    · rw [hag x hx]; exact h2 x
    · rw [hzero x (by omega) (by omega)]; omega
  obtain ⟨len, hlen_def⟩ : ∃ len : Nat, (len : Int) = b + 2 - c := ⟨(b + 2 - c).toNat, by omega⟩
  have hrep : RepQ c t' (listOf (fun i => t' (c + 1 + i)) len) := by
    intro i
    rw [listOf_getD]
    by_cases hi : i < len
    · rw [if_pos hi]
    · rw [if_neg hi, hag _ (Or.inr (by omega))]
      exact hhi _ (by omega)
  have hbin : Bin (listOf (fun i => t' (c + 1 + i)) len) := by
    intro i
    rw [listOf_getD]
    by_cases hi : i < len
    · rw [if_pos hi]; exact h2' _
    · rw [if_neg hi]; omega
  have ht'c : t' c = 1 - f' := by rw [hag c (Or.inl le_rfl), hc]
  obtain ⟨hhalt, hab⟩ := src_run H hS _ _ c t' ht'c hrep hbin hn'
  have hab' := hab (len + 2) (fun m cs' h => by
    have := hlen _ hbin hhalt m cs' h
    rw [listOf_length] at this; exact this)
  exact AB_cat (VB_mono hvb hca (by omega)) hrun (AB_mono hab' hca (by omega))

/-- **止まる実行は [a−1, b+6] に収まる**（初めの状態で場合を分ける）。 -/
theorem bnd_main (hf2 : f' < 2) (hlen : HLen act s) (hperm : ∀ q, q < 3 → q = z ∨ q = r1 ∨ q = r2)
    (hsrc : Src3 tbl) (c0 : QConf) (a b : Int) (ha : a ≤ c0.pos) (hb : c0.pos ≤ b)
    (hz : ∀ x, (x < a ∨ b < x) → c0.tape x = 0) (h2 : ∀ x, c0.tape x < 2) (n : Nat)
    (hn : qrun tbl n c0 = none) : AB tbl c0 (a - 1) (b + 6) := by
  obtain ⟨q, p, t⟩ := c0
  simp only at ha hb hz h2
  -- 要求の状態から始まるとき: 1 回の訪問のあと z で p−1 に居る
  have hvis : ∀ aa : Bool, qrun tbl n ⟨sP r1 r2 aa, p, t⟩ = none → AB tbl ⟨sP r1 r2 aa, p, t⟩ (a - 1) (b + 6) := by
    intro aa hn
    obtain ⟨len, hl⟩ : ∃ len : Nat, (len : Int) = b - p + 1 := ⟨(b - p + 1).toNat, by omega⟩
    have hrep : RepQ (p - 1) t (listOf (fun i => t (p + i)) len) := by
      intro i
      rw [listOf_getD]
      by_cases hi : i < len
      · rw [if_pos hi]; congr 1; omega
      · rw [if_neg hi]; exact hz _ (Or.inr (by omega))
    have hbin : Bin (listOf (fun i => t (p + i)) len) := by
      intro i
      rw [listOf_getD]
      by_cases hi : i < len
      · rw [if_pos hi]; exact h2 _
      · rw [if_neg hi]; omega
    have hv := visitG H _ (p - 1) t hbin hrep aa
    rw [show p - 1 + 1 = p by omega, listOf_length] at hv
    cases ho : cg act (listOf (fun i => t (p + i)) len) aa with
    | ret cs' =>
      rw [ho] at hv
      obtain ⟨k, t1, hvb, hrun, hag, hrep'⟩ := hv
      obtain ⟨_, hn'⟩ := run_split hrun hn
      have hl' := cg_len ho
      rw [listOf_length] at hl'
      have hb' := cg_bin hbin ho
      have h21 : ∀ x, t1 x < 2 := by
        intro x
        by_cases hx : x ≤ p - 1
        · rw [hag x hx]; exact h2 x
        · have := hrep' (x - (p - 1 + 1)).toNat
          rw [show p - 1 + 1 + ((x - (p - 1 + 1)).toNat : Int) = x by omega] at this
          rw [this]; exact hb' _
      have hab := from_z H hS hf2 hlen a b (p - 1) t1 (by omega) (by omega) h21
        (fun x hx => by rw [hag x (by omega)]; exact hz x (Or.inl hx))
        (fun x hx => by
          have := hrep' (x - (p - 1 + 1)).toNat
          rw [show p - 1 + 1 + ((x - (p - 1 + 1)).toNat : Int) = x by omega] at this
          rw [this, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl) _ hn'
      exact AB_cat (VB_mono hvb (by omega) (by omega)) hrun hab
    | halt =>
      rw [ho] at hv
      obtain ⟨k, hvb, hrun⟩ := hv
      exact AB_halt (VB_mono hvb (by omega) (by omega)) hrun
    | div =>
      rw [ho] at hv
      exact absurd hn (hv n)
  by_cases hq3 : q < 3
  · rcases hperm q hq3 with rfl | rfl | rfl
    · exact from_z H hS hf2 hlen a b p t (by omega) hb h2 (fun x hx => hz x (Or.inl hx))
        (fun x hx => hz x (Or.inr (by omega))) n hn
    · exact hvis true hn
    · exact hvis false hn
  · have hf : ∀ x, find? tbl q x = none := by
      intro x
      cases h : find? tbl q x with
      | none => rfl
      | some r =>
        obtain ⟨hr, hp, _⟩ := find?_spec h
        exact absurd (hp ▸ hsrc r hr) hq3
    exact AB_halt (VB_one (lo := a - 1) (up := b + 6) (by omega) (by omega)) (step_none rfl (hf (t p)))

end srcRun

/-- **有界停止**（源のある型 III の表。左右の上界は 1 と 6）。 -/
theorem halts_iff_boundL {tbl : List Quint} (hsrc : Src3 tbl) (hcl : QClosed tbl 2)
    {z r1 r2 f' : Nat} {act : Bool → Nat → CAct} {s : Bool} (H : CellG tbl z r1 r2 f' act)
    (hS : find? tbl z (1 - f') = some ⟨z, 1 - f', 1 - f', Dir.R, sP r1 r2 s⟩) (hf2 : f' < 2)
    (hperm : ∀ q, q < 3 → q = z ∨ q = r1 ∨ q = r2) (hlen : HLen act s)
    (c : QConf) (a b : Int) (ha : a ≤ c.pos) (hb : c.pos ≤ b)
    (hz : ∀ x, (x < a ∨ b < x) → c.tape x = 0) (h2 : ∀ x, c.tape x < 2) :
    QHalts tbl c ↔ qrun tbl (bound3 6 1 a b) c = none := by
  constructor
  · intro hH
    obtain ⟨T, hR⟩ := qhalts_haltRun hH
    have hab := bnd_main H hS hf2 hlen hperm hsrc c a b ha hb hz h2 (T + 1) hR.dead
    refine bound_of_window hsrc hcl hR 6 1 a b hz h2 ?_ ?_
    · intro t ht; have := (hab t _ (hR.run t ht)).1; push_cast; omega
    · intro t ht; have := (hab t _ (hR.run t ht)).2; push_cast; omega
  · intro h; exact ⟨_, h⟩

/-! ### 3 つの型 -/

/-- 型 Q（class 39, 40, 55, 56）: r1 は 0 を吸収・1 で r2 を転送、r2 は 0 で r1 を転送・1 で止まる。 -/
def actQ : Bool → Nat → CAct
  | true, 0 => .ab
  | true, _ + 1 => .fw false
  | false, 0 => .fw true
  | false, _ + 1 => .ht

/-- 型 R（class 38, 47）: r1 は 0 で r1・1 で r2 を転送、r2 は 0 を吸収・1 で止まる。 -/
def actR : Bool → Nat → CAct
  | true, 0 => .fw true
  | true, _ + 1 => .fw false
  | false, 0 => .ab
  | false, _ + 1 => .ht

/-- 型 S（class 41, 58）: r1 は 0 で r2・1 で r1 を転送、r2 は 0 を吸収・1 で止まる。 -/
def actS : Bool → Nat → CAct
  | true, 0 => .fw false
  | true, _ + 1 => .fw true
  | false, 0 => .ab
  | false, _ + 1 => .ht

/-! #### 型 Q: 2 を受ける位置に 1 が無ければ止まらない -/

/-- 要求 a を受け続けるとき、2（= r2）を受ける位置（a が r1 なら奇数番目、r2 なら偶数番目）がすべて 0。 -/
def goodQ : List Nat → Bool → Prop
  | [], _ => True
  | _ :: t, true => goodQ t false
  | x :: t, false => x = 0 ∧ goodQ t true

theorem q_good : ∀ (cs : List Nat) (a : Bool), goodQ cs a → ∃ cs', cg actQ cs a = .ret cs' ∧ goodQ cs' a
  | [], true, _ => ⟨[1], rfl, trivial⟩
  | [], false, _ => ⟨[0, 1], rfl, show 0 = 0 ∧ goodQ [1] true from ⟨rfl, trivial⟩⟩
  | 0 :: t, true, h => ⟨1 :: t, rfl, h⟩
  | (x + 1) :: t, true, h => by
    obtain ⟨t', ht, hg⟩ := q_good t false h
    exact ⟨0 :: t', by simp only [cg, actQ, ht, COut.cons0], hg⟩
  | 0 :: t, false, h => by
    obtain ⟨t', ht, hg⟩ := q_good t true (And.right h)
    exact ⟨0 :: t', by simp only [cg, actQ, ht, COut.cons0], show 0 = 0 ∧ goodQ t' true from ⟨rfl, hg⟩⟩
  | (x + 1) :: t, false, h => absurd (And.left h) (by omega)

theorem q_bad : ∀ (cs : List Nat) (a : Bool), ¬ goodQ cs a →
    cg actQ cs a = .halt ∨ ∃ cs', cg actQ cs a = .ret cs' ∧ cs'.length = cs.length ∧ ¬ goodQ cs' a
  | [], _, h => absurd trivial h
  | 0 :: t, true, h => Or.inr ⟨1 :: t, rfl, rfl, h⟩
  | (x + 1) :: t, true, h => by
    rcases q_bad t false h with h1 | ⟨t', h1, hl, hg⟩
    · left; simp only [cg, actQ, h1, COut.cons0]
    · right; exact ⟨0 :: t', by simp only [cg, actQ, h1, COut.cons0], by simp [hl], hg⟩
  | 0 :: t, false, h => by
    have h' : ¬ goodQ t true := fun hg => h ⟨rfl, hg⟩
    rcases q_bad t true h' with h1 | ⟨t', h1, hl, hg⟩
    · left; simp only [cg, actQ, h1, COut.cons0]
    · right; exact ⟨0 :: t', by simp only [cg, actQ, h1, COut.cons0], by simp [hl], fun hh => hg (And.right hh)⟩
  | (x + 1) :: t, false, _ => Or.inl rfl

theorem q_good_it (s : Bool) : ∀ (m : Nat) (cs : List Nat), goodQ cs s → ∃ cs', srcIt actQ s cs m = .ret cs'
  | 0, cs, _ => ⟨cs, rfl⟩
  | m + 1, cs, h => by
    obtain ⟨cs', h1, hg⟩ := q_good cs s h
    obtain ⟨cs'', h2⟩ := q_good_it s m cs' hg
    exact ⟨cs'', by simp only [srcIt, h1, h2]⟩

theorem q_bad_it (s : Bool) : ∀ (m : Nat) (cs : List Nat), ¬ goodQ cs s → ∀ cs', srcIt actQ s cs m = .ret cs' →
    cs'.length = cs.length
  | 0, cs, _, cs', h => by simp only [srcIt, COut.ret.injEq] at h; rw [h]
  | m + 1, cs, hg, cs', h => by
    rcases q_bad cs s hg with h1 | ⟨cs1, h1, hl, hg1⟩
    · simp [srcIt, h1] at h
    · simp only [srcIt, h1] at h
      rw [q_bad_it s m cs1 hg1 cs' h, hl]

theorem hlenQ (s : Bool) : HLen actQ s := by
  intro cs _ ⟨N, hN⟩ m cs' h
  have hg : ¬ goodQ cs s := by
    intro hg
    obtain ⟨cs'', h'⟩ := q_good_it s N cs hg
    rw [hN] at h'; cases h'
  have := q_bad_it s m cs hg cs' h; omega

/-! #### 型 R: 1 が 2 つ以上なければ止まらない -/

/-- 0 でない項の数。 -/
def onesR : List Nat → Nat
  | [] => 0
  | 0 :: t => onesR t
  | (_ + 1) :: t => onesR t + 1

theorem cgR_nil : cg actR [] true = .div := rfl

theorem r_few : ∀ cs : List Nat, onesR cs ≤ 1 →
    cg actR cs true ≠ .halt ∧ ∀ cs', cg actR cs true = .ret cs' → onesR cs' ≤ 1
  | [], _ => ⟨by rw [cgR_nil]; decide, fun cs' h => by rw [cgR_nil] at h; cases h⟩
  | 0 :: t, h => by
    obtain ⟨h1, h2⟩ := r_few t h
    have hc : cg actR (0 :: t) true = (cg actR t true).cons0 := rfl
    rw [hc]
    refine ⟨fun hh => h1 (cons0_eq_halt hh), fun cs' hh => ?_⟩
    obtain ⟨t', ht', rfl⟩ := cons0_eq_ret hh
    exact h2 t' ht'
  | (x + 1) :: t, h => by
    have h0 : onesR t = 0 := by
      have : onesR ((x + 1) :: t) = onesR t + 1 := rfl
      omega
    have hc : cg actR ((x + 1) :: t) true = (cg actR t false).cons0 := rfl
    rw [hc]
    cases t with
    | nil =>
      have e : (cg actR [] false).cons0 = .ret [0, 1] := rfl
      rw [e]
      exact ⟨by decide, fun cs' hh => by cases hh; decide⟩
    | cons y u =>
      cases y with
      | zero =>
        have e : (cg actR (0 :: u) false).cons0 = .ret (0 :: 1 :: u) := rfl
        rw [e]
        refine ⟨by simp, fun cs' hh => ?_⟩
        cases hh
        have : onesR (0 :: u) = onesR u := rfl
        show onesR u + 1 ≤ 1
        omega
      | succ y =>
        have : onesR ((y + 1) :: u) = onesR u + 1 := rfl
        omega

theorem r_many : ∀ cs : List Nat, 2 ≤ onesR cs →
    cg actR cs true = .halt ∨ ∃ cs', cg actR cs true = .ret cs' ∧ cs'.length = cs.length ∧ 2 ≤ onesR cs'
  | [], h => absurd h (by decide)
  | 0 :: t, h => by
    have hc : cg actR (0 :: t) true = (cg actR t true).cons0 := rfl
    rw [hc]
    rcases r_many t h with h1 | ⟨t', h1, hl, ho⟩
    · left; rw [h1]; rfl
    · right; exact ⟨0 :: t', by rw [h1]; rfl, by simp [hl], ho⟩
  | (x + 1) :: t, h => by
    have hc : cg actR ((x + 1) :: t) true = (cg actR t false).cons0 := rfl
    rw [hc]
    cases t with
    | nil =>
      have : onesR [x + 1] = 1 := rfl
      omega
    | cons y u =>
      cases y with
      | zero =>
        right
        refine ⟨0 :: 1 :: u, rfl, rfl, ?_⟩
        have e1 : onesR ((x + 1) :: 0 :: u) = onesR u + 1 := rfl
        show 2 ≤ onesR u + 1
        omega
      | succ y => left; rfl

theorem r_few_it : ∀ (m : Nat) (cs : List Nat), onesR cs ≤ 1 → srcIt actR true cs m ≠ .halt
  | 0, _, _ => by simp [srcIt]
  | m + 1, cs, h => by
    obtain ⟨h1, h2⟩ := r_few cs h
    cases hc : cg actR cs true with
    | ret cs' => simp only [srcIt, hc]; exact r_few_it m cs' (h2 cs' hc)
    | halt => exact absurd hc h1
    | div => simp [srcIt, hc]

theorem r_many_it : ∀ (m : Nat) (cs : List Nat), 2 ≤ onesR cs → ∀ cs', srcIt actR true cs m = .ret cs' →
    cs'.length = cs.length
  | 0, cs, _, cs', h => by simp only [srcIt, COut.ret.injEq] at h; rw [h]
  | m + 1, cs, ho, cs', h => by
    rcases r_many cs ho with h1 | ⟨cs1, h1, hl, ho1⟩
    · simp [srcIt, h1] at h
    · simp only [srcIt, h1] at h
      rw [r_many_it m cs1 ho1 cs' h, hl]

theorem hlenR : HLen actR true := by
  intro cs _ ⟨N, hN⟩ m cs' h
  have ho : 2 ≤ onesR cs := by
    by_contra hc
    exact r_few_it N cs (by omega) hN
  have := r_many_it m cs ho cs' h; omega

/-! #### 型 S: 源が 3 回送るまでに止まる -/

theorem s_shape : ∀ (cs cs1 : List Nat), cg actS cs true = .ret cs1 → ∃ y u, cs1 = 0 :: y :: u
  | [], cs1, h => by
    have e : cg actS [] true = .ret [0, 1] := rfl
    rw [e] at h; cases h; exact ⟨1, [], rfl⟩
  | 0 :: t, cs1, h => by
    have hc : cg actS (0 :: t) true = (cg actS t false).cons0 := rfl
    rw [hc] at h
    cases t with
    | nil =>
      have e : (cg actS [] false).cons0 = .ret [0, 1] := rfl
      rw [e] at h; cases h; exact ⟨1, [], rfl⟩
    | cons y u =>
      cases y with
      | zero =>
        have e : (cg actS (0 :: u) false).cons0 = .ret (0 :: 1 :: u) := rfl
        rw [e] at h; cases h; exact ⟨1, u, rfl⟩
      | succ y =>
        have e : (cg actS ((y + 1) :: u) false).cons0 = .halt := rfl
        rw [e] at h; cases h
  | (x + 1) :: t, cs1, h => by
    have hc : cg actS ((x + 1) :: t) true = (cg actS t true).cons0 := rfl
    rw [hc] at h
    obtain ⟨t', ht', rfl⟩ := cons0_eq_ret h
    obtain ⟨y, u, rfl⟩ := s_shape t t' ht'
    exact ⟨0, y :: u, rfl⟩

theorem hlenS : HLen actS true := by
  intro cs _ _ m cs' h
  cases m with
  | zero => simp only [srcIt, COut.ret.injEq] at h; subst h; omega
  | succ m =>
    cases hc : cg actS cs true with
    | halt => simp [srcIt, hc] at h
    | div => simp [srcIt, hc] at h
    | ret cs1 =>
      have hl1 := cg_len hc
      obtain ⟨y, u, rfl⟩ := s_shape cs cs1 hc
      simp only [srcIt, hc] at h
      cases m with
      | zero => simp only [srcIt, COut.ret.injEq] at h; subst h; exact hl1
      | succ m =>
        cases y with
        | succ y =>
          have e : cg actS (0 :: (y + 1) :: u) true = .halt := rfl
          simp [srcIt, e] at h
        | zero =>
          have e : cg actS (0 :: 0 :: u) true = .ret (0 :: 1 :: u) := rfl
          simp only [srcIt, e] at h
          cases m with
          | zero =>
            simp only [srcIt, COut.ret.injEq] at h; subst h
            simp only [List.length_cons] at hl1 ⊢; exact hl1
          | succ m =>
            have e3 : cg actS (0 :: 1 :: u) true = .halt := rfl
            simp [srcIt, e3] at h

/-! ### Bool の検査 -/

/-- r1, r2 の規則が動作 act のとおり。 -/
def cellGWith (tbl : List Quint) (z r1 r2 f' : Nat) (act : Bool → Nat → CAct) : Bool :=
  [true, false].all fun a => [0, 1].all fun x =>
    decide (find? tbl (sP r1 r2 a) x = cellRule z r1 r2 f' a x (act a x))

/-- 状態の役割 z, r1, r2 が 0, 1, 2 を尽くす。 -/
def permOK (z r1 r2 : Nat) : Bool := [0, 1, 2].all fun q => q == z || q == r1 || q == r2

theorem permOK_spec {z r1 r2 : Nat} (h : permOK z r1 r2 = true) : ∀ q, q < 3 → q = z ∨ q = r1 ∨ q = r2 := by
  intro q hq
  have := List.all_eq_true.mp h q (by simp; omega)
  simp only [Bool.or_eq_true, beq_iff_eq] at this
  rcases this with (h1 | h1) | h1
  · exact Or.inl h1
  · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr h1)

/-- z の 2 つの規則（L1 と源 R3）、f' < 2、状態の役割が 0, 1, 2 を尽くす。 -/
def srcWith (tbl : List Quint) (z r1 r2 f' : Nat) (s : Bool) : Bool :=
  decide (f' < 2) && decide (find? tbl z f' = some ⟨z, f', 0, Dir.L, z⟩) &&
  decide (find? tbl z (1 - f') = some ⟨z, 1 - f', 1 - f', Dir.R, sP r1 r2 s⟩) &&
  permOK z r1 r2

/-- 型 Q・R・S のどれかの源つきの表。 -/
def sideLWith (tbl : List Quint) (z r1 r2 f' : Nat) : Bool :=
  (cellGWith tbl z r1 r2 f' actQ && (srcWith tbl z r1 r2 f' true || srcWith tbl z r1 r2 f' false)) ||
  (cellGWith tbl z r1 r2 f' actR && srcWith tbl z r1 r2 f' true) ||
  (cellGWith tbl z r1 r2 f' actS && srcWith tbl z r1 r2 f' true)

/-- (z, r1, r2) の 6 通りと f'。 -/
def sideL (tbl : List Quint) : Bool :=
  cell2Roles.any fun r => [0, 1].any fun f' => sideLWith tbl r.1 r.2.1 r.2.2 f'

theorem cellGWith_spec {tbl : List Quint} {z r1 r2 f' : Nat} {act : Bool → Nat → CAct}
    (h : cellGWith tbl z r1 r2 f' act = true) (hZ : find? tbl z f' = some ⟨z, f', 0, Dir.L, z⟩) :
    CellG tbl z r1 r2 f' act := by
  refine ⟨fun a x hx => ?_, hZ⟩
  have h1 := List.all_eq_true.mp h a (by cases a <;> simp)
  have h2 := List.all_eq_true.mp h1 x (by rcases (by omega : x = 0 ∨ x = 1) with rfl | rfl <;> simp)
  exact of_decide_eq_true h2

theorem srcWith_spec {tbl : List Quint} {z r1 r2 f' : Nat} {s : Bool} (h : srcWith tbl z r1 r2 f' s = true) :
    f' < 2 ∧ find? tbl z f' = some ⟨z, f', 0, Dir.L, z⟩ ∧
      find? tbl z (1 - f') = some ⟨z, 1 - f', 1 - f', Dir.R, sP r1 r2 s⟩ ∧
      (∀ q, q < 3 → q = z ∨ q = r1 ∨ q = r2) := by
  unfold srcWith at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨h1, h2, h3, permOK_spec h4⟩

theorem sideL_bound {tbl : List Quint} (hsrc : Src3 tbl) (hcl : QClosed tbl 2) (h : sideL tbl = true) :
    ∀ (c : QConf) (a b : Int), a ≤ c.pos → c.pos ≤ b →
      (∀ x, (x < a ∨ b < x) → c.tape x = 0) → (∀ x, c.tape x < 2) →
      (QHalts tbl c ↔ qrun tbl (bound3 6 1 a b) c = none) := by
  unfold sideL at h
  simp only [List.any_eq_true] at h
  obtain ⟨r, -, f', -, hw⟩ := h
  unfold sideLWith at hw
  simp only [Bool.or_eq_true, Bool.and_eq_true] at hw
  rcases hw with ⟨⟨hc, hs | hs⟩ | ⟨hc, hs⟩⟩ | ⟨hc, hs⟩
  · obtain ⟨hf2, hZ, hS, hperm⟩ := srcWith_spec hs
    exact halts_iff_boundL hsrc hcl (cellGWith_spec hc hZ) hS hf2 hperm (hlenQ true)
  · obtain ⟨hf2, hZ, hS, hperm⟩ := srcWith_spec hs
    exact halts_iff_boundL hsrc hcl (cellGWith_spec hc hZ) hS hf2 hperm (hlenQ false)
  · obtain ⟨hf2, hZ, hS, hperm⟩ := srcWith_spec hs
    exact halts_iff_boundL hsrc hcl (cellGWith_spec hc hZ) hS hf2 hperm hlenR
  · obtain ⟨hf2, hZ, hS, hperm⟩ := srcWith_spec hs
    exact halts_iff_boundL hsrc hcl (cellGWith_spec hc hZ) hS hf2 hperm hlenS

theorem sideL_mir_bound {tbl : List Quint} (hsrc : Src3 tbl) (hcl : QClosed tbl 2)
    (h : sideL (mirTbl tbl) = true) :
    ∀ (c : QConf) (a b : Int), a ≤ c.pos → c.pos ≤ b →
      (∀ x, (x < a ∨ b < x) → c.tape x = 0) → (∀ x, c.tape x < 2) →
      (QHalts tbl c ↔ qrun tbl (bound3 6 1 a b) c = none) := by
  rw [mirTbl_eq] at h
  have hb := sideL_bound (src3_mir hsrc) (closed_mir hcl) h
  intro c a b ha hb' hz h2
  have := hb (mirQ c) (-b) (-a) (by show -b ≤ -c.pos; omega) (by show -c.pos ≤ -a; omega)
    (fun x hx => by show c.tape (-x) = 0; exact hz (-x) (by omega)) (fun x => h2 (-x))
  rw [QHalts_mir, qrun_mir] at this
  have e : bound3 6 1 (-b) (-a) = bound3 6 1 a b := by
    unfold bound3; congr 2; omega
  rw [e] at this
  rw [this]
  cases qrun tbl (bound3 6 1 a b) c <;> simp

/-- **群 D の源つきの 8 類の検査**: 表か、その鏡像が `sideL`。 -/
def grpL (es : List Nat) (D : List Dir) : Bool :=
  sideL (URTM.Three.realize es D) || sideL (mirTbl (URTM.Three.realize es D))

/-- 段階 2e の 8 の例外: `isExcK` の表のうち、この 8 類に当たらない表。 -/
def isExcL (es : List Nat) (D : List Dir) : Bool := isExcK es D && !grpL es D

/-- 窓の幅で書いた上界。 -/
def bndL (w : Nat) : Nat := bnd3N 6 1 w

theorem bndL_primrec : Primrec bndL :=
  (Primrec.nat_add.comp (csize_primrec.comp (Primrec.const 2)
    (Primrec.nat_add.comp (Primrec.nat_add.comp (Primrec.nat_add.comp Primrec.id (Primrec.const 6))
      (Primrec.const 1)) (Primrec.const 1))) (Primrec.const 1)).of_eq fun w => rfl

section
variable {tbl : List Quint} {q₀ q₁ q₂ sg : Nat}

/-- **8 類の有界停止**（任意の表の正規形）。 -/
theorem okL_bound (H : RTM32 tbl q₀ q₁ q₂ sg)
    (hok : grpL (absCodes q₀ q₁ q₂ sg tbl) (absDirs q₀ q₁ q₂ tbl) = true) :
    ∀ (c : QConf) (m n : ℕ), -(m : ℤ) ≤ c.pos → c.pos ≤ (n : ℤ) →
      (∀ x, (x < -(m : ℤ) ∨ (n : ℤ) < x) → c.tape x = 0) → (∀ x, c.tape x < 2) →
      (QHalts (normT (tbl := tbl) (q₀ := q₀) (q₁ := q₁) (q₂ := q₂) (σ := sg)) c ↔
        qrun (normT (tbl := tbl) (q₀ := q₀) (q₁ := q₁) (q₂ := q₂) (σ := sg)) (bndL (m + n)) c
          = none) := by
  have hsrc := realize_src3 (absCodes q₀ q₁ q₂ sg tbl) (absDirs q₀ q₁ q₂ tbl)
  have hcl := realize_closed (absCodes q₀ q₁ q₂ sg tbl) (absDirs q₀ q₁ q₂ tbl)
  unfold grpL at hok
  have hb : ∀ (c : QConf) (a b : Int), a ≤ c.pos → c.pos ≤ b →
      (∀ x, (x < a ∨ b < x) → c.tape x = 0) → (∀ x, c.tape x < 2) →
      (QHalts (URTM.Three.realize (absCodes q₀ q₁ q₂ sg tbl) (absDirs q₀ q₁ q₂ tbl)) c ↔
        qrun (URTM.Three.realize (absCodes q₀ q₁ q₂ sg tbl) (absDirs q₀ q₁ q₂ tbl))
          (bound3 6 1 a b) c = none) := by
    rcases Bool.or_eq_true_iff.mp hok with h | h
    · exact sideL_bound hsrc hcl h
    · exact sideL_mir_bound hsrc hcl h
  intro c m n ha hb' hz h2
  unfold bndL
  rw [← bound3_eq]
  exact hb c _ _ ha hb' hz h2

/-- **3 状態 2 記号の RTM の停止問題は、U の ID の上で計算可能**（`isExcL` の表を除く）。 -/
theorem three_halting_computable_L (H : RTM32 tbl q₀ q₁ q₂ sg)
    (hne : isExcL (absCodes q₀ q₁ q₂ sg tbl) (absDirs q₀ q₁ q₂ tbl) = false) :
    ∃ f : ZID → Bool, Computable f ∧
      ∀ z, (∀ a ∈ z.2.1 ++ z.2.2, a = 0 ∨ a ∈ [sg]) → (ZHalts tbl z ↔ f z = true) := by
  cases hK : isExcK (absCodes q₀ q₁ q₂ sg tbl) (absDirs q₀ q₁ q₂ tbl) with
  | false => exact three_halting_computable_K H hK
  | true =>
    have hL : grpL (absCodes q₀ q₁ q₂ sg tbl) (absDirs q₀ q₁ q₂ tbl) = true := by
      unfold isExcL at hne; rw [hK] at hne; simpa using hne
    exact halting_computable_of_bound H bndL_primrec (okL_bound H hL)

/-- **定理（段階 2e の 8）: `isExcL` の表を除き、3 状態 2 記号の URTM は存在しない**（Morita Def. 7.1、
    U の記号集合 {0, sg} の上の ID への符号化）。 -/
theorem no_three_two_URTM_L (H : RTM32 tbl q₀ q₁ q₂ sg)
    (hne : isExcL (absCodes q₀ q₁ q₂ sg tbl) (absDirs q₀ q₁ q₂ tbl) = false) :
    ¬ IsUTM_MoritaOver tbl [sg] :=
  not_UTM_of_halting_computable (three_halting_computable_L H hne)

end

/-! ### 残る例外の数

段階 2e の 7 の例外の上界 120 表（`excKKeys`）のうち、`grpL` に当たる 96 表（8 類）の鍵を一覧 `l96Keys` に書き、
それらが `grpL` に当たることを kernel で確かめる。残る例外はその外の 24 表に**含まれる**（上界）。 -/

/-- `grpL` に当たる 96 表の鍵（Python で生成。下の `l96_grpL` が kernel で検査する）。 -/
def l96Keys : List Nat := [
  241403, 241776, 241991, 242364, 244343, 244357, 247068, 247070, 290795, 290809, 297865, 307632,
  307634, 317042, 326677, 345854, 709167, 710539, 711820, 712016, 716343, 716367, 716596, 716620,
  733143, 734515, 736915, 750196, 750392, 755192, 794539, 812816, 986887, 987115, 987127, 987451,
  1020501, 1020921, 1021065, 1021509, 1027760, 1027940, 1027952, 1028612, 1032562, 1033318, 1033414, 1033906,
  2163377, 2163605, 2163617, 2163941, 2196991, 2197411, 2197555, 2197999, 2204250, 2204430, 2204442, 2205102,
  2209052, 2209808, 2209904, 2210396, 2356253, 2357625, 2358906, 2359102, 2363429, 2363453, 2363682, 2363706,
  2380229, 2381601, 2384001, 2397282, 2397478, 2402278, 2441625, 2459902, 2829681, 2830054, 2830269, 2830642,
  2832621, 2832635, 2835346, 2835348, 2879073, 2879087, 2886143, 2895910, 2895912, 2905320, 2914955, 2934132
]

theorem l96_grpL : l96Keys.all (fun k => grpL (unkey k).1 (unkey k).2) = true := by decide +kernel

theorem l96_sub : l96Keys.all (fun k => excKKeys.contains k) = true := by decide +kernel

/-- 段階 2e の 8 の例外の鍵（の上界）。 -/
def excLKeys : List Nat := excKKeys.filter fun k => !l96Keys.contains k

/-- **段階 2e の 8 の例外の表（の上界）の一覧**。 -/
def excLTables : List (List Nat × List Dir) := excLKeys.map unkey

/-- **主定理の仮定が外れる表は一覧に載る**（符号 6 つ・向き 3 つの表について）。 -/
theorem mem_excLTables {es : List Nat} {D : List Dir} (h : ValidKey es D) (hx : isExcL es D = true) :
    (es, D) ∈ excLTables := by
  unfold isExcL at hx
  obtain ⟨hK, hL⟩ := Bool.and_eq_true_iff.mp hx
  obtain ⟨k, hk, he⟩ := List.mem_map.mp (mem_excKTables h hK)
  refine List.mem_map.mpr ⟨k, List.mem_filter.mpr ⟨hk, ?_⟩, he⟩
  cases hc : l96Keys.contains k
  · rfl
  · exfalso
    have := List.all_eq_true.mp l96_grpL k (List.contains_iff_mem.mp hc)
    rw [he] at this
    simp only [this, Bool.not_true] at hL
    exact Bool.false_ne_true hL

/-- **段階 2e の 8 の例外は高々 24 表**（120 − 96。kernel の評価）。 -/
theorem excLKeys_length : excLKeys.length = 24 := by decide +kernel

theorem excLTables_length : excLTables.length = 24 := by
  unfold excLTables; rw [List.length_map, excLKeys_length]

end URTM.Meta
