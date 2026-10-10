/-
  2 状態 RTM の停止問題の決定可能性 その 9: Morita の五つ組の表との橋。**手書き**。

  Morita 2017 の TM（Def. 5.1/5.3）を**両側無限テープ**の上でそのまま定義する（`QConf`・`qstep`）。
  規則が無ければ停止。空白は記号 0（記号の付け替えで一般性を失わない）。
    * `qrun_iff_run2` : 可逆（Def. 5.4 の `reversible`）で 2 状態 {qL, qR}、左へ動いて qL に入る規則と
      右へ動いて qR に入る規則が両方あるとき（docs/10 の場合 (iii)）、表の実行は方向状態機械
      `ruleOf` の実行と 1 歩ずつ一致する（構造定理 `two_state_shape` による）
-/
import URTM.TSDMain
import URTM.TwoState

namespace URTM.TwoState

/-- 両側無限テープ上の五つ組 TM の配置。 -/
structure QConf where
  st : Nat
  pos : Int
  tape : Int → Nat

def qstep (tbl : List Quint) (c : QConf) : Option QConf :=
  match find? tbl c.st (c.tape c.pos) with
  | none => none
  | some r => some ⟨r.q, move r.d c.pos, write c.tape c.pos r.t⟩

def qrun (tbl : List Quint) : Nat → QConf → Option QConf
  | 0, c => some c
  | n + 1, c =>
    match qstep tbl c with
    | none => none
    | some c' => qrun tbl n c'

/-- 表の TM が停止する。 -/
def QHalts (tbl : List Quint) (c : QConf) : Prop := ∃ n, qrun tbl n c = none

theorem find?_spec {tbl : List Quint} {p s : Nat} {r : Quint} (h : find? tbl p s = some r) :
    r ∈ tbl ∧ r.p = p ∧ r.s = s := by
  unfold find? at h
  have hm := List.mem_of_find?_eq_some h
  have hp := List.find?_some h
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  exact ⟨hm, hp.1, hp.2⟩

section Bridge
variable (tbl : List Quint) (qL qR : Nat)

def stOf : Dir → Nat
  | Dir.L => qL
  | Dir.Z => qL
  | Dir.R => qR

def dirOf (q : Nat) : Dir := if q = qL then Dir.L else Dir.R

/-- 表から方向状態機械を作る。 -/
def ruleOf : Rule := fun d s => (find? tbl (stOf qL qR d) s).map (fun r => (r.t, dirOf qL r.q))

def toC2 (c : QConf) : Conf2 := ⟨c.tape, c.pos, dirOf qL c.st⟩

end Bridge

/-- 場合 (iii) の仮定。 -/
structure Case3 (tbl : List Quint) (qL qR : Nat) : Prop where
  rev : reversible tbl = true
  ne : qL ≠ qR
  states : ∀ r ∈ tbl, r.q = qL ∨ r.q = qR
  hasL : ∃ a ∈ tbl, a.q = qL ∧ a.d = Dir.L
  hasR : ∃ b ∈ tbl, b.q = qR ∧ b.d = Dir.R

theorem Case3.dir_eq {tbl : List Quint} {qL qR : Nat} (h : Case3 tbl qL qR) :
    ∀ r ∈ tbl, r.d = dirOf qL r.q := by
  obtain ⟨a, ha, haq, had⟩ := h.hasL
  obtain ⟨b, hb, hbq, hbd⟩ := h.hasR
  obtain ⟨_, hLd, hRd⟩ := two_state_shape h.rev h.states ha hb haq had hbq hbd
  intro r hr
  rcases h.states r hr with hq | hq
  · rw [hLd r hr hq]; unfold dirOf; rw [if_pos hq]
  · rw [hRd r hr hq]; unfold dirOf; rw [if_neg (by rw [hq]; exact fun e => h.ne e.symm)]

theorem stOf_dirOf {qL qR : Nat} {q : Nat} (hq : q = qL ∨ q = qR) :
    stOf qL qR (dirOf qL q) = q := by
  unfold dirOf
  by_cases h : q = qL
  · rw [if_pos h]; exact h.symm
  · rw [if_neg h]; rcases hq with hq | hq
    · exact absurd hq h
    · exact hq.symm

theorem qstep_iff {tbl : List Quint} {qL qR : Nat} (h : Case3 tbl qL qR) (c : QConf)
    (hst : c.st = qL ∨ c.st = qR) :
    (qstep tbl c = none ∧ step2 (ruleOf tbl qL qR) (toC2 qL c) = none) ∨
    ∃ c', qstep tbl c = some c' ∧ (c'.st = qL ∨ c'.st = qR) ∧
      step2 (ruleOf tbl qL qR) (toC2 qL c) = some (toC2 qL c') := by
  have hs : stOf qL qR (dirOf qL c.st) = c.st := stOf_dirOf hst
  cases hf : find? tbl c.st (c.tape c.pos) with
  | none =>
    left
    refine ⟨by unfold qstep; rw [hf], ?_⟩
    unfold step2 ruleOf toC2; simp only; rw [hs, hf]; rfl
  | some r =>
    right
    obtain ⟨hr, _, _⟩ := find?_spec hf
    refine ⟨⟨r.q, move r.d c.pos, write c.tape c.pos r.t⟩, by unfold qstep; rw [hf],
      h.states r hr, ?_⟩
    unfold step2 ruleOf toC2; simp only; rw [hs, hf]
    simp only [Option.map]
    rw [h.dir_eq r hr]

theorem qrun_iff_run2 {tbl : List Quint} {qL qR : Nat} (h : Case3 tbl qL qR) :
    ∀ (n : Nat) (c : QConf), (c.st = qL ∨ c.st = qR) →
      (qrun tbl n c = none ↔ run2 (ruleOf tbl qL qR) n (toC2 qL c) = none) := by
  intro n
  induction n with
  | zero => intro c _; simp [qrun, run2]
  | succ n ih =>
    intro c hst
    rcases qstep_iff h c hst with ⟨h1, h2⟩ | ⟨c', h1, hst', h2⟩
    · constructor
      · intro _; unfold run2; rw [h2]
      · intro _; unfold qrun; rw [h1]
    · have e1 : qrun tbl (n + 1) c = qrun tbl n c' := by simp [qrun, h1]
      have e2 : run2 (ruleOf tbl qL qR) (n + 1) (toC2 qL c) =
          run2 (ruleOf tbl qL qR) n (toC2 qL c') := run2_succ_some _ n h2
      rw [e1, e2]; exact ih c' hst'

theorem QHalts_iff_Halts {tbl : List Quint} {qL qR : Nat} (h : Case3 tbl qL qR) (c : QConf)
    (hst : c.st = qL ∨ c.st = qR) :
    QHalts tbl c ↔ Halts (ruleOf tbl qL qR) (toC2 qL c) := by
  constructor
  · rintro ⟨n, hn⟩; exact ⟨n, (qrun_iff_run2 h n c hst).mp hn⟩
  · rintro ⟨n, hn⟩; exact ⟨n, (qrun_iff_run2 h n c hst).mpr hn⟩

theorem ruleOf_NoZ (tbl : List Quint) (qL qR : Nat) : NoZ (ruleOf tbl qL qR) := by
  intro d s v d' h
  unfold ruleOf at h
  cases hf : find? tbl (stOf qL qR d) s with
  | none => rw [hf] at h; exact absurd h (by simp)
  | some r =>
    rw [hf] at h
    have hh : (r.t, dirOf qL r.q) = (v, d') := Option.some.inj h
    have e : d' = dirOf qL r.q := (congrArg Prod.snd hh).symm
    rw [e]; unfold dirOf; split <;> simp

/-- 表の記号が nsym 未満で閉じている。 -/
def QClosed (tbl : List Quint) (nsym : Nat) : Prop := ∀ r ∈ tbl, r.s < nsym → r.t < nsym

theorem ruleOf_Closed {tbl : List Quint} {nsym : Nat} (hcl : QClosed tbl nsym) (qL qR : Nat) :
    Closed (ruleOf tbl qL qR) nsym := by
  intro d s v d' hs h
  unfold ruleOf at h
  cases hf : find? tbl (stOf qL qR d) s with
  | none => rw [hf] at h; exact absurd h (by simp)
  | some r =>
    rw [hf] at h
    have hh : (r.t, dirOf qL r.q) = (v, d') := Option.some.inj h
    have e : v = r.t := (congrArg Prod.fst hh).symm
    obtain ⟨hr, _, hrs⟩ := find?_spec hf
    rw [e]; exact hcl r hr (by rw [hrs]; exact hs)

/-- **場合 (iii) の決定可能性**（Morita の表のまま）。 -/
theorem case3_decidable {tbl : List Quint} {qL qR : Nat} (h : Case3 tbl qL qR) {nsym : Nat}
    (hcl : QClosed tbl nsym) (a b : Int) (c : QConf) (hst : c.st = qL ∨ c.st = qR)
    (hinit : ∀ x, c.tape x < nsym) (hab : a ≤ b) (ha : a ≤ c.pos) (hb : c.pos ≤ b)
    (hsupp : ∀ x, (x < a ∨ b < x) → c.tape x = 0) :
    decideHalt (ruleOf tbl qL qR) nsym a b (toC2 qL c) = true ↔ QHalts tbl c := by
  rw [QHalts_iff_Halts h c hst]
  exact decideHalt_correct _ (ruleOf_NoZ tbl qL qR) nsym (ruleOf_Closed hcl qL qR) a b _
    hinit hab ha hb hsupp

end URTM.TwoState
