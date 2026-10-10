/-
  Mathlib の `Turing.TM0` 機械（有限の台 S に支えられるもの）を、本体の五つ組表 `List Quint`
  （Morita の五つ組 [p, s, t, d, q]、両側無限テープ、空白 0）へ翻訳し、停止が一致することを示す。

  TM0 の 1 歩は「書く」か「動く」のどちらか一方なので、それぞれ
    書く b   ↦ [p, s, b, 0, q]   （d = 0: 動かない）
    左へ動く ↦ [p, s, s, −, q]   （同じ記号を書き戻す）
    右へ動く ↦ [p, s, s, +, q]
  という五つ組 1 本に写す。状態は台 S の中の番号、記号は有限型 Γ の番号（空白 `default` ↦ 0）。
  停止の一致は Mathlib の `StateTransition.tr_eval_dom`（1 歩ずつの模倣）で示す。
-/
import Mathlib.Computability.TuringMachine.PostTuringMachine
import URTMMeta.NoURTM

namespace URTM.Meta
open URTM Turing StateTransition

/-! ### zipper の停止と `StateTransition.eval` -/

theorem zrun_reaches (tbl : List Quint) :
    ∀ n (z z' : ZID), zrun tbl n z = some z' → Reaches (zstep tbl) z z'
  | 0, z, z', h => by
    simp only [zrun, Option.some.injEq] at h; subst h; exact Relation.ReflTransGen.refl
  | n + 1, z, z', h => by
    unfold zrun at h
    cases hs : zstep tbl z with
    | none => rw [hs] at h; exact absurd h (by simp)
    | some z₁ =>
      rw [hs] at h
      exact Relation.ReflTransGen.head (Option.mem_def.mpr hs) (zrun_reaches tbl n z₁ z' h)

theorem reaches_zrun (tbl : List Quint) {z z' : ZID} (h : Reaches (zstep tbl) z z') :
    ∃ n, zrun tbl n z = some z' := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨0, rfl⟩
  | head hab _ ih =>
    obtain ⟨n, hn⟩ := ih
    refine ⟨n + 1, ?_⟩
    unfold zrun
    rw [Option.mem_def.mp hab]
    exact hn

theorem zrun_none_last (tbl : List Quint) :
    ∀ n (z : ZID), zrun tbl n z = none → ∃ m b, zrun tbl m z = some b ∧ zstep tbl b = none
  | 0, z, h => by simp [zrun] at h
  | n + 1, z, h => by
    unfold zrun at h
    cases hs : zstep tbl z with
    | none => exact ⟨0, z, rfl, hs⟩
    | some z₁ =>
      rw [hs] at h
      obtain ⟨m, b, h1, h2⟩ := zrun_none_last tbl n z₁ h
      refine ⟨m + 1, b, ?_, h2⟩
      unfold zrun; rw [hs]; exact h1

/-- 止まる ⟺ `StateTransition.eval` が定義される。 -/
theorem ZHalts_iff_eval (tbl : List Quint) (z : ZID) :
    ZHalts tbl z ↔ (eval (zstep tbl) z).Dom := by
  rw [Part.dom_iff_mem]
  constructor
  · rintro ⟨n, hn⟩
    obtain ⟨m, b, h1, h2⟩ := zrun_none_last tbl n z hn
    exact ⟨b, mem_eval.mpr ⟨zrun_reaches tbl m z b h1, h2⟩⟩
  · rintro ⟨b, hb⟩
    obtain ⟨h1, h2⟩ := mem_eval.mp hb
    obtain ⟨m, hm⟩ := reaches_zrun tbl h1
    exact ZHalts_of_at ⟨m, hm, h2⟩

/-- 止まった配置の形で: `ZHalts` なら止まる配置がある。 -/
theorem ZHalts.exists_at {tbl : List Quint} {z : ZID} (h : ZHalts tbl z) :
    ∃ b, ZHaltsAt tbl z b := by
  obtain ⟨n, hn⟩ := h
  obtain ⟨m, b, h1, h2⟩ := zrun_none_last tbl n z hn
  exact ⟨b, m, h1, h2⟩

/-! ### 表引きの一意性 -/

theorem look_none_of (tbl : List Quint) (P s : Nat) (h : ∀ r ∈ tbl, ¬ (r.p = P ∧ r.s = s)) :
    look tbl P s = none := by
  induction tbl with
  | nil => rfl
  | cons r tbl ih =>
    unfold look
    rw [if_neg (h r (List.mem_cons_self ..))]
    exact ih fun r' hr' => h r' (List.mem_cons_of_mem _ hr')

theorem look_unique (tbl : List Quint) (P s : Nat) (r₀ : Quint) (h₀ : r₀ ∈ tbl)
    (hp : r₀.p = P) (hs : r₀.s = s)
    (h : ∀ r ∈ tbl, r.p = P → r.s = s → r = r₀) : look tbl P s = some (rhs r₀) := by
  induction tbl with
  | nil => simp at h₀
  | cons r tbl ih =>
    unfold look
    by_cases hr : r.p = P ∧ r.s = s
    · rw [if_pos hr, h r (List.mem_cons_self ..) hr.1 hr.2]
    · rw [if_neg hr]
      rcases List.mem_cons.mp h₀ with e | e
      · subst e; exact absurd ⟨hp, hs⟩ hr
      · exact ih e fun r' hr' => h r' (List.mem_cons_of_mem _ hr')

/-! ### TM0 → 五つ組表 -/

section Translate

variable {Γ Λ : Type} [Inhabited Γ] [Inhabited Λ] [Fintype Γ] [DecidableEq Γ] [DecidableEq Λ]

/-- 記号の一覧（有限型の全要素）。 -/
noncomputable def symL (Γ : Type) [Fintype Γ] : List Γ := (Finset.univ : Finset Γ).toList

/-- 記号の番号。空白 `default` は 0。 -/
noncomputable def symN (a : Γ) : Nat := if a = default then 0 else (symL Γ).idxOf a + 1

/-- 状態の番号（台 S の中の位置）。 -/
noncomputable def stN (S : Finset Λ) (q : Λ) : Nat := S.toList.idxOf q

theorem symN_default : symN (default : Γ) = 0 := if_pos rfl

theorem symN_inj {a b : Γ} (h : symN a = symN b) : a = b := by
  unfold symN at h
  by_cases ha : a = default <;> by_cases hb : b = default
  · rw [ha, hb]
  · rw [if_pos ha, if_neg hb] at h; omega
  · rw [if_neg ha, if_pos hb] at h; omega
  · rw [if_neg ha, if_neg hb] at h
    exact (List.idxOf_inj (l := symL Γ) (Finset.mem_toList.mpr (Finset.mem_univ a))).mp (by omega)

omit [Inhabited Λ] in
theorem stN_inj {S : Finset Λ} {q q' : Λ} (hq : q ∈ S) (h : stN S q = stN S q') : q = q' :=
  (List.idxOf_inj (Finset.mem_toList.mpr hq)).mp h

/-- TM0 の 1 規則（状態 q で a を読んで o）を五つ組に。 -/
noncomputable def mkQ (S : Finset Λ) (q : Λ) (a : Γ) (o : Λ × TM0.Stmt Γ) : Quint :=
  match o.2 with
  | .move .left => ⟨stN S q, symN a, symN a, .L, stN S o.1⟩
  | .move .right => ⟨stN S q, symN a, symN a, .R, stN S o.1⟩
  | .write b => ⟨stN S q, symN a, symN b, .Z, stN S o.1⟩

omit [Inhabited Λ] in
theorem mkQ_p (S : Finset Λ) (q : Λ) (a : Γ) (o : Λ × TM0.Stmt Γ) : (mkQ S q a o).p = stN S q := by
  obtain ⟨q', st⟩ := o; cases st with
  | move d => cases d <;> rfl
  | write b => rfl

omit [Inhabited Λ] in
theorem mkQ_s (S : Finset Λ) (q : Λ) (a : Γ) (o : Λ × TM0.Stmt Γ) : (mkQ S q a o).s = symN a := by
  obtain ⟨q', st⟩ := o; cases st with
  | move d => cases d <;> rfl
  | write b => rfl

/-- **翻訳した五つ組表**: 台 S の状態と全記号の組ごとに、規則があれば五つ組 1 本。 -/
noncomputable def tblOf (M : TM0.Machine Γ Λ) (S : Finset Λ) : List Quint :=
  S.toList.flatMap fun q => (symL Γ).filterMap fun a => (M q a).map (mkQ S q a)

theorem mem_tblOf {M : TM0.Machine Γ Λ} {S : Finset Λ} {r : Quint} :
    r ∈ tblOf M S ↔ ∃ q ∈ S, ∃ a o, M q a = some o ∧ mkQ S q a o = r := by
  unfold tblOf
  simp only [List.mem_flatMap, List.mem_filterMap, Option.map_eq_some_iff, Finset.mem_toList]
  constructor
  · rintro ⟨q, hq, a, _, o, ho, rfl⟩; exact ⟨q, hq, a, o, ho, rfl⟩
  · rintro ⟨q, hq, a, o, ho, rfl⟩; exact ⟨q, hq, a, by simp [symL], o, ho, rfl⟩

/-- 表引きは TM0 の遷移と一致する（q ∈ S）。 -/
theorem look_tblOf (M : TM0.Machine Γ Λ) (S : Finset Λ) {q : Λ} (hq : q ∈ S) (a : Γ) :
    look (tblOf M S) (stN S q) (symN a) = (M q a).map (fun o => rhs (mkQ S q a o)) := by
  have key : ∀ r ∈ tblOf M S, r.p = stN S q → r.s = symN a →
      ∃ o, M q a = some o ∧ mkQ S q a o = r := by
    intro r hr hp hs
    obtain ⟨q', hq', a', o, ho, rfl⟩ := mem_tblOf.mp hr
    rw [mkQ_p] at hp; rw [mkQ_s] at hs
    obtain rfl := stN_inj hq' hp
    obtain rfl := symN_inj hs
    exact ⟨o, ho, rfl⟩
  cases hM : M q a with
  | none =>
    apply look_none_of
    rintro r hr ⟨hp, hs⟩
    obtain ⟨o, ho, _⟩ := key r hr hp hs
    rw [hM] at ho; exact absurd ho (by simp)
  | some o =>
    apply look_unique _ _ _ _ (mem_tblOf.mpr ⟨q, hq, a, o, hM, rfl⟩) (mkQ_p ..) (mkQ_s ..)
    intro r hr hp hs
    obtain ⟨o', ho', rfl⟩ := key r hr hp hs
    rw [hM] at ho'; cases ho'; rfl

/-- TM0 の配置と zipper の対応。 -/
def TRel (S : Finset Λ) (c : TM0.Cfg Γ Λ) (z : ZID) : Prop :=
  c.q ∈ S ∧ z.1 = stN S c.q ∧ z.2.2.headD 0 = symN c.Tape.head ∧
    (∀ i, z.2.2.getD (i + 1) 0 = symN (c.Tape.right.nth i)) ∧
    (∀ i, z.2.1.getD i 0 = symN (c.Tape.left.nth i))

theorem tblOf_respects (M : TM0.Machine Γ Λ) (S : Finset Λ) (hS : TM0.Supports M ↑S) :
    Respects (TM0.step M) (zstep (tblOf M S)) (TRel S) := by
  rintro ⟨q, ⟨a, LT, RT⟩⟩ ⟨st, L, R⟩ ⟨hq, hst, hh, hr, hl⟩
  simp only at hst hh hr hl
  have hz : zstep (tblOf M S) (st, L, R) =
      (M q a).map (fun o => mv (rhs (mkQ S q a o)) (st, L, R)) := by
    unfold zstep; simp only; rw [hst, hh, look_tblOf M S hq, Option.map_map]; rfl
  have hstep : TM0.step M ⟨q, ⟨a, LT, RT⟩⟩ = (M q a).map fun o => ⟨o.1, match o.2 with
      | TM0.Stmt.move d => (Tape.mk a LT RT).move d
      | TM0.Stmt.write b => (Tape.mk a LT RT).write b⟩ := by
    simp only [TM0.step]; congr 1
  cases hM : M q a with
  | none =>
    rw [hstep, hM]; simp only [Option.map_none]; rw [hz, hM]; rfl
  | some o =>
    rw [hstep, hM]; simp only [Option.map_some]
    refine ⟨mv (rhs (mkQ S q a o)) (st, L, R), ?_, Relation.TransGen.single (by rw [hz, hM]; rfl)⟩
    have hq' : o.1 ∈ S := hS.2 (show (o.1, o.2) ∈ M q a by rw [hM]; rfl) hq
    obtain ⟨q', stm⟩ := o
    cases stm with
    | move d =>
      cases d with
      | left =>
        refine ⟨hq', rfl, ?_, ?_, ?_⟩
        · show L.headD 0 = symN LT.head
          rw [← getD_zero, hl 0, ListBlank.nth_zero]
        · intro i
          show (L.headD 0 :: symN a :: R.tail).getD (i + 1) 0 = symN ((RT.cons a).nth i)
          cases i with
          | zero => simp [ListBlank.nth_zero]
          | succ j =>
            rw [List.getD_cons_succ, List.getD_cons_succ, getD_tail, hr j, ListBlank.nth_succ,
              ListBlank.tail_cons]
        · intro i
          show L.tail.getD i 0 = symN (LT.tail.nth i)
          rw [getD_tail, hl (i + 1), ListBlank.nth_succ]
      | right =>
        refine ⟨hq', rfl, ?_, ?_, ?_⟩
        · show R.tail.headD 0 = symN RT.head
          rw [← getD_zero, getD_tail, hr 0, ListBlank.nth_zero]
        · intro i
          show R.tail.getD (i + 1) 0 = symN (RT.tail.nth i)
          rw [getD_tail, hr (i + 1), ListBlank.nth_succ]
        · intro i
          show (symN a :: L).getD i 0 = symN ((LT.cons a).nth i)
          cases i with
          | zero => simp [ListBlank.nth_zero]
          | succ j => rw [List.getD_cons_succ, hl j, ListBlank.nth_succ, ListBlank.tail_cons]
    | write b =>
      refine ⟨hq', rfl, rfl, ?_, hl⟩
      intro i
      show R.tail.getD i 0 = symN (RT.nth i)
      rw [getD_tail, hr i]

theorem getD_map_symN (l : List Γ) : ∀ n, (l.map symN).getD n 0 = symN (l.getI n) := by
  induction l with
  | nil => intro n; simp [symN_default]
  | cons a l ih =>
    intro n; cases n with
    | zero => rfl
    | succ n => simp only [List.map_cons, List.getD_cons_succ, List.getI_cons_succ]; exact ih n

theorem init_rel (S : Finset Λ) (hdef : (default : Λ) ∈ S) (l : List Γ) :
    TRel S (TM0.init l) (stN S default, [], l.map symN) := by
  refine ⟨hdef, rfl, ?_, ?_, ?_⟩
  · show (l.map symN).headD 0 = symN (ListBlank.mk l).head
    rw [← getD_zero, getD_map_symN, ListBlank.head_mk]; cases l <;> rfl
  · intro i
    show (l.map symN).getD (i + 1) 0 = symN ((ListBlank.mk l).tail.nth i)
    rw [getD_map_symN, ← ListBlank.nth_succ, ListBlank.nth_mk]
  · intro i
    show ([] : List Nat).getD i 0 = symN ((ListBlank.mk ([] : List Γ)).nth i)
    rw [ListBlank.nth_mk]; simp [symN_default]

/-- **翻訳の正しさ**: TM0 機械 M が入力 l から止まる ⟺ 翻訳した五つ組表が対応する有限 ID から止まる。 -/
theorem tm0_halts_iff (M : TM0.Machine Γ Λ) (S : Finset Λ) (hS : TM0.Supports M ↑S)
    (l : List Γ) :
    (eval (TM0.step M) (TM0.init l)).Dom ↔ ZHalts (tblOf M S) (stN S default, [], l.map symN) := by
  rw [ZHalts_iff_eval]
  exact (tr_eval_dom (tblOf_respects M S hS) (init_rel S hS.1 l)).symm

end Translate

end URTM.Meta
