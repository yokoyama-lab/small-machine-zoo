/-
  **2 状態 URTM は存在しない**（Morita 2017 の未解決問題 B3、p.200）と、
  **1 テープ 2 状態 RTM のクラスは計算万能でない**（B2、p.155）の機械証明。

  Morita Def. 7.1（UTM）: 全域再帰的な c : ℕ × I → ID(U)、d : ID(U) → I ∪ {⊥} があって、
    Tₙ が α から止まるなら U は c(n,α) から止まり d で結果が戻る。
    Tₙ が α から止まらないなら U も c(n,α) から止まらない。
  ここでは Tₙ の列挙として Mathlib の部分再帰関数のコード `Nat.Partrec.Code`
  （標準の Gödel 番号付け）を、入力 α として ℕ を使う。「全域再帰的」は Mathlib の `Computable`。
  U の ID は有限 ID（`ZID`）。

  証明: 2 状態 RTM の停止は計算可能に判定できる（`halting_computable`）。
  c で引き戻すと部分再帰関数の停止問題が判定できてしまい、`ComputablePred.halting_problem` に反する。
-/
import URTMMeta.Computable

namespace URTM.Meta
open URTM URTM.TwoState
open Nat.Partrec (Code)

theorem zrun_stop (tbl : List Quint) :
    ∀ n (z₀ z : ZID), zrun tbl n z₀ = some z → zstep tbl z = none → zrun tbl (n + 1) z₀ = none
  | 0, z₀, z, h, hs => by
    simp only [zrun, Option.some.injEq] at h; subst h; simp [zrun, hs]
  | n + 1, z₀, z, h, hs => by
    unfold zrun at h ⊢
    cases h' : zstep tbl z₀ with
    | none => rfl
    | some z' => rw [h'] at h; exact zrun_stop tbl n z' z h hs

/-- U が止まって配置 z に着く。 -/
def ZHaltsAt (tbl : List Quint) (z₀ z : ZID) : Prop :=
  ∃ n, zrun tbl n z₀ = some z ∧ zstep tbl z = none

theorem ZHalts_of_at {tbl : List Quint} {z₀ z : ZID} (h : ZHaltsAt tbl z₀ z) : ZHalts tbl z₀ := by
  obtain ⟨n, h1, h2⟩ := h
  exact ⟨n + 1, zrun_stop tbl n z₀ z h1 h2⟩

/-- **Morita Def. 5.8（模倣）**: 表 tbl の機械が、入力 α の型の「系」を模倣する。
    `Halt a` は系が a から止まって値 `Val a` を返すこと（止まらなければ `Halt a` が偽）。 -/
def Simulates (tbl : List Quint) {α : Type} [Primcodable α] (sys : α → Part ℕ) : Prop :=
  ∃ (c : α → ZID) (d : ZID → ℕ), Computable c ∧ Computable d ∧
    (∀ a v, v ∈ sys a → ∃ z, ZHaltsAt tbl (c a) z ∧ d z = v) ∧
    (∀ a, ¬ (sys a).Dom → ¬ ZHalts tbl (c a))

/-- **Morita Def. 7.1（UTM）**: すべての部分再帰関数（コード T）とその入力 x を模倣する。 -/
def IsUTM (tbl : List Quint) : Prop := Simulates tbl (fun p : Code × ℕ => p.1.eval p.2)

/-- 模倣は停止を保つ。 -/
theorem Simulates.halts_iff {tbl : List Quint} {α : Type} [Primcodable α] {sys : α → Part ℕ}
    {c : α → ZID} {d : ZID → ℕ}
    (hh : ∀ a v, v ∈ sys a → ∃ z, ZHaltsAt tbl (c a) z ∧ d z = v)
    (hn : ∀ a, ¬ (sys a).Dom → ¬ ZHalts tbl (c a)) (a : α) :
    (sys a).Dom ↔ ZHalts tbl (c a) := by
  constructor
  · intro h
    obtain ⟨z, hz, _⟩ := hh a ((sys a).get h) (Part.get_mem h)
    exact ZHalts_of_at hz
  · intro h
    by_contra h'
    exact hn a h' h

/-- **核の定理**: 2 状態 RTM が（Def. 5.8 の意味で）模倣できる系は、停止が計算可能に判定できる。 -/
theorem sim_halting_computable {tbl : List Quint} {q₀ q₁ qf : Nat} (hT : TwoStateRTM tbl q₀ q₁ qf)
    {α : Type} [Primcodable α] {sys : α → Part ℕ} (hs : Simulates tbl sys) :
    ComputablePred fun a => (sys a).Dom := by
  obtain ⟨c, d, hc, _, hh, hn⟩ := hs
  obtain ⟨f, hf, hfe⟩ := ComputablePred.computable_iff.mp (halting_computable hT)
  refine ComputablePred.computable_iff.mpr ⟨fun a => f (c a), hf.comp hc, ?_⟩
  funext a
  apply propext
  rw [Simulates.halts_iff hh hn a]
  exact iff_of_eq (congrFun hfe (c a))

/-- **B1 の核**: 停止が決定不能な系は、どの 2 状態 RTM にも模倣できない。 -/
theorem not_simulates_of_undecidable {α : Type} [Primcodable α] {sys : α → Part ℕ}
    (hund : ¬ ComputablePred fun a => (sys a).Dom)
    {tbl : List Quint} {q₀ q₁ qf : Nat} (hT : TwoStateRTM tbl q₀ q₁ qf) : ¬ Simulates tbl sys :=
  fun hs => hund (sim_halting_computable hT hs)

/-- **定理（Morita B3 の否定的解決）: 2 状態 URTM は存在しない。**
    q₀, q₁ の 2 状態（加えて停止用の疑似状態 qf を許す）で、決定的かつ可逆（Def. 5.4）な
    1 テープ五つ組 TM は、Def. 7.1 の意味で万能になれない。 -/
theorem no_two_state_URTM (tbl : List Quint) (q₀ q₁ qf : Nat) (hT : TwoStateRTM tbl q₀ q₁ qf) :
    ¬ IsUTM tbl := by
  intro hU
  have h := sim_halting_computable hT hU
  -- 入力 0 に固定すれば `ComputablePred.halting_problem 0` に反する
  apply ComputablePred.halting_problem 0
  obtain ⟨f, hf, hfe⟩ := ComputablePred.computable_iff.mp h
  refine ComputablePred.computable_iff.mpr
    ⟨fun T => f (T, 0), hf.comp (Computable.pair Computable.id (Computable.const 0)), ?_⟩
  funext T
  exact congrFun hfe (T, 0)

/-- 停止が決定不能な 1 入力の部分再帰関数のコード（x ↦ ⟦x⟧(0)）。 -/
theorem exists_undecidable_code :
    ∃ U : Code, ¬ ComputablePred fun x : ℕ => (U.eval x).Dom := by
  have hp : Partrec fun x : ℕ => (Denumerable.ofNat Code x).eval 0 :=
    Code.eval_part.comp (Computable.ofNat Code) (Computable.const 0)
  obtain ⟨U, hU⟩ := Code.exists_code.mp (Partrec.nat_iff.mp hp)
  refine ⟨U, fun h => ComputablePred.halting_problem 0 ?_⟩
  obtain ⟨f, hf, hfe⟩ := ComputablePred.computable_iff.mp h
  refine ComputablePred.computable_iff.mpr ⟨fun T => f (Encodable.encode T),
    hf.comp Computable.encode, ?_⟩
  funext T
  have := congrFun hfe (Encodable.encode T)
  rw [hU] at this
  simpa [Denumerable.ofNat_encode] using this

/-- **定理（Morita B2 の否定的解決）: 1 テープ 2 状態 RTM のクラスは計算万能でない**（Def. 5.9）。
    ある部分再帰関数は、どの 2 状態 RTM にも模倣されない。 -/
theorem two_state_class_not_universal :
    ∃ U : Code, ∀ (tbl : List Quint) (q₀ q₁ qf : Nat), TwoStateRTM tbl q₀ q₁ qf →
      ¬ Simulates tbl (fun x : ℕ => U.eval x) := by
  obtain ⟨U, hU⟩ := exists_undecidable_code
  exact ⟨U, fun tbl q₀ q₁ qf hT => not_simulates_of_undecidable hU hT⟩

end URTM.Meta
