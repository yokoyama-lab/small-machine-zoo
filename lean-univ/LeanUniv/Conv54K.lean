/-
  **Morita's 2-symbol conversion (Theorem 5.4) with `k`-bit codes, and its number of states.**

  `URTM.Conv54` is the 2-bit case. Here the conversion is written for any code length `k ≥ 2`
  (`code s` a list of `k` bits; the construction is the one of `tools/fewsym.py`, mode `morita`,
  orientation `L` for every state):

      δr : [[p^r, x₁⋯x_i], x_{i+1}, 0, +, [p^r, x₁⋯x_{i+1}]]               (0 ≤ i < k − 1)
      δt : [[p^r, c₁(s)⋯c_{k−1}(s)], c_k(s), c_k(t), −, [q^w, c₁(t)⋯c_{k−1}(t)]]
      δw : [[q^w, c₁(t)⋯c_i(t)], 0, c_i(t), −, [q^w, c₁(t)⋯c_{i−1}(t)]]    (2 ≤ i ≤ k − 1)
           [[q^w, c₁(t)], 0, c₁(t), hsd(q), [q^s, 1]]
      δs : [[q^s, j], x, x, hsd(q), [q^s, j + 1]]  (1 ≤ j < k − 1),   [[q^s, k − 1], x, x, hsd(q), [q^r]]

  for every rule `[p, s, t, d, q]` of `T` into a real state (the halting rules are not converted), and
  `hsd(q)` the direction of the rules into `q`. As in `Conv54`, only the rules that can be used are listed
  (δr and δw are made from the rules of `T`); δs is listed for every state of `qs` (`tools/fewsym.py` lists it
  only for the states entered by a rule; for (13,7) these are all 13 states, so the two agree there).
  The state `[p^r, x₁⋯x_i]` is `.r p [x₁, …, x_i]`, `[q^w, y₁⋯y_i]` is `.w q [y₁, …, y_i]`, `[q^s, j]` is `.s q j`.

  **Number of states** (`conv_nst`, `nst` counts the current states of the rules, as `Spec.NStates`):

      |D_go| + (k − 1)·m + P_r + P_w   ≤   m·k + P_r + P_w      (Morita's formula)

  where `D_go` are the states with a rule into a real state, `m = |qs|`, and `P_r` (`pRK`) / `P_w` (`pWK`)
  are the numbers of pairs (state, prefix of length `1..k−1` of a code it reads) / (state, prefix of length
  `1..k−1` of a code written when entering it). For `k = 2` this is `SymCount.conv54_nst`.

  `numCode ss k` is Morita's code (the `i`-th symbol of `ss` gets the `k`-bit binary numeral of `i`, most
  significant bit first; the blank, first in `ss`, gets `0^k`).

  No `sorry`, no new axiom, no `native_decide`.
-/
import LeanUniv.SymCount

namespace URTM.Univ.Conv54K

set_option linter.unusedSectionVars false

open URTM URTM.KState
open URTM.Univ.SymCount (nst nst_eq_of goFrom isTo dGo)

/-- The states of the converted machine: `[p^r, prefix]`, `[q^w, prefix]`, `[q^s, j]`. -/
inductive KSt (Q : Type) where
  | r (q : Q) (pre : List Bool)
  | w (q : Q) (pre : List Bool)
  | s (q : Q) (j : ℕ)
  deriving DecidableEq, Repr

section Def
variable {Q P S : Type} [DecidableEq Q]

/-- `hsd(q)`: the direction of the (first) rule into `q` (`R` if there is none). -/
def hsd (T : Machine Q P S) (q : Q) : Dir :=
  match T.find? (fun r => isTo r q) with
  | some r => r.d
  | none => .R

/-- The `i`-th bit of a code (`false` past its end). -/
def bit (c : List Bool) (i : ℕ) : Bool := c.getD i false

/-- δr of a rule: read the first `k − 1` bits of the code of the read symbol, writing `0`. -/
def rRules (code : S → List Bool) (k : ℕ) (r : Rule Q P S) : List (Rule (KSt Q) P Bool) :=
  match r.q with
  | .go _ => (List.range (k - 1)).map fun i =>
      ⟨.r r.p ((code r.s).take i), bit (code r.s) i, false, .R, .go (.r r.p ((code r.s).take (i + 1)))⟩
  | .halt _ => []

/-- δt of a rule: read the last bit, write the last bit of the written symbol, turn back. -/
def tRules (code : S → List Bool) (k : ℕ) (r : Rule Q P S) : List (Rule (KSt Q) P Bool) :=
  match r.q with
  | .go q => [⟨.r r.p ((code r.s).take (k - 1)), bit (code r.s) (k - 1), bit (code r.t) (k - 1), .L,
      .go (.w q ((code r.t).take (k - 1)))⟩]
  | .halt _ => []

/-- δw of a rule: write back the first `k − 1` bits of the written symbol; the last one leaves towards `hsd(q)`. -/
def wRules (T : Machine Q P S) (code : S → List Bool) (k : ℕ) (r : Rule Q P S) : List (Rule (KSt Q) P Bool) :=
  match r.q with
  | .go q => (List.range (k - 1)).map fun j =>
      ⟨.w q ((code r.t).take (j + 1)), false, bit (code r.t) j, if j = 0 then hsd T q else .L,
        .go (if j = 0 then .s q 1 else .w q ((code r.t).take j))⟩
  | .halt _ => []

/-- δs of a state: `k − 1` more moves towards `hsd(q)`, ending in `[q^r]`. -/
def sRules (T : Machine Q P S) (k : ℕ) (q : Q) : List (Rule (KSt Q) P Bool) :=
  (List.range (k - 1)).flatMap fun j => [false, true].map fun b =>
    ⟨.s q (j + 1), b, b, hsd T q, .go (if j + 2 = k then .r q [] else .s q (j + 2))⟩

/-- **Theorem 5.4 with `k`-bit codes** (the rules that can be used). -/
def conv (T : Machine Q P S) (code : S → List Bool) (k : ℕ) (qs : List Q) : Machine (KSt Q) P Bool :=
  T.flatMap (rRules code k) ++ T.flatMap (tRules code k) ++ T.flatMap (wRules T code k) ++
    qs.flatMap (sRules T k)

/-- The prefixes of length `1..k−1` of a code. -/
def prefs (k : ℕ) (c : List Bool) : List (List Bool) := (List.range (k - 1)).map fun j => c.take (j + 1)

/-- (state, prefix of a code it reads), with repetitions. -/
def rdPairs (T : Machine Q P S) (code : S → List Bool) (k : ℕ) : List (Q × List Bool) :=
  T.flatMap fun r => match r.q with
    | .go _ => (prefs k (code r.s)).map fun pre => (r.p, pre)
    | .halt _ => []

/-- (state, prefix of a code written when entering it), with repetitions. -/
def wrPairs (T : Machine Q P S) (code : S → List Bool) (k : ℕ) : List (Q × List Bool) :=
  T.flatMap fun r => match r.q with
    | .go q => (prefs k (code r.t)).map fun pre => (q, pre)
    | .halt _ => []

/-- **`P_r`**: the pairs (state, prefix of length `1..k−1` of a code it reads). -/
def pRK (T : Machine Q P S) (code : S → List Bool) (k : ℕ) : List (Q × List Bool) := (rdPairs T code k).dedup
/-- **`P_w`**: the pairs (state, prefix of length `1..k−1` of a code written when entering it). -/
def pWK (T : Machine Q P S) (code : S → List Bool) (k : ℕ) : List (Q × List Bool) := (wrPairs T code k).dedup

/-- The current states of the converted machine. -/
def sList (T : Machine Q P S) (code : S → List Bool) (k : ℕ) (qs : List Q) : List (KSt Q) :=
  (dGo T qs).map (fun p => .r p []) ++ (pRK T code k).map (fun a => .r a.1 a.2) ++
    (pWK T code k).map (fun a => .w a.1 a.2) ++
    qs.flatMap (fun q => (List.range (k - 1)).map fun j => .s q (j + 1))

end Def

/-- **Morita's code**: the `k`-bit binary numeral (most significant bit first) of the position in `ss`. -/
def numCode {S : Type} [DecidableEq S] (ss : List S) (k : ℕ) (s : S) : List Bool :=
  (List.range k).reverse.map fun j => (ss.idxOf s).testBit j

/-! ## The number of states -/

section Count
variable {Q P S : Type} [DecidableEq Q] {T : Machine Q P S} {code : S → List Bool} {k : ℕ} {qs : List Q}

theorem mem_rdPairs {a : Q × List Bool} :
    a ∈ rdPairs T code k ↔ ∃ r ∈ T, r.q.isGo = true ∧ ∃ j, j < k - 1 ∧ a = (r.p, (code r.s).take (j + 1)) := by
  unfold rdPairs
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨r, hr, h⟩
    cases hq : r.q with
    | halt _ => rw [hq] at h; simp at h
    | go q =>
      rw [hq] at h
      simp only [prefs, List.mem_map, List.mem_range] at h
      obtain ⟨_, ⟨j, hj, rfl⟩, rfl⟩ := h
      exact ⟨r, hr, by simp [hq, Tgt.isGo], j, hj, rfl⟩
  · rintro ⟨r, hr, hg, j, hj, rfl⟩
    refine ⟨r, hr, ?_⟩
    cases hq : r.q with
    | halt _ => rw [hq] at hg; cases hg
    | go q => simp only [prefs, List.mem_map, List.mem_range]; exact ⟨_, ⟨j, hj, rfl⟩, rfl⟩

theorem mem_wrPairs {a : Q × List Bool} :
    a ∈ wrPairs T code k ↔ ∃ r ∈ T, ∃ q, r.q = .go q ∧ ∃ j, j < k - 1 ∧ a = (q, (code r.t).take (j + 1)) := by
  unfold wrPairs
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨r, hr, h⟩
    cases hq : r.q with
    | halt _ => rw [hq] at h; simp at h
    | go q =>
      rw [hq] at h
      simp only [prefs, List.mem_map, List.mem_range] at h
      obtain ⟨_, ⟨j, hj, rfl⟩, rfl⟩ := h
      exact ⟨r, hr, q, hq, j, hj, rfl⟩
  · rintro ⟨r, hr, q, hq, j, hj, rfl⟩
    refine ⟨r, hr, ?_⟩
    rw [hq]; simp only [prefs, List.mem_map, List.mem_range]; exact ⟨_, ⟨j, hj, rfl⟩, rfl⟩

theorem mem_dGo (hQ : ∀ q, q ∈ qs) {p : Q} : p ∈ dGo T qs ↔ goFrom T p = true := by
  simp [dGo, hQ p]

theorem goFrom_iff {p : Q} : goFrom T p = true ↔ ∃ r ∈ T, r.p = p ∧ r.q.isGo = true := by
  simp [goFrom, List.any_eq_true]

theorem take_ne_nil (hk : 2 ≤ k) (hlen : ∀ s, (code s).length = k) (s : S) {j : ℕ} :
    (code s).take (j + 1) ≠ [] := by
  intro h
  have h1 : ((code s).take (j + 1)).length = 0 := by rw [h]; rfl
  rw [List.length_take, hlen] at h1
  omega

theorem sList_nodup (hk : 2 ≤ k) (hlen : ∀ s, (code s).length = k) (hqs : qs.Nodup) :
    (sList T code k qs).Nodup := by
  unfold sList
  refine List.Nodup.append (List.Nodup.append (List.Nodup.append ?_ ?_ ?_) ?_ ?_) ?_ ?_
  · exact (hqs.filter _).map (fun _ _ h => by injection h)
  · exact (List.nodup_dedup _).map (fun a b h => by injection h with h1 h2; exact Prod.ext h1 h2)
  · rw [List.disjoint_left]
    intro x hx hy
    obtain ⟨p, -, rfl⟩ := List.mem_map.1 hx
    obtain ⟨a, ha, h⟩ := List.mem_map.1 hy
    injection h with _ h2
    obtain ⟨r, -, -, j, -, rfl⟩ := mem_rdPairs.1 (List.mem_dedup.1 ha)
    exact take_ne_nil hk hlen r.s h2
  · exact (List.nodup_dedup _).map (fun a b h => by injection h with h1 h2; exact Prod.ext h1 h2)
  · rw [List.disjoint_left]
    intro x hx hy
    obtain ⟨a, -, rfl⟩ := List.mem_map.1 hy
    rcases List.mem_append.1 hx with h | h
    · obtain ⟨p, -, h⟩ := List.mem_map.1 h; cases h
    · obtain ⟨b, -, h⟩ := List.mem_map.1 h; cases h
  · refine List.nodup_flatMap.2 ⟨fun q _ => List.nodup_range.map (fun a b h => by injection h with _ h; omega),
      hqs.pairwise_of_forall_ne fun a _ b _ hab => ?_⟩
    simp only [Function.onFun]
    rw [List.disjoint_left]
    intro x hx hy
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
    obtain ⟨j, -, h⟩ := List.mem_map.1 hy
    injection h with h1; exact hab h1.symm
  · rw [List.disjoint_left]
    intro x hx hy
    obtain ⟨q, -, h⟩ := List.mem_flatMap.1 hy
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 h
    rcases List.mem_append.1 hx with h | h
    · rcases List.mem_append.1 h with h | h
      · obtain ⟨p, -, h⟩ := List.mem_map.1 h; cases h
      · obtain ⟨b, -, h⟩ := List.mem_map.1 h; cases h
    · obtain ⟨b, -, h⟩ := List.mem_map.1 h; cases h

/-- The current states of the rules are exactly `sList`. -/
theorem src_iff (hk : 2 ≤ k) (hQ : ∀ q, q ∈ qs) {x : KSt Q} :
    (∃ ρ ∈ conv T code k qs, ρ.p = x) ↔ x ∈ sList T code k qs := by
  simp only [sList, List.mem_append, List.mem_map, List.mem_flatMap, List.mem_range, mem_dGo hQ]
  constructor
  · rintro ⟨ρ, hρ, rfl⟩
    simp only [conv, List.mem_append, List.mem_flatMap] at hρ
    rcases hρ with ((⟨r, hr, h⟩ | ⟨r, hr, h⟩) | ⟨r, hr, h⟩) | ⟨q, -, h⟩
    · cases hq : r.q with
      | halt _ => rw [rRules, hq] at h; simp at h
      | go q =>
        rw [rRules, hq] at h
        simp only [List.mem_map, List.mem_range] at h
        obtain ⟨i, hi, rfl⟩ := h
        rcases i with _ | i
        · exact .inl (.inl (.inl ⟨r.p, goFrom_iff.2 ⟨r, hr, rfl, by simp [hq, Tgt.isGo]⟩, rfl⟩))
        · refine .inl (.inl (.inr ⟨(r.p, (code r.s).take (i + 1)), List.mem_dedup.2 ?_, rfl⟩))
          exact mem_rdPairs.2 ⟨r, hr, by simp [hq, Tgt.isGo], i, by omega, rfl⟩
    · cases hq : r.q with
      | halt _ => rw [tRules, hq] at h; simp at h
      | go q =>
        rw [tRules, hq] at h
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        subst h
        refine .inl (.inl (.inr ⟨(r.p, (code r.s).take (k - 1)), List.mem_dedup.2 ?_, rfl⟩))
        refine mem_rdPairs.2 ⟨r, hr, by simp [hq, Tgt.isGo], k - 2, by omega, ?_⟩
        rw [show k - 2 + 1 = k - 1 by omega]
    · cases hq : r.q with
      | halt _ => rw [wRules, hq] at h; simp at h
      | go q =>
        rw [wRules, hq] at h
        simp only [List.mem_map, List.mem_range] at h
        obtain ⟨j, hj, rfl⟩ := h
        exact .inl (.inr ⟨(q, (code r.t).take (j + 1)),
          List.mem_dedup.2 (mem_wrPairs.2 ⟨r, hr, q, hq, j, hj, rfl⟩), rfl⟩)
    · simp only [sRules, List.mem_flatMap, List.mem_range, List.mem_map, List.mem_cons, List.not_mem_nil,
        or_false] at h
      obtain ⟨j, hj, b, -, rfl⟩ := h
      exact .inr ⟨q, hQ q, j, hj, rfl⟩
  · rintro (((⟨p, hp, rfl⟩ | ⟨a, ha, rfl⟩) | ⟨a, ha, rfl⟩) | ⟨q, -, j, hj, rfl⟩)
    · obtain ⟨r, hr, rfl, hg⟩ := goFrom_iff.1 hp
      cases hq : r.q with
      | halt _ => rw [hq] at hg; cases hg
      | go q =>
        refine ⟨⟨.r r.p ((code r.s).take 0), bit (code r.s) 0, false, .R, .go (.r r.p ((code r.s).take (0 + 1)))⟩,
          ?_, rfl⟩
        simp only [conv, List.mem_append, List.mem_flatMap]
        refine .inl (.inl (.inl ⟨r, hr, ?_⟩))
        rw [rRules, hq]
        exact List.mem_map.2 ⟨0, List.mem_range.2 (by omega), rfl⟩
    · obtain ⟨r, hr, hg, j, hj, rfl⟩ := mem_rdPairs.1 (List.mem_dedup.1 ha)
      cases hq : r.q with
      | halt _ => rw [hq] at hg; cases hg
      | go q =>
        by_cases hjk : j + 1 < k - 1
        · refine ⟨⟨.r r.p ((code r.s).take (j + 1)), bit (code r.s) (j + 1), false, .R,
            .go (.r r.p ((code r.s).take (j + 1 + 1)))⟩, ?_, rfl⟩
          simp only [conv, List.mem_append, List.mem_flatMap]
          refine .inl (.inl (.inl ⟨r, hr, ?_⟩))
          rw [rRules, hq]
          exact List.mem_map.2 ⟨j + 1, List.mem_range.2 hjk, rfl⟩
        · have hkj : k - 1 = j + 1 := by omega
          refine ⟨⟨.r r.p ((code r.s).take (k - 1)), bit (code r.s) (k - 1), bit (code r.t) (k - 1), .L,
            .go (.w q ((code r.t).take (k - 1)))⟩, ?_, by simp [hkj]⟩
          simp only [conv, List.mem_append, List.mem_flatMap]
          refine .inl (.inl (.inr ⟨r, hr, ?_⟩))
          rw [tRules, hq]
          exact List.mem_cons_self
    · obtain ⟨r, hr, q, hq, j, hj, rfl⟩ := mem_wrPairs.1 (List.mem_dedup.1 ha)
      refine ⟨⟨.w q ((code r.t).take (j + 1)), false, bit (code r.t) j, if j = 0 then hsd T q else .L,
        .go (if j = 0 then .s q 1 else .w q ((code r.t).take j))⟩, ?_, rfl⟩
      simp only [conv, List.mem_append, List.mem_flatMap]
      refine .inl (.inr ⟨r, hr, ?_⟩)
      rw [wRules, hq]
      exact List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩
    · refine ⟨⟨.s q (j + 1), false, false, hsd T q, .go (if j + 2 = k then .r q [] else .s q (j + 2))⟩, ?_, rfl⟩
      simp only [conv, List.mem_append, List.mem_flatMap]
      refine .inr ⟨q, hQ q, ?_⟩
      simp only [sRules, List.mem_flatMap, List.mem_range, List.mem_map, List.mem_cons, List.not_mem_nil,
        or_false]
      exact ⟨j, hj, false, .inl rfl, rfl⟩

/-- **Number of states of Morita's 2-symbol conversion with `k`-bit codes**:
    `|D_go| + (k − 1)·m + P_r + P_w` (`m = |qs|`). -/
theorem conv_nst (hk : 2 ≤ k) (hlen : ∀ s, (code s).length = k) (hQ : ∀ q, q ∈ qs) (hqs : qs.Nodup) :
    nst (conv T code k qs) =
      (dGo T qs).length + (k - 1) * qs.length + (pRK T code k).length + (pWK T code k).length := by
  have hlen' : (sList T code k qs).length =
      (dGo T qs).length + (k - 1) * qs.length + (pRK T code k).length + (pWK T code k).length := by
    simp only [sList, List.length_append, List.length_map, List.length_flatMap, List.length_range,
      SymCount.sum_map_const]
    ring
  rw [← hlen']
  exact nst_eq_of (sList_nodup hk hlen hqs) (fun x => src_iff hk hQ)

/-- **Morita's formula as a bound**: `m·k + P_r + P_w` (equality when every state has a rule into a real
    state). -/
theorem conv_nst_le (hk : 2 ≤ k) (hlen : ∀ s, (code s).length = k) (hQ : ∀ q, q ∈ qs) (hqs : qs.Nodup) :
    nst (conv T code k qs) ≤ qs.length * k + (pRK T code k).length + (pWK T code k).length := by
  rw [conv_nst hk hlen hQ hqs]
  have : (dGo T qs).length ≤ qs.length := List.length_filter_le _ _
  have : (k - 1) * qs.length + qs.length = qs.length * k := by
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [Nat.add_sub_cancel]; ring
  omega

end Count

end URTM.Univ.Conv54K
