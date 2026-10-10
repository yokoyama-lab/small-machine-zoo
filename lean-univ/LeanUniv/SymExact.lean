/-
  **Exact symbol counts of the 3-state conversions with one kind of counter** (the values 18476, 1820
  and 659 of the paper's table on the 3-state and 2-symbol conversions).

  `SymCount` gives the improved 3-state conversion only as an upper bound. Here the bound is shown to be
  attained, for every 1WU machine:

  * `conv3P_nsym`: the 3-state conversion with one kind of counter (`Conv3P.conv`, ↑ and ↓ merged, the
    counters of `x` cut at `need x`) has exactly `|syms| + Σ_x need x` symbols, i.e. every symbol of
    `Conv3P.univ` occurs in the table (the counters `[x, 1..need x]` occur in the counting rules, a plain
    symbol occurs in δ3 or δ8). Hypotheses: those of `Conv3P` on the rules (`hS`, shape, `hidx`, `hsrc`),
    the enumeration is duplicate-free, and the blank has at least one counter (if it is enumerated).
  * `shared_nsym` (**↑ and ↓ merged, nothing cut**): with `need x = M − 1` for every symbol, on a 1WU machine
    with the hypotheses of Morita's Lemma 5.10 (`Conv510.Hyp`, states numbered below `M`), exactly `N·M`
    symbols (`N` the symbols of the 1WU machine). For (32,3): `298·62 = 18476`.
  * `conv3S_nsym_eq` / `convM3S_nsym_eq` (**the improved 3-state conversion**, not mirrored / mirrored): with
    the counter bound `need3`, exactly `1 + n + (m₋n + |G|)(n + 1) + n(n + 2 + |R| + |G|) + (n + 2)`.
    For (32,3): 659 (not mirrored) and 600 (mirrored).

  No `sorry`, no new axiom, no `native_decide`.
-/
import LeanUniv.SymCount

namespace URTM.Univ.SymExact

set_option linter.unusedSectionVars false

open URTM URTM.KState
open URTM.Univ.SymCount
open URTM.Conv3P (CSym univ)
open URTM.Conv510 (shapeOK)

/-! ## 1. The 3-state conversion with one kind of counter (`Conv3P.conv`): `|syms| + Σ need` -/

section Conv3P
variable {Q P S : Type} [DecidableEq Q] [DecidableEq S]

/-- The underlying symbol of a symbol of the 3-state machine. -/
def cOwn : CSym S → S
  | .pl s => s
  | .ct s _ => s

theorem univ_nodup {need : S → ℕ} {L : List S} (hL : L.Nodup) : (univ need L).Nodup := by
  unfold univ
  refine List.Nodup.append (hL.map (fun _ _ h => by injection h)) ?_ ?_
  · refine nodup_flatMap_owner cOwn hL (fun x _ => ?_) (fun x _ y hy => ?_)
    · exact List.nodup_range.map (fun a b h => by injection h with _ h; omega)
    · obtain ⟨k, -, rfl⟩ := List.mem_map.1 hy; rfl
  · rw [List.disjoint_left]
    intro a ha hb
    obtain ⟨s, -, rfl⟩ := List.mem_map.1 ha
    obtain ⟨x, -, h⟩ := List.mem_flatMap.1 hb
    obtain ⟨k, -, h⟩ := List.mem_map.1 h
    cases h

/-- **Every symbol of `univ need L` occurs in the 3-state table** (if the blank has a counter). -/
theorem univ_sub_syms {W : Machine Q P S} {qL : Q} {s0 : S} {idx : Q → ℕ} {need : S → ℕ} {L : List S}
    (hs0 : s0 ∈ L → 1 ≤ need s0) {x : CSym S} (hx : x ∈ univ need L) :
    x ∈ syms (Conv3P.conv W qL s0 idx need L) := by
  simp only [univ, List.mem_append, List.mem_map, List.mem_flatMap, List.mem_range] at hx
  rcases hx with ⟨u, hu, rfl⟩ | ⟨u, hu, k, hk, rfl⟩
  · by_cases h1 : 1 ≤ need u
    · exact s_mem_syms (Conv3P.mem_d3 (W := W) (qL := qL) (s0 := s0) (idx := idx) hu h1)
    · have h0 : u ≠ s0 := fun e => h1 (by subst e; exact hs0 hu)
      exact s_mem_syms (Conv3P.mem_d8 (W := W) (qL := qL) (idx := idx) (need := need) hu h0)
  · rcases k with _ | k
    · exact t_mem_syms (Conv3P.mem_d3 (W := W) (qL := qL) (s0 := s0) (idx := idx) hu (by omega))
    · exact s_mem_syms (Conv3P.mem_d4 (W := W) (qL := qL) (s0 := s0) (idx := idx) hu (k := k) (by omega))

/-- **The 3-state conversion with one kind of counter has exactly `|L| + Σ_{x ∈ L} need x` symbols.** -/
theorem conv3P_nsym {W : Machine Q P S} {qL : Q} {s0 : S} {idx : Q → ℕ} {need : S → ℕ} {L : List S}
    (hS : ∀ r ∈ W, r.s ∈ L ∧ r.t ∈ L) (hsh : ∀ r ∈ W, shapeOK qL s0 r = true)
    (hidx : ∀ r ∈ W, ∀ q, r.q = .go q → q ≠ qL → 1 ≤ idx q ∧ idx q ≤ need r.t)
    (hsrc : ∀ r ∈ W, r.p ≠ qL → 1 ≤ idx r.p ∧ idx r.p ≤ need r.s)
    (hL : L.Nodup) (hs0 : s0 ∈ L → 1 ≤ need s0) :
    nsym (Conv3P.conv W qL s0 idx need L) = L.length + (L.map need).sum := by
  rw [← univ_length need L]
  refine nsym_eq_of (univ_nodup hL) (fun x => ⟨fun h => ?_, fun h => univ_sub_syms hs0 h⟩)
  obtain ⟨ρ, hρ, rfl | rfl⟩ := mem_syms.1 h
  · exact (Conv3P.conv_syms hS hsh hidx hsrc ρ hρ).1
  · exact (Conv3P.conv_syms hS hsh hidx hsrc ρ hρ).2

/-- **↑ and ↓ merged, all counters kept** (`need x = M − 1`): on a 1WU machine with the hypotheses of
    Morita's Lemma 5.10 (states other than `q_L` numbered in `1..M−1`), the 3-state machine has exactly
    `N·M` symbols, `N = |L|`. -/
theorem shared_nsym {T : Machine Q P S} {qL : Q} {s0 : S} {idx : Q → ℕ} {m : ℕ} {L : List S}
    (H : Conv510.Hyp T qL s0 idx m L) (hsrc : ∀ r ∈ T, r.p ≠ qL → 1 ≤ idx r.p ∧ idx r.p < m)
    (hL : L.Nodup) (hm : 2 ≤ m) :
    nsym (Conv3P.conv T qL s0 idx (fun _ => m - 1) L) = L.length * m := by
  rw [conv3P_nsym (fun _ _ => ⟨H.hS _, H.hS _⟩) H.hshape
    (fun r hr q hq hqL => by
      have := Conv510.idxOK_spec (H.hidx r hr) hq hqL; exact ⟨this.1, show idx q ≤ m - 1 by omega⟩)
    (fun r hr hp => by have := hsrc r hr hp; exact ⟨this.1, show idx r.p ≤ m - 1 by omega⟩) hL
    (fun _ => show 1 ≤ m - 1 by omega), sum_map_const]
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  ring

end Conv3P

/-! ## 2. The improved 3-state conversion (`Conv3S.conv`, `Conv3S.convM`): the formula is attained -/

section Conv3S
open URTM.Conv1W (VSym VSt)
variable {Q P S : Type} [DecidableEq Q] [DecidableEq S]

theorem wsyms_nodup {ss : List S} {qm : List Q} {Gl : List (Q × S)} (hss : ss.Nodup) (hqm : qm.Nodup)
    (hGl : Gl.Nodup) : (Conv3S.wsyms ss qm Gl).Nodup := by
  refine List.nodup_cons.2 ⟨fun h => Conv1W.allSyms_ne h rfl, ?_⟩
  unfold Conv1W.allSyms
  refine List.Nodup.append (List.Nodup.append ?_ ?_ ?_) ?_ ?_
  · exact hss.map (fun _ _ h => by injection h)
  · refine List.nodup_flatMap.2 ⟨fun p _ => hss.map (fun _ _ h => by injection h),
      hqm.pairwise_of_forall_ne fun a _ b _ hab => ?_⟩
    simp only [Function.onFun]
    rw [List.disjoint_left]
    intro x hx hy
    obtain ⟨s, -, rfl⟩ := List.mem_map.1 hx
    obtain ⟨s', -, h⟩ := List.mem_map.1 hy
    injection h with h1; exact hab h1.symm
  · rw [List.disjoint_left]
    intro x hx hy
    obtain ⟨s, -, rfl⟩ := List.mem_map.1 hx
    obtain ⟨p, -, h⟩ := List.mem_flatMap.1 hy
    obtain ⟨s', -, h⟩ := List.mem_map.1 h
    cases h
  · exact hGl.map (fun a b h => by injection h with h1 h2; exact Prod.ext h1 h2)
  · rw [List.disjoint_left]
    intro x hx hy
    obtain ⟨pv, -, rfl⟩ := List.mem_map.1 hy
    rcases List.mem_append.1 hx with h | h
    · obtain ⟨s, -, h⟩ := List.mem_map.1 h; cases h
    · obtain ⟨p, -, h⟩ := List.mem_flatMap.1 h
      obtain ⟨s', -, h⟩ := List.mem_map.1 h
      cases h

/-- The symbols of a mirrored machine are those of the machine. -/
theorem syms_mirror (M : Machine Q P S) : syms (Conv3Base.mirror M) = syms M := by
  unfold syms Conv3Base.mirror
  induction M with
  | nil => rfl
  | cons r M ih => simp [List.flatMap_cons, ih, Conv3Base.flipR]

theorem nsym_mirror (M : Machine Q P S) : nsym (Conv3Base.mirror M) = nsym M := by
  unfold nsym; rw [syms_mirror]

variable {T : Machine Q P S} {b : S} {ss : List S} {qm : List Q} {Rl Gl : List (Q × S)}
  {idx : VSt Q S → ℕ} {need : VSym Q S → ℕ}

/-- **The improved 3-state conversion (not mirrored) has exactly**
    `1 + n + (m₋n + |G|)(n + 1) + n(n + 2 + |R| + |G|) + (n + 2)` **symbols** when the counter bound is
    `need3` (`n = |ss|`, `m₋ = |qm|`, `|R| = |Rl|`, `|G| = |Gl|`; the enumerations duplicate-free). -/
theorem conv3S_nsym_eq (H : Conv3S.Hyp T b ss qm Rl Gl idx need)
    (hsrc : ∀ r ∈ Conv1W.conv T b ss qm Rl Gl, r.p ≠ .L → 1 ≤ idx r.p ∧ idx r.p ≤ need r.s)
    (hneed : ∀ x ∈ Conv3S.wsyms ss qm Gl, need x = need3 ss.length Rl.length Gl.length x)
    (hss : ss.Nodup) (hqm : qm.Nodup) (hGl : Gl.Nodup) :
    nsym (Conv3S.conv T b ss qm Rl Gl idx need) =
      1 + ss.length + (qm.length * ss.length + Gl.length) * (ss.length + 1) +
        ss.length * (ss.length + 2 + Rl.length + Gl.length) + (ss.length + 2) := by
  have hbl : need .bl = ss.length + 2 := hneed _ Conv3S.bl_mem
  unfold Conv3S.conv
  rw [conv3P_nsym (fun _ h => Conv3S.w_syms H h) (fun _ h => Conv3S.w_shape h) H.hidx hsrc
    (wsyms_nodup hss hqm hGl) (fun _ => by omega), ← univ_length, univ_congr hneed, univ_need3_length]

/-- **The same for the mirrored conversion** (the form of (3,600)). -/
theorem convM3S_nsym_eq (H : Conv3S.Hyp (Conv3Base.mirror T) b ss qm Rl Gl idx need)
    (hsrc : ∀ r ∈ Conv1W.conv (Conv3Base.mirror T) b ss qm Rl Gl, r.p ≠ .L → 1 ≤ idx r.p ∧ idx r.p ≤ need r.s)
    (hneed : ∀ x ∈ Conv3S.wsyms ss qm Gl, need x = need3 ss.length Rl.length Gl.length x)
    (hss : ss.Nodup) (hqm : qm.Nodup) (hGl : Gl.Nodup) :
    nsym (Conv3S.convM T b ss qm Rl Gl idx need) =
      1 + ss.length + (qm.length * ss.length + Gl.length) * (ss.length + 1) +
        ss.length * (ss.length + 2 + Rl.length + Gl.length) + (ss.length + 2) := by
  unfold Conv3S.convM
  rw [nsym_mirror]
  exact conv3S_nsym_eq H hsrc hneed hss hqm hGl

end Conv3S

end URTM.Univ.SymExact
