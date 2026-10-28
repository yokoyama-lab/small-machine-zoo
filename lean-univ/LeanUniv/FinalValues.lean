/-
  **The values of the paper's table on the 3-state and 2-symbol conversions that were not yet checked in
  Lean**: 169, 149, 135, 92 (the 2-symbol conversion of (13,7), 3-bit codes) and 18476, 1820, 659 (the
  3-state conversion of (32,3)); and 600 as an equality.

  The general formulas (for every source machine) are restated first so that their statements are pinned:

  * `morita2k_formula` (169, 149): Morita's 2-symbol conversion with `k`-bit codes (`Conv54K.conv`) has exactly
    `|D_go| + (k − 1)·m + P_r + P_w` states, at most Morita's `m·k + P_r + P_w`.
  * `conv3P_formula` (1820): the 3-state conversion with ↑ and ↓ merged and the counters cut at `need`
    (`Conv3P.conv`) has exactly `N + Σ_x need x` symbols.
  * `shared_formula` (18476): with every counter kept (`need x = M − 1`), on a 1WU machine with the
    hypotheses of Morita's Lemma 5.10, exactly `N·M`.
  * `three_formula_eq` (659, 600): the improved 3-state conversion has exactly
    `1 + n + (m₋n + |G|)(n + 1) + n(n + 2 + |R| + |G|) + (n + 2)` symbols (not mirrored and mirrored).

  Then the values (each an equality; how each was obtained is stated in its docstring):

  * `morita2_13_7` (169) and `codeopt2_13_7` (149): the Lean conversion applied to (13,7) with Morita's code and
    with the code found by search; the converted machines are deterministic, reversible and simulate every
    CTSH (`Values13_7.Sim13`).
  * `fewsym135_13_7` (135) and `fewsym92_13_7` (92): the tables of the record `urtm13-7.2` before and after
    merging, imported from the generator (the written values, path types and merging were chosen by
    CP-SAT outside Lean); both simulate every CTSH, and the 92-state table is the image of the 135-state
    table under a renaming of the states.
  * `shared3_32_3` (18476), `pruned3_32_3` (1820): Morita's 1WU machine of (32,3) with the 3-state conversion
    with one kind of counter; for 1820 the numbering and `need` are imported from the generator. The 18476
    machine simulates every CTSH (`URTM.CTSH.U3_18476.urtm3_18476_simulates_ctsh` in
    `lean/URTM/CTSH3_18476Main.lean`); for 1820 only the number of symbols is claimed.
  * `three_32_3_659` (659): the improved 3-state conversion, not mirrored; it simulates every CTSH
    (`Sim3_659`, the composition of `CTSH3_600Main` without the mirror).
  * `three_32_3_600_eq` (600): the mirrored conversion, as an equality (`FinalFormulas.three_32_3` gave the bound).

  No `sorry`, no new axiom, no `native_decide`.
-/
import LeanUniv.SymExact
import LeanUniv.Conv54K
import LeanUniv.Values13_7
import LeanUniv.Values32_3
import LeanUniv.Sim3_659

set_option maxRecDepth 100000
set_option linter.unusedSectionVars false

namespace URTM.Univ.FinalValues

open URTM URTM.KState
open URTM.Univ.SymCount (nsym nst dGo need3)

/-! ## The general formulas (restated here so that their statements are pinned) -/

section General
variable {Q P S : Type} [DecidableEq Q] [DecidableEq S]

omit [DecidableEq S] in
/-- **Morita's 2-symbol conversion with `k`-bit codes, for every `T`**: `|D_go| + (k − 1)·m + P_r + P_w`
    states, at most `m·k + P_r + P_w`. -/
theorem morita2k_formula (T : Machine Q P S) (code : S → List Bool) (k : ℕ) (qs : List Q) (hk : 2 ≤ k)
    (hlen : ∀ s, (code s).length = k) (hQ : ∀ q, q ∈ qs) (hqs : qs.Nodup) :
    nst (Conv54K.conv T code k qs) =
      (dGo T qs).length + (k - 1) * qs.length + (Conv54K.pRK T code k).length + (Conv54K.pWK T code k).length ∧
    nst (Conv54K.conv T code k qs) ≤ qs.length * k + (Conv54K.pRK T code k).length + (Conv54K.pWK T code k).length :=
  ⟨Conv54K.conv_nst hk hlen hQ hqs, Conv54K.conv_nst_le hk hlen hQ hqs⟩

/-- **The 3-state conversion with one kind of counter, for every 1WU machine `W`**: `N + Σ_x need x` symbols. -/
theorem conv3P_formula (W : Machine Q P S) (qL : Q) (s0 : S) (idx : Q → ℕ) (need : S → ℕ) (L : List S)
    (H : Conv3P.Hyp W qL s0 idx need L) (hsrc : ∀ r ∈ W, r.p ≠ qL → 1 ≤ idx r.p ∧ idx r.p ≤ need r.s)
    (hL : L.Nodup) (hs0 : s0 ∈ L → 1 ≤ need s0) :
    nsym (Conv3P.conv W qL s0 idx need L) = L.length + (L.map need).sum :=
  SymExact.conv3P_nsym H.hS H.hshape H.hidx hsrc hL hs0

/-- **↑ and ↓ merged, every counter kept, for every 1WU machine with the hypotheses of Lemma 5.10**: `N·M`. -/
theorem shared_formula (T : Machine Q P S) (qL : Q) (s0 : S) (idx : Q → ℕ) (m : ℕ) (L : List S)
    (H : Conv510.Hyp T qL s0 idx m L) (hsrc : ∀ r ∈ T, r.p ≠ qL → 1 ≤ idx r.p ∧ idx r.p < m)
    (hL : L.Nodup) (hm : 2 ≤ m) :
    nsym (Conv3P.conv T qL s0 idx (fun _ => m - 1) L) = L.length * m :=
  SymExact.shared_nsym H hsrc hL hm

/-- **The improved 3-state conversion, for every `T`** (not mirrored and mirrored): with the counter bound
    `need3`, exactly `1 + n + (m₋n + |G|)(n + 1) + n(n + 2 + |R| + |G|) + (n + 2)` symbols. -/
theorem three_formula_eq (T : Machine Q P S) (b : S) (ss : List S) (qm : List Q) (Rl Gl : List (Q × S))
    (idx : Conv1W.VSt Q S → ℕ) (need : Conv1W.VSym Q S → ℕ)
    (hneed : ∀ x ∈ Conv3S.wsyms ss qm Gl, need x = need3 ss.length Rl.length Gl.length x)
    (hss : ss.Nodup) (hqm : qm.Nodup) (hGl : Gl.Nodup) :
    (Conv3S.Hyp T b ss qm Rl Gl idx need →
      (∀ r ∈ Conv1W.conv T b ss qm Rl Gl, r.p ≠ .L → 1 ≤ idx r.p ∧ idx r.p ≤ need r.s) →
      nsym (Conv3S.conv T b ss qm Rl Gl idx need) =
        1 + ss.length + (qm.length * ss.length + Gl.length) * (ss.length + 1) +
          ss.length * (ss.length + 2 + Rl.length + Gl.length) + (ss.length + 2)) ∧
    (Conv3S.Hyp (Conv3Base.mirror T) b ss qm Rl Gl idx need →
      (∀ r ∈ Conv1W.conv (Conv3Base.mirror T) b ss qm Rl Gl, r.p ≠ .L → 1 ≤ idx r.p ∧ idx r.p ≤ need r.s) →
      nsym (Conv3S.convM T b ss qm Rl Gl idx need) =
        1 + ss.length + (qm.length * ss.length + Gl.length) * (ss.length + 1) +
          ss.length * (ss.length + 2 + Rl.length + Gl.length) + (ss.length + 2)) :=
  ⟨fun H hsrc => SymExact.conv3S_nsym_eq H hsrc hneed hss hqm hGl,
   fun H hsrc => SymExact.convM3S_nsym_eq H hsrc hneed hss hqm hGl⟩

end General

/-! ## The 2-symbol conversion of (13,7) (3-bit codes): 169, 149, 135, 92 -/

section TwoSym
open URTM.Gen.K13_7
open URTM.Univ.Values13_7

/-- **169** (Morita's conversion, Morita's code). The Lean conversion `Conv54K.conv` (3-bit codes) applied to
    (13,7) with Morita's code `numCode ss 3` (`b, y, n, y1, n1, *, $` ↦ `000, 001, …, 110`): every one of the 13
    states has a rule into a real state, `P_r = P_w = 65`, and the converted machine has exactly
    `13 + 2·13 + 65 + 65 = 13·3 + 65 + 65 = 169` states. It is deterministic and reversible and simulates every
    CTSH (each step of (13,7) in 7 steps). -/
theorem morita2_13_7 :
    (dGo T qs).length = 13 ∧ (Conv54K.pRK T (Conv54K.numCode ss 3) 3).length = 65 ∧
    (Conv54K.pWK T (Conv54K.numCode ss 3) 3).length = 65 ∧
    nst (Conv54K.conv T (Conv54K.numCode ss 3) 3 qs) = 13 * 3 + 65 + 65 ∧ 13 * 3 + 65 + 65 = 169 ∧
    Deterministic (Conv54K.conv T (Conv54K.numCode ss 3) 3 qs) ∧
    Reversible (Conv54K.conv T (Conv54K.numCode ss 3) 3 qs) ∧
    Sim13 (Conv54K.conv T (Conv54K.numCode ss 3) 3 qs) ⟨Conv54K.numCode ss 3, 3, fun p => .r p [], fun _ => 0⟩ := by
  obtain ⟨h1, h2, h3⟩ := counts169
  have h := Conv54K.conv_nst (T := T) (code := code169) (k := 3) (qs := qs) (by decide) hlen169 hQ hqs
  have hq : qs.length = 13 := by decide
  rw [h1, h2, h3, hq] at h
  exact ⟨h1, h2, h3, h.trans rfl, rfl, det169, rev169, sim13 hyp169 det169⟩

/-- **149** (the code chosen by search). The same conversion with the code of
    `results/fewsym/urtm13-7.morita.json` (`b 000, y 100, n 101, y1 001, n1 010, * 110, $ 111`, the best of the
    5040 assignments with the blank `000`; the search itself is outside Lean): `P_r = P_w = 55` and
    `13·3 + 55 + 55 = 149` states; deterministic, reversible, simulates every CTSH. -/
theorem codeopt2_13_7 :
    (dGo T qs).length = 13 ∧ (Conv54K.pRK T code149 3).length = 55 ∧ (Conv54K.pWK T code149 3).length = 55 ∧
    nst (Conv54K.conv T code149 3 qs) = 13 * 3 + 55 + 55 ∧ 13 * 3 + 55 + 55 = 149 ∧
    Deterministic (Conv54K.conv T code149 3 qs) ∧ Reversible (Conv54K.conv T code149 3 qs) ∧
    Sim13 (Conv54K.conv T code149 3 qs) ⟨code149, 3, fun p => .r p [], fun _ => 0⟩ := by
  obtain ⟨h1, h2, h3⟩ := counts149
  have h := Conv54K.conv_nst (T := T) (code := code149) (k := 3) (qs := qs) (by decide) hlen149 hQ hqs
  have hq : qs.length = 13 := by decide
  rw [h1, h2, h3, hq] at h
  exact ⟨h1, h2, h3, h.trans rfl, rfl, det149, rev149, sim13 hyp149 det149⟩

/-- **135** (written values and path types chosen by CP-SAT; the table is imported, not computed by a Lean
    conversion). The table before merging of the record `results/fewsym/records/urtm13-7.2.merge.json`
    (`URTM.Gen.FS135_2`, generated by `tools/gen_fewsym_lean.py --unmerged`) uses the code of 149, has exactly
    135 states, is deterministic and reversible, and simulates every CTSH (each step of (13,7) in 3, 5 or 7
    steps; the finite per-rule check `FewSym.certB` by the kernel). -/
theorem fewsym135_13_7 :
    (∀ s, URTM.Gen.FS135_2.code s = code149 s) ∧ URTM.Gen.FS135_2.E.k = 3 ∧
    nst URTM.Gen.FS135_2.M = 135 ∧
    Deterministic URTM.Gen.FS135_2.M ∧ Reversible URTM.Gen.FS135_2.M ∧
    Sim13 URTM.Gen.FS135_2.M URTM.Gen.FS135_2.E :=
  ⟨fun s => (code135 s).1, rfl, nst135, URTM.Gen.FS135_2.det, URTM.Gen.FS135_2.rev,
    sim13 URTM.Gen.FS135_2.hyp URTM.Gen.FS135_2.det⟩

/-- **92** (states merged by CP-SAT; the table is imported). The merged table of the same record
    (`URTM.Gen.FS92_2`, the (92,2) of `CTSH92_2Main`) has exactly 92 states and is the image of the 135-state
    table under the renaming `hm` of the states (every renamed rule is a rule of the 92-state table and every
    rule of it is a renamed one; the reading states correspond); it is deterministic and reversible and
    simulates every CTSH. -/
theorem fewsym92_13_7 :
    nst URTM.Gen.FS92_2.M = 92 ∧
    (∀ r ∈ URTM.Gen.FS135_2.M, URTM.Gen.FS135_2.mapR r ∈ URTM.Gen.FS92_2.M) ∧
    (∀ r ∈ URTM.Gen.FS92_2.M, ∃ r' ∈ URTM.Gen.FS135_2.M, URTM.Gen.FS135_2.mapR r' = r) ∧
    (∀ p ∈ qs, URTM.Gen.FS135_2.hm (URTM.Gen.FS135_2.ρ p) = URTM.Gen.FS92_2.ρ p) ∧
    (∀ s, URTM.Gen.FS92_2.code s = code149 s) ∧
    Deterministic URTM.Gen.FS92_2.M ∧ Reversible URTM.Gen.FS92_2.M ∧
    Sim13 URTM.Gen.FS92_2.M URTM.Gen.FS92_2.E :=
  ⟨nst92, URTM.Gen.FS135_2.merge_img, URTM.Gen.FS135_2.merge_onto, URTM.Gen.FS135_2.merge_ρ,
    fun s => (code135 s).2, URTM.Gen.FS92_2.det, URTM.Gen.FS92_2.rev,
    sim13 URTM.Gen.FS92_2.hyp URTM.Gen.FS92_2.det⟩

end TwoSym

/-! ## The 3-state conversion of (32,3): 18476, 1820, 659, 600 -/

section ThreeState
open URTM.CTSH URTM.SimLemmas URTM.Gen.K32_3
open URTM.CTSH.U3_36654 (That allW idx3)
open URTM.CTSH.U32_3 (encC32 finCfg32)
open URTM.CTSH.U3_600 (f32)

/-- **18476** (↑ and ↓ merged). Morita's 1WU machine of (32,3) (`That`, Lemma 5.9: `N = 298` symbols, states
    numbered `1..61` by Morita's numbering `idx3`, `M = 62`), and the 3-state conversion with one kind of
    counter keeping every counter `1..M − 1` (`Conv3P.conv` with `need x = 61`): exactly `N·M = 298·62 = 18476`
    symbols. The simulation of every CTSH by this machine is `URTM.CTSH.U3_18476.urtm3_18476_simulates_ctsh`
    (`lean/URTM/CTSH3_18476Main.lean`). -/
theorem shared3_32_3 :
    allW.length = 298 ∧ nsym (Conv3P.conv That .L .bl idx3 (fun _ => 61) allW) = 298 * 62 ∧ 298 * 62 = 18476 :=
  ⟨Values32_3.allW_length, Values32_3.shared_32_3, rfl⟩

/-- **1820** (only the counters that occur). The same 1WU machine and conversion with the numbering `idxP` and
    the counter bound `needP` of `tools/threestate.py` (onewu=pair, counter=pruned, numbering chosen by trying
    the orders of the groups; imported, `URTM.Gen.P3_1820`): the hypotheses of `Conv3P` hold (checked by the
    kernel), and the 3-state machine has exactly `N + Σ_x need x = 298 + 1522 = 1820` symbols. Only the number
    of symbols is claimed: that the cut counters suffice along every run (needed for a simulation) is not shown. -/
theorem pruned3_32_3 :
    Conv3P.Hyp That .L .bl URTM.Gen.P3_1820.idxP URTM.Gen.P3_1820.needP allW ∧
    (allW.map URTM.Gen.P3_1820.needP).sum = 1522 ∧
    nsym (Conv3P.conv That .L .bl URTM.Gen.P3_1820.idxP URTM.Gen.P3_1820.needP allW) = 298 + 1522 ∧
    298 + 1522 = 1820 := by
  have hs : (allW.map URTM.Gen.P3_1820.needP).sum = 1522 := by decide +kernel
  refine ⟨URTM.Gen.P3_1820.hyp, hs, ?_, rfl⟩
  rw [Values32_3.pruned_32_3, Values32_3.allW_length, hs]

/-- **659** (the improved 3-state conversion, not mirrored). `Conv3S.conv` applied to (32,3) without its halting
    rules, with the parameters of `tools/threestate.py` (imported, `URTM.Gen.T3_659`; the Lean conversion equals
    the Python table `T3py` rule by rule): `n = 3`, `m₋ = 14`, `|R| = 46`, `|G| = 47`, the counter bound is `need3`,
    and the 3-state machine has exactly `1 + n + (m₋n + |G|)(n + 1) + n(n + 2 + |R| + |G|) + (n + 2) = 659` symbols.
    It is deterministic and reversible and simulates every CTSH (`Sim3_659.urtm3_659_simulates_ctsh`, the form of
    `CTSH3_600Main.urtm3_600_simulates_ctsh` without the mirror). -/
theorem three_32_3_659 :
    ss.length = 3 ∧ URTM.Gen.T3_659.qm.length = 14 ∧ URTM.Gen.T3_659.Rl.length = 46 ∧
    URTM.Gen.T3_659.Gl.length = 47 ∧
    (∀ x ∈ Conv3S.wsyms ss URTM.Gen.T3_659.qm URTM.Gen.T3_659.Gl, URTM.Gen.T3_659.need x = need3 3 46 47 x) ∧
    nsym (Conv3S.conv URTM.Gen.T3_659.T' Sy.s0 ss URTM.Gen.T3_659.qm URTM.Gen.T3_659.Rl URTM.Gen.T3_659.Gl
      URTM.Gen.T3_659.idx URTM.Gen.T3_659.need) =
      1 + 3 + (14 * 3 + 47) * (3 + 1) + 3 * (3 + 2 + 46 + 47) + (3 + 2) ∧
    1 + 3 + (14 * 3 + 47) * (3 + 1) + 3 * (3 + 2 + 46 + 47) + (3 + 2) = 659 ∧
    Conv3S.conv URTM.Gen.T3_659.T' Sy.s0 ss URTM.Gen.T3_659.qm URTM.Gen.T3_659.Rl URTM.Gen.T3_659.Gl
      URTM.Gen.T3_659.idx URTM.Gen.T3_659.need = URTM.Gen.T3_659.T3py ∧
    Deterministic URTM.Gen.T3_659.T3py ∧ Reversible URTM.Gen.T3_659.T3py ∧
    ∀ (C : CTSH) (w : List Ch),
      (∀ n vf mf, CHaltsIn C n (w, 0) (vf, mf) →
        ∃ N M rm, n ≤ N + 1 ∧ HaltsIn URTM.Gen.T3_659.T' N (encC32 C w) (unhalt f32 (finCfg32 C vf mf rm)) ∧
          HaltsIn URTM.Gen.T3_659.T3py M (Sim3_659.E659 C w) (Sim3_659.fin659 C w vf mf rm N)) ∧
      (∀ M e, HaltsIn URTM.Gen.T3_659.T3py M (Sim3_659.E659 C w) e →
        ∃ n vf mf rm N, CHaltsIn C n (w, 0) (vf, mf) ∧
          HaltsIn URTM.Gen.T3_659.T' N (encC32 C w) (unhalt f32 (finCfg32 C vf mf rm)) ∧
          e = Sim3_659.fin659 C w vf mf rm N) ∧
      ((∀ n f, ¬ CHaltsIn C n (w, 0) f) ↔ (∀ M e, ¬ HaltsIn URTM.Gen.T3_659.T3py M (Sim3_659.E659 C w) e)) := by
  obtain ⟨h1, h2, h3, h4⟩ := Values32_3.params659
  obtain ⟨hD, hR, -⟩ := Sim3_659.urtm3_659_simulates_ctsh [] []
  refine ⟨h1, h2, h3, h4, Values32_3.need659, Values32_3.three_659, rfl, URTM.Gen.T3_659.conv_eq_py, hD, hR,
    fun C w => ?_⟩
  obtain ⟨-, -, -, -, -, -, -, hf, hb, hn⟩ := Sim3_659.urtm3_659_simulates_ctsh C w
  exact ⟨hf, hb, hn⟩

/-- **600 as an equality** (the improved 3-state conversion, mirrored): `n = 3`, `m₋ = 18`, `|R| = |G| = 36`,
    and the 3-state machine has exactly 600 symbols (`FinalFormulas.three_32_3` gave the bound `≤ 600` and the
    count of the witness). -/
theorem three_32_3_600_eq :
    nsym (Conv3S.convM URTM.Gen.T3_600.T' Sy.s0 ss URTM.Gen.T3_600.qmR URTM.Gen.T3_600.RlR URTM.Gen.T3_600.GlR
      URTM.Gen.T3_600.idx URTM.Gen.T3_600.need) =
      1 + 3 + (18 * 3 + 36) * (3 + 1) + 3 * (3 + 2 + 36 + 36) + (3 + 2) ∧
    1 + 3 + (18 * 3 + 36) * (3 + 1) + 3 * (3 + 2 + 36 + 36) + (3 + 2) = 600 :=
  ⟨Values32_3.three_600, rfl⟩

end ThreeState

end URTM.Univ.FinalValues
