/-
  **Morita's one-cell-per-letter family with two separator symbols** (2026-11-02).

  `MoritaGen.readM` counts one separator symbol `∗`. URTM(10,7) (`U10_7`) halts with the separators of
  the rule region in two colours: `∗` in the part before the phase marker and `Y` (the colour that
  also carries the tagged copies) in the part after it, so the readout counts both.

  * `readM2 hs s s' e g`: as `readM hs s e g` with `L.count s + L.count s'` in place of `L.count s`.
    It sees only the state and the window list and ignores trailing blanks (`readM2_toID`), and it
    is primitive recursive (`readM2_primrec`).
  * `strictBody_morita2`: `strictBody_morita` with the two counts (same hypotheses otherwise, plus
    `lo c ≠ st'` and `N.sym st' ≠ 0`).
-/
import LeanUniv.MoritaGen

namespace URTM.Univ.MoritaGen2
open URTM URTM.CTSH URTM.Univ.KToSpec URTM.Univ.NumGen URTM.Univ.MoritaGen
open URTM.Univ.U10_8 (loN)
open URTM.KState (Tgt Cfg Machine HaltsIn)

/-- The readout on the state `q` and the whole window list `L`, counting `s` and `s'`. -/
def readL2 (hs s s' e : ℕ) (q : ℕ) (L : List ℕ) : ℕ × List ℕ :=
  if q = hs then (L.count s + L.count s' - e, 1 :: lowSuffix L) else (L.count s + L.count s', [])

/-- **Readout** (list level) from a code `g` of the halting ID: `(|C|, ϕ₁(vf))`. -/
def readM2 (hs s s' e : ℕ) (g : Spec.Code) : Option (ℕ × List ℕ) :=
  some (readL2 hs s s' e g.1 (g.2.1.reverse ++ g.2.2))

/-- **The readout depends only on the ID**, not on the code chosen for it. -/
theorem readM2_toID (hs s s' e : ℕ) (h0 : s ≠ 0) (h0' : s' ≠ 0) {p : ℤ} {g g' : Spec.Code}
    (h : Spec.toID p g = Spec.toID p g') : readM2 hs s s' e g = readM2 hs s s' e g' :=
  congrArg some (read_toID (readL2 hs s s' e)
    (fun q k L => by simp only [readL2, count_padL h0, count_padL h0', lowSuffix_padL])
    (fun q k L => by simp only [readL2, count_padR h0, count_padR h0', lowSuffix_padR]) h)

theorem readM2_null (hs s s' e q : ℕ) (hq : q ≠ hs) (L : List ℕ) (p : ℕ) :
    readM2 hs s s' e (window q L p) = some (L.count s + L.count s', []) := by
  simp only [readM2, window_whole, window_st, readL2, if_neg hq]

theorem readM2_halt (hs s s' e : ℕ) (A : List ℕ) (m : ℕ) (hm0 : m ≠ 0) (hm1 : m ≠ 1)
    (hm2 : m ≠ 2) (v : List Ch) (p : ℕ) :
    readM2 hs s s' e (window hs (A ++ m :: v.map loN) p) =
      some ((A ++ m :: v.map loN).count s + (A ++ m :: v.map loN).count s' - e,
        (Ch.Y :: v).map loN) := by
  simp only [readM2, window_whole, window_st, readL2, if_true, lowSuffix_mark A m hm0 hm1 hm2]
  rfl

open Primrec in
theorem readM2_primrec (hs s s' e : ℕ) : Primrec (readM2 hs s s' e) := by
  have hL : Primrec fun g : Spec.Code => g.2.1.reverse ++ g.2.2 :=
    list_append.comp (list_reverse.comp (fst.comp snd)) (snd.comp snd)
  have hc : Primrec fun g : Spec.Code =>
      (g.2.1.reverse ++ g.2.2).count s + (g.2.1.reverse ++ g.2.2).count s' :=
    nat_add.comp (ComputableDec.list_count (const s) hL) (ComputableDec.list_count (const s') hL)
  exact (option_some.comp (Primrec.ite (Primrec.eq.comp fst (const hs))
    (pair (nat_sub.comp hc (const e)) (list_cons.comp (const 1) (lowSuffix_primrec.comp hL)))
    (pair hc (const [])))).of_eq fun g => by simp only [readM2, readL2]

/-- **Body form** of the family theorem with two separator symbols `st`, `st'`: the body of
    `IsUTMStrict` for the encoder `cOf (encM …)` (which writes `st` only) and the decoder
    `dOf (readM2 …)`. Hypotheses as for `strictBody_morita`, with the final list tapes holding
    exactly `|C|` symbols `st` or `st'` together (`|C| + e` for `(Y v, 0)`). -/
theorem strictBody_morita2 {Q P S : Type} [DecidableEq S] (N : Numbering Q P S)
    (T : Machine Q P S) (lo : Ch → S) (st st' bk x : S) (q0 : Q) (hnull hhalt : P) (e : ℕ)
    (hbk : N.sym bk = 0) (hlo : ∀ c, N.sym (lo c) = loN c) (hls : ∀ c, lo c ≠ st)
    (hls' : ∀ c, lo c ≠ st') (hst0 : N.sym st ≠ 0) (hst0' : N.sym st' ≠ 0) (hnh : hnull ≠ hhalt)
    (encC : CTSH → List Ch → Cfg Q P S) (finC : CTSH → List Ch → ℕ → List Ch → Cfg Q P S)
    (henc : ∀ C w, encC C w = ⟨.go q0, (((Sim.RA lo st bk C 0).length + 2 : ℕ) : ℤ),
      Sim.tp bk (bk :: Sim.RA lo st bk C 0 ++ x :: w.map lo)⟩)
    (hsim : ∀ C w,
      (∀ n vf mf, CHaltsIn C n (w, 0) (vf, mf) →
        ∃ M rm, n ≤ M ∧ HaltsIn T M (encC C w) (finC C vf mf rm)) ∧
      (∀ M c, HaltsIn T M (encC C w) c →
        ∃ n vf mf rm, CHaltsIn C n (w, 0) (vf, mf) ∧ c = finC C vf mf rm) ∧
      ((∀ n f, ¬ CHaltsIn C n (w, 0) f) ↔ (∀ M c, ¬ HaltsIn T M (encC C w) c)))
    (hnullfin : ∀ C mf rm, mf ≤ C.length → ∃ (L : List S) (p : ℕ), p ≤ L.length ∧
      finC C [] mf rm = ⟨.halt hnull, p, Sim.tp bk L⟩ ∧ L.count st + L.count st' = C.length)
    (hhaltfin : ∀ C v rm, ∃ (A : List S) (mk : S) (p : ℕ), p ≤ (A ++ mk :: v.map lo).length ∧
      finC C (.Y :: v) 0 rm = ⟨.halt hhalt, p, Sim.tp bk (A ++ mk :: v.map lo)⟩ ∧
      (A ++ [mk]).count st + (A ++ [mk]).count st' - e = C.length ∧
      N.sym mk ≠ 0 ∧ N.sym mk ≠ 1 ∧ N.sym mk ≠ 2)
    (hU0 : N.st (.go q0) ∈ Spec.states (numT N T))
    (hUs : ∀ a ∈ [1, 2, N.sym x, N.sym st], a = 0 ∨ a ∈ Spec.symbols (numT N T)) :
    DropGen.StrictBody (numT N T) (ChainGen.cOf (encM (N.st (.go q0)) (N.sym x) (N.sym st)))
      (GenDec.dOf (readM2 (N.st (.halt hhalt)) (N.sym st) (N.sym st') e)) := by
  refine ChainGen.strictBody_of_ctsh (numT N T) (encM (N.st (.go q0)) (N.sym x) (N.sym st))
    (readM2 (N.st (.halt hhalt)) (N.sym st) (N.sym st') e)
    (fun C w => isIDOf_encM _ _ _ _ hU0 hUs C w) (fun C w => ?_)
    (fun p g g' h => readM2_toID _ _ _ _ hst0 hst0' h)
  rw [encM_eq N lo st bk hbk hlo q0 x C w, ← henc C w]
  obtain ⟨hF, -, hN⟩ := hsim C w
  refine runSim_of_sim N T _ C w (encC C w) (fun f c => ∃ rm, c = finC C f.1 f.2 rm) _
    (fun n f hf => ?_) (fun hn => hN.mp hn) (fun f c hf hc => ?_)
  · obtain ⟨M, rm, -, h⟩ := hF n f.1 f.2 hf
    exact ⟨M, _, h, rm, rfl⟩
  · obtain ⟨rm, rfl⟩ := hc
    obtain ⟨vf, mf⟩ := f
    obtain ⟨hk, hv | hv⟩ := hf
    · obtain ⟨v, hv1, hv2⟩ := hv
      simp only at hv1 hv2
      subst hv1 hv2
      obtain ⟨A, mk, p, hp, hfin, hc, hm0, hm1, hm2⟩ := hhaltfin C v rm
      simp only [hfin]
      refine read_of_tp N bk hbk _ _ _ p hp _ _ ?_
      rw [List.map_append, List.map_cons, map_lo N lo hlo, readM2_halt _ _ _ _ _ _ hm0 hm1 hm2]
      have hcnt : (A.map N.sym ++ N.sym mk :: v.map loN).count (N.sym st) =
          (A ++ [mk]).count st := by
        rw [← map_lo N lo hlo, ← List.map_cons, ← List.map_append,
          List.count_map_of_injective _ _ N.sym_inj]
        simp [List.count_append, List.count_cons, count_lo lo st hls]
      have hcnt' : (A.map N.sym ++ N.sym mk :: v.map loN).count (N.sym st') =
          (A ++ [mk]).count st' := by
        rw [← map_lo N lo hlo, ← List.map_cons, ← List.map_append,
          List.count_map_of_injective _ _ N.sym_inj]
        simp [List.count_append, List.count_cons, count_lo lo st' hls']
      rw [hcnt, hcnt', hc]
    · simp only at hv
      subst hv
      obtain ⟨L, p, hp, hfin, hc⟩ := hnullfin C mf rm (by simp [CTSH.k] at hk; omega)
      simp only [hfin]
      refine read_of_tp N bk hbk _ _ _ p hp _ _ ?_
      rw [readM2_null _ _ _ _ _ (fun h => hnh (Tgt.halt.inj (N.st_inj h))),
        List.count_map_of_injective _ _ N.sym_inj, List.count_map_of_injective _ _ N.sym_inj, hc]
      rfl

end URTM.Univ.MoritaGen2
