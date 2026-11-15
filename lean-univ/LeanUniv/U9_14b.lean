/-
  **The second URTM(9,14) table (t4b) in the sense of Morita's Def. 7.1.**

  `T9b` (`lean/URTM/CTSH9_14bDefs.lean`) is Morita's URTM(10,8) with copy_n_2 merged into case_y_1, the
  difference carried by cell tags, plus one quintuple that clears the tag of the left-end blank (64
  quintuples). Its CTSH theorem is `URTM.CTSH.U9_14b.urtm9_14b_simulates_ctsh`. Numbering, encoder and
  decoder are those of `LeanUniv/U9_14.lean` (t4a): the encoder of (10,8), and the decoder erases the tags
  (`x ↦ x % 8`) before the decoder of (10,8). No hypotheses. Minimality is not claimed.
-/
import LeanUniv.Chain10_8
import LeanUniv.ComputableEnc
import LeanUniv.ComputableDec
import URTM.CTSH9_14b
import LeanUniv.U9_14

namespace URTM.Univ.U9_14b
open URTM URTM.Spec URTM.CTSH URTM.Gen.K10_8 URTM.Univ.KToSpec Relation
open URTM.KState (Tgt Cfg HaltsIn)
open URTM.CTSH.U9_14 (TS RA9 un bk)
open URTM.CTSH.U9_14b (T9b encC9b finCfg9b tapeList9b rep9b eB)
open URTM.Univ.U9_14 (syN9 num9_14 syN9_mod eraseCode eraseID toID_erase tp_map tp_bk eraseCode_primrec)
open URTM.Univ.U10_8 (stN syN stN_inj syN_inj encList δ readU)
open URTM.Univ.L0 (tbl)

/-! ### Numbering and the Spec table -/

/-- **The second URTM(9,14) table (t4b) as a Spec table** (64 quintuples). -/
def U : List Quint := numT num9_14 T9b

/-- The witness is the numbering of `T9b` (Morita's (10,8) table `T` mapped by `tagRuleB`, plus one quintuple). -/
theorem U_def : U = numT num9_14 (URTM.Gen.K10_8.T.map URTM.CTSH.U9_14b.tagRuleB ++
    [⟨.q4, (.s0, true), (.s0, false), .R, .go .q0⟩]) := rfl

instance (V : List Quint) : Decidable (Spec.Deterministic V) := by
  unfold Spec.Deterministic; infer_instance
instance (V : List Quint) : Decidable (Spec.Reversible V) := by
  unfold Spec.Reversible; infer_instance

theorem U_length : U.length = 64 := by decide +kernel

/-- **Counts** (Morita's convention): 9 states, 14 symbols. -/
theorem U_counts : Spec.NStates U = 9 ∧ Spec.NSyms U = 14 := by decide +kernel
theorem U_det : Spec.Deterministic U := by decide +kernel
theorem U_rev : Spec.Reversible U := by decide +kernel

/-! ### Tapes with and without tags -/

theorem eB_zero (C : CTSH) : eB C 0 [] = false := by
  have hk : 0 < C.k := by simp [CTSH.k]
  simp [eB, Nat.div_self hk]

theorem tapeList9b_zero (C : CTSH) (w : List Ch) :
    tapeList9b C 0 [] w = (U10_8.tapeList C 0 [] w).map (·, false) := by
  simp [tapeList9b, eB_zero, RA9, U10_8.tapeList, U10_8.RA, prod, U10_8.Lo_zero, un]

/-- The initial configuration of `T9b` is the one of (10,8) without tags. -/
theorem encList_eq9b (C : CTSH) (w : List Ch) :
    Spec.toID 0 (encList C w) = numCfg num9_14 (δ C) (encC9b C w) := by
  rw [U10_8.encList_eq]
  simp only [numCfg, encC9b, rep9b, U10_8.encC, U10_8.rep, U10_8.tapeOf, tapeList9b_zero, tp_bk]
  congr 1
  all_goals first
    | rfl
    | (funext x; simp [num9_14, U10_8.num10_8, syN9])
    | simp [RA9]

theorem isIDOf_encList9b (C : CTSH) (w : List Ch) : Spec.IsIDOf U (Spec.toID 0 (encList C w)) := by
  have hs : ∀ a ∈ [0, 1, 2, 6, 7], a = 0 ∨ a ∈ Spec.symbols U := by decide +kernel
  have hlo : ∀ c : Ch, U10_8.loN c ∈ [0, 1, 2, 6, 7] := by intro c; cases c <;> decide
  have h0 : (0 : ℕ) ∈ Spec.states U := by decide +kernel
  refine isIDOf_toID U 0 _ h0 fun a ha => hs a ?_
  simp only [encList, List.mem_append, List.mem_cons, List.mem_flatMap, List.mem_map,
    List.not_mem_nil] at ha
  rcases ha with ((rfl | rfl | ⟨u, -, rfl | ⟨c, -, rfl⟩⟩) | rfl | h) | ⟨c, -, rfl⟩
  all_goals first | decide | exact hlo c | exact absurd h id

/-! ### Erasing the tags on Spec codes -/

/-- The halting tape of `T9b` (the `halt` case). -/
def haltList (C : CTSH) (rm v : List Ch) : List TS :=
  (Sy.s0, eB C 0 rm) :: un (U10_8.Hi C 0) ++ (Sy.s0, false) :: (Sy.s7, true) ::
    ((rm.map U10_8.up).map (·, true) ++ (Sy.s1, true) :: un (v.map U10_8.lo))

/-- The tape of a final configuration of `T9b`, without the tags, is the one of (10,8). -/
theorem fin_fst (C : CTSH) (vf : List Ch) (mf : ℕ) (rm : List Ch)
    (hv : vf = [] ∨ ∃ v, vf = .Y :: v) (i : ℤ) :
    ((finCfg9b C vf mf rm).tape i).1 = (U10_8.finCfg C vf mf rm).tape i := by
  rcases hv with rfl | ⟨v, rfl⟩
  · have e : (tapeList9b C mf rm []).map Prod.fst = U10_8.tapeList C mf rm [] := by
      simp [tapeList9b, RA9, U10_8.tapeList, U10_8.RA, un, Function.comp_def, URTM.CTSH.U9_14.tagSt]
    have := congrFun (tp_map Prod.fst bk (tapeList9b C mf rm [])) i
    simp only [e] at this
    simp only [finCfg9b, U10_8.finCfg, U10_8.tapeOf]
    exact this.symm
  · have e : (haltList C rm v).map Prod.fst = U10_8.tapeList C 0 rm (.Y :: v) := by
      simp [haltList, U10_8.tapeList, U10_8.RA, prod, U10_8.Lo_zero, un, Function.comp_def, U10_8.lo]
    have := congrFun (tp_map Prod.fst bk (haltList C rm v)) i
    simp only [e] at this
    simp only [finCfg9b, U10_8.finCfg, U10_8.tapeOf]
    exact this.symm

theorem fin_erase (C : CTSH) (vf : List Ch) (mf : ℕ) (rm : List Ch)
    (hv : vf = [] ∨ ∃ v, vf = .Y :: v) (hm : vf = [] ∨ mf = 0) :
    eraseID (numCfg num9_14 (δ C) (finCfg9b C vf mf rm)) =
      numCfg U10_8.num10_8 (δ C) (U10_8.finCfg C vf mf rm) := by
  simp only [eraseID, numCfg]
  congr 1
  · rcases hv with rfl | ⟨v, rfl⟩ <;> rfl
  · rcases hv with rfl | ⟨v, rfl⟩ <;> rfl
  · funext x
    simp only [num9_14, U10_8.num10_8, syN9_mod, fin_fst C vf mf rm hv]

/-- A code of a final ID of `T9b`. -/
theorem fin_code (C : CTSH) (vf : List Ch) (mf : ℕ) (rm : List Ch) (hv : vf = [] ∨ ∃ v, vf = .Y :: v) :
    ∃ g, Spec.toID (numCfg num9_14 (δ C) (finCfg9b C vf mf rm)).pos g =
      numCfg num9_14 (δ C) (finCfg9b C vf mf rm) := by
  rcases hv with rfl | ⟨v, rfl⟩
  · have := numCfg_tp (N := num9_14) bk rfl (δ C) (.halt .h0) (tapeList9b C mf rm [])
      ((U10_8.RA C mf).length + 2 + rm.length) (by simp [tapeList9b, URTM.CTSH.U9_14.RA9_length, un]; omega)
    have e : finCfg9b C [] mf rm = ⟨.halt .h0, (((U10_8.RA C mf).length + 2 + rm.length : ℕ) : ℤ),
        CTSH.Sim.tp bk (tapeList9b C mf rm [])⟩ := by
      simp [finCfg9b]
    rw [e, this]
    exact ⟨_, rfl⟩
  · have := numCfg_tp (N := num9_14) bk rfl (δ C) (.halt .h1) (haltList C rm v)
      (U10_8.RA C 0).length (by simp [haltList, U10_8.RA, prod, U10_8.Lo_zero, un])
    have e : finCfg9b C (.Y :: v) mf rm = ⟨.halt .h1, (((U10_8.RA C 0).length : ℕ) : ℤ),
        CTSH.Sim.tp bk (haltList C rm v)⟩ := by
      simp [finCfg9b, haltList]
    rw [e, this]
    exact ⟨_, rfl⟩

/-- **The readout is right on every code of a halting ID of `T9b`** (after erasing the tags). -/
theorem readU_fin (C : CTSH) (vf : List Ch) (mf : ℕ) (hmf : mf ≤ C.length) (rm : List Ch)
    (hv : vf = [] ∨ ∃ v, vf = .Y :: v) (hm : vf = [] ∨ mf = 0) (g : Code)
    (hg : Spec.toID (numCfg num9_14 (δ C) (finCfg9b C vf mf rm)).pos g =
      numCfg num9_14 (δ C) (finCfg9b C vf mf rm)) :
    readU (eraseCode g) = some (C.length, (vf, mf)) := by
  obtain ⟨p, hp⟩ := U10_8.finCfg_window C vf mf rm hm
  have h1 := toID_erase (numCfg num9_14 (δ C) (finCfg9b C vf mf rm)).pos g
  rw [hg, fin_erase C vf mf rm hv hm, hp] at h1
  have hpos : (numCfg num9_14 (δ C) (finCfg9b C vf mf rm)).pos = (p : ℤ) - δ C := by
    have h1 := congrArg Spec.ID.pos (fin_erase C vf mf rm hv hm)
    have h2 := congrArg Spec.ID.pos hp
    simp only [eraseID] at h1
    rw [h1, h2]; rfl
  rw [hpos] at h1
  rw [PadInv.readU_toID h1]
  exact U10_8.readU_window C mf hmf rm vf _ p

/-! ### The run-level simulation and the exit layer -/

theorem runSim_U9_14b (C : CTSH) (w : List Ch) :
    RunSim (CStep C) (Halting C) (Spec.Step U) (Spec.Halted U)
      (fun y γ => ∃ g, Spec.toID γ.pos g = γ ∧ readU (eraseCode g) = some (C.length, y))
      (w, 0) (Spec.toID 0 (encList C w)) := by
  have hmain := URTM.CTSH.U9_14b.urtm9_14b_simulates_ctsh C w
  rw [encList_eq9b]
  refine ⟨fun y hy => ?_, fun hn hU => ?_⟩
  · obtain ⟨n, hn⟩ := U10_8.cstepN_of_rtg hy.1
    obtain ⟨vf, mf⟩ := y
    obtain ⟨N, rm, -, hN⟩ := hmain.1 n vf mf ⟨hn, hy.2⟩
    have hv : vf = [] ∨ ∃ v, vf = .Y :: v := by
      rcases hy.2.2 with ⟨v, h1, -⟩ | h
      · exact .inr ⟨v, h1⟩
      · exact .inl h
    have hm : vf = [] ∨ mf = 0 := by
      rcases hy.2.2 with ⟨v, -, h2⟩ | h
      · exact .inr h2
      · exact .inl h
    have hmf : mf ≤ C.length := by have := hy.2.1; simp [CTSH.k] at this; omega
    obtain ⟨g, hg⟩ := fin_code C vf mf rm hv
    exact ⟨_, (haltsAt_numCfg_iff (N := num9_14) T9b (δ C) _ _).mpr ⟨N, _, hN, rfl⟩, g, hg,
      readU_fin C vf mf hmf rm hv hm g hg⟩
  · obtain ⟨γ, hγ⟩ := hU
    obtain ⟨N, c', h, -⟩ := (haltsAt_numCfg_iff (N := num9_14) T9b (δ C) _ γ).mp hγ
    exact hmain.2.2.mp (fun n (f : CTSH.ID) hc => hn ⟨f, U10_8.rtg_of_cstepN hc.1, hc.2⟩) N c' h

/-- **Decoder** of URTM(9,14): erase the tags, then the (10,8) decoder. -/
def d9_14b (g : Code) : Option Code := Chain10_8.d10_8 (eraseCode g)

theorem d9_14b_toID (p : ℤ) (g g' : Code) (h : toID p g = toID p g') : d9_14b g = d9_14b g' :=
  Chain10_8.d10_8_toID p _ _ (by rw [toID_erase, toID_erase, h])

theorem d9_14b_computable : Computable d9_14b :=
  ComputableDec.d10_8_computable.comp eraseCode_primrec.to_comp

theorem hout (n : ℕ) (a : Code) :
    RunSim TagToCTSH.stepC TagToCTSH.haltC (Spec.Step U) (Halted U)
      (fun y γ => ∃ g, toID γ.pos g = γ ∧ d9_14b g = Fin.decM y)
      (Fin.encMid (tbl n) a) (toID 0 (Chain10_8.c10_8 (n, a))) := by
  rw [Chain10_8.encMid_eq]
  have h := (Chain10_8.runSim_carry (Chain10_8.ctshOf (tbl n)) (Chain10_8.wordOf (tbl n) a, 0)).trans
    (runSim_U9_14b (Chain10_8.ctshOf (tbl n)) (Chain10_8.wordOf (tbl n) a))
  refine ⟨fun y hy => ?_, h.2⟩
  obtain ⟨γ, hγ, s', rfl, g, hg, hr⟩ := h.1 y hy
  exact ⟨γ, hγ, g, hg, by simp [d9_14b, Chain10_8.d10_8, hr, Chain10_8.decM_eq]⟩

/-! ### The main theorems -/

theorem strictBody_U9_14b : DropGen.StrictBody U Chain10_8.c10_8 d9_14b :=
  strictBody_of_chain U Chain10_8.c10_8 d9_14b
    (fun n => L0.CStep (tbl n)) (fun n => L0.CHalt (tbl n)) (fun n => Fin.Inv1 (tbl n))
    (fun _ => TagToCTSH.stepC) (fun _ => TagToCTSH.haltC)
    (fun n => Fin.encMid (tbl n)) Fin.decM
    (fun _ _ _ => isIDOf_encList9b _ _)
    Fin.hin1
    (fun n => Fin.mid (tbl n))
    (fun n a _ => hout n a)
    d9_14b_toID

/-- **URTM(9,14) is a UTM in the strict sense of Morita Def. 7.1.** -/
theorem isUTMStrict_U : IsUTMStrict U :=
  DropGen.isUTMStrict_of_body ComputableEnc.c10_8_computable d9_14b_computable strictBody_U9_14b

/-- **Existence of URTM(9,14)** in the exact sense of Morita's Def. 7.1. No hypotheses. -/
theorem exists_urtm_9_14b :
    ∃ U : List Quint, Deterministic U ∧ Reversible U ∧ NStates U = 9 ∧ NSyms U = 14 ∧
      IsUTMStrict U :=
  ⟨U, U_det, U_rev, U_counts.1, U_counts.2, isUTMStrict_U⟩

end URTM.Univ.U9_14b
