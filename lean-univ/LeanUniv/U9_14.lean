/-
  **URTM(9,14) in the sense of Morita's Def. 7.1** (computable encoding and decoding included).

  The table `T9` (`lean/URTM/CTSH9_14Defs.lean`) is Morita's URTM(10,8) with the state copy_y_2
  merged into case_y_1 and the difference carried by cell tags (`Sy × Bool`). Its CTSH theorem is
  `URTM.CTSH.U9_14.urtm9_14_simulates_ctsh` (`lean/URTM/CTSH9_14.lean`).

  * Numbering `num9_14`: states as for (10,8) (`U10_8.stN`; `q6` does not occur in `T9`), symbols
    `(s, false) ↦ syN s`, `(s, true) ↦ 8 + syN s`.
  * Encoder: the (10,8) encoder `Chain10_8.c10_8` itself. The initial configuration `encC9 C w`
    carries no tag, so its Spec ID is the one of (10,8) (`encList_eq9`).
  * Decoder: `d9_14 g = d10_8 (eraseCode g)`, where `eraseCode` sends every cell number `x` to
    `x % 8` (it erases the tag). The halting IDs of `T9`, so erased, are those of (10,8)
    (`fin_erase`), and `readU` reads them (`U10_8.readU_window`).

  `exists_urtm_9_14`: there is a deterministic reversible TM with 9 states and 14 symbols that
  satisfies `IsUTMStrict`. No hypotheses. Minimality is not claimed.
-/
import LeanUniv.Chain10_8
import LeanUniv.ComputableEnc
import LeanUniv.ComputableDec
import URTM.CTSH9_14

namespace URTM.Univ.U9_14
open URTM URTM.Spec URTM.CTSH URTM.Gen.K10_8 URTM.Univ.KToSpec Relation
open URTM.KState (Tgt Cfg HaltsIn)
open URTM.CTSH.U9_14 (TS T9 encC9 finCfg9 tapeList9 RA9 un bk)
open URTM.Univ.U10_8 (stN syN stN_inj syN_inj encList δ readU)
open URTM.Univ.L0 (tbl)

/-! ### Numbering and the Spec table -/

def syN9 : TS → ℕ := fun x => syN x.1 + (if x.2 then 8 else 0)

theorem syN_lt (s : Sy) : syN s < 8 := by cases s <;> decide

theorem syN9_inj : Function.Injective syN9 := by
  intro ⟨a, b⟩ ⟨a', b'⟩ h
  cases a <;> cases b <;> cases a' <;> cases b' <;> first | rfl | exact absurd h (by decide)

theorem syN9_mod (x : TS) : syN9 x % 8 = syN x.1 := by
  obtain ⟨a, b⟩ := x; cases a <;> cases b <;> rfl

def num9_14 : Numbering St Ps TS := ⟨stN, syN9, stN_inj, syN9_inj⟩

/-- **URTM(9,14) as a Spec table** (63 quintuples). -/
def U : List Quint := numT num9_14 T9

/-- The witness is the numbering of `T9` (Morita's (10,8) table `T` mapped by `tagRule`). -/
theorem U_def : U = numT num9_14 (URTM.Gen.K10_8.T.map URTM.CTSH.U9_14.tagRule) := rfl

instance (V : List Quint) : Decidable (Spec.Deterministic V) := by
  unfold Spec.Deterministic; infer_instance
instance (V : List Quint) : Decidable (Spec.Reversible V) := by
  unfold Spec.Reversible; infer_instance

theorem U_length : U.length = 63 := by decide +kernel

/-- **Counts** (Morita's convention): 9 states, 14 symbols. -/
theorem U_counts : Spec.NStates U = 9 ∧ Spec.NSyms U = 14 := by decide +kernel
theorem U_det : Spec.Deterministic U := by decide +kernel
theorem U_rev : Spec.Reversible U := by decide +kernel

/-! ### Tapes with and without tags -/

theorem tp_map {α β : Type} (f : α → β) (b : α) (L : List α) :
    CTSH.Sim.tp (f b) (L.map f) = fun i => f (CTSH.Sim.tp b L i) := by
  funext i
  cases i with
  | ofNat j =>
    simp only [CTSH.Sim.tp, List.getD_eq_getElem?_getD, List.getElem?_map]
    cases L[j]? <;> rfl
  | negSucc _ => rfl

theorem tapeList9_zero (C : CTSH) (w : List Ch) :
    tapeList9 C 0 [] w = (U10_8.tapeList C 0 [] w).map (·, false) := by
  simp [tapeList9, RA9, U10_8.tapeList, U10_8.RA, prod, U10_8.Lo_zero, un]

/-- The initial configuration of `T9` is the one of (10,8) without tags. -/
theorem tp_bk (L : List Sy) :
    CTSH.Sim.tp bk (L.map (·, false)) = fun i => (CTSH.Sim.tp Sy.s0 L i, false) :=
  tp_map (fun x : Sy => (x, false)) Sy.s0 L

/-- The initial configuration of `T9` is the one of (10,8) without tags. -/
theorem encList_eq9 (C : CTSH) (w : List Ch) :
    Spec.toID 0 (encList C w) = numCfg num9_14 (δ C) (encC9 C w) := by
  rw [U10_8.encList_eq]
  simp only [numCfg, encC9, URTM.CTSH.U9_14.rep9, U10_8.encC, U10_8.rep, U10_8.tapeOf,
    tapeList9_zero, tp_bk]
  congr 1
  all_goals first
    | rfl
    | (funext x; simp [num9_14, U10_8.num10_8, syN9])
    | simp [RA9]

theorem isIDOf_encList9 (C : CTSH) (w : List Ch) : Spec.IsIDOf U (Spec.toID 0 (encList C w)) := by
  have hs : ∀ a ∈ [0, 1, 2, 6, 7], a = 0 ∨ a ∈ Spec.symbols U := by decide +kernel
  have hlo : ∀ c : Ch, U10_8.loN c ∈ [0, 1, 2, 6, 7] := by intro c; cases c <;> decide
  have h0 : (0 : ℕ) ∈ Spec.states U := by decide +kernel
  refine isIDOf_toID U 0 _ h0 fun a ha => hs a ?_
  simp only [encList, List.mem_append, List.mem_cons, List.mem_flatMap, List.mem_map,
    List.not_mem_nil] at ha
  rcases ha with ((rfl | rfl | ⟨u, -, rfl | ⟨c, -, rfl⟩⟩) | rfl | h) | ⟨c, -, rfl⟩
  all_goals first | decide | exact hlo c | exact absurd h id

/-! ### Erasing the tags on Spec codes -/

/-- Erase the tags: every cell number `x ↦ x % 8`. -/
def eraseCode (g : Code) : Code := (g.1, g.2.1.map (· % 8), g.2.2.map (· % 8))

def eraseID (γ : Spec.ID) : Spec.ID := ⟨γ.st, γ.pos, fun x => γ.tape x % 8⟩

theorem toID_erase (p : ℤ) (g : Code) : toID p (eraseCode g) = eraseID (toID p g) := by
  simp only [toID, eraseCode, eraseID]
  congr 1
  funext x
  split_ifs <;> simp only [List.getD_eq_getElem?_getD, List.getElem?_map] <;>
    first
    | (cases g.2.2[(x - p).toNat]? <;> rfl)
    | (cases g.2.1[(p - 1 - x).toNat]? <;> rfl)

/-- The tape of a final configuration of `T9`, without the tags, is the one of (10,8). -/
theorem fin_fst (C : CTSH) (vf : List Ch) (mf : ℕ) (rm : List Ch)
    (hv : vf = [] ∨ ∃ v, vf = .Y :: v) (i : ℤ) :
    ((finCfg9 C vf mf rm).tape i).1 = (U10_8.finCfg C vf mf rm).tape i := by
  rcases hv with rfl | ⟨v, rfl⟩
  · have e : (tapeList9 C mf rm [] ++ [((Sy.s0, true) : TS)]).map Prod.fst =
        U10_8.tapeList C mf rm [] ++ [Sy.s0] := by
      simp [tapeList9, RA9, U10_8.tapeList, U10_8.RA, un, Function.comp_def, URTM.CTSH.U9_14.tagSt]
    have := congrFun (tp_map Prod.fst bk (tapeList9 C mf rm [] ++ [((Sy.s0, true) : TS)])) i
    simp only [e, CTSH.Sim.tp_trail] at this
    simp only [finCfg9, U10_8.finCfg, U10_8.tapeOf]
    exact this.symm
  · have e : (bk :: un (U10_8.Hi C 0) ++ ((Sy.s0, true) : TS) :: (Sy.s7, true) ::
        (un (rm.map U10_8.up) ++ (Sy.s1, true) :: un (v.map U10_8.lo))).map Prod.fst =
        U10_8.tapeList C 0 rm (.Y :: v) := by
      simp [U10_8.tapeList, U10_8.RA, prod, U10_8.Lo_zero, un, Function.comp_def, U10_8.lo]
    have := congrFun (tp_map Prod.fst bk (bk :: un (U10_8.Hi C 0) ++ ((Sy.s0, true) : TS) ::
      (Sy.s7, true) :: (un (rm.map U10_8.up) ++ (Sy.s1, true) :: un (v.map U10_8.lo)))) i
    simp only [e] at this
    simp only [finCfg9, U10_8.finCfg, U10_8.tapeOf]
    exact this.symm

theorem fin_erase (C : CTSH) (vf : List Ch) (mf : ℕ) (rm : List Ch)
    (hv : vf = [] ∨ ∃ v, vf = .Y :: v) (hm : vf = [] ∨ mf = 0) :
    eraseID (numCfg num9_14 (δ C) (finCfg9 C vf mf rm)) =
      numCfg U10_8.num10_8 (δ C) (U10_8.finCfg C vf mf rm) := by
  simp only [eraseID, numCfg]
  congr 1
  · rcases hv with rfl | ⟨v, rfl⟩ <;> rfl
  · rcases hv with rfl | ⟨v, rfl⟩ <;> rfl
  · funext x
    simp only [num9_14, U10_8.num10_8, syN9_mod, fin_fst C vf mf rm hv]

/-- A code of a final ID of `T9`. -/
theorem fin_code (C : CTSH) (vf : List Ch) (mf : ℕ) (rm : List Ch) (hv : vf = [] ∨ ∃ v, vf = .Y :: v) :
    ∃ g, Spec.toID (numCfg num9_14 (δ C) (finCfg9 C vf mf rm)).pos g =
      numCfg num9_14 (δ C) (finCfg9 C vf mf rm) := by
  rcases hv with rfl | ⟨v, rfl⟩
  · have := numCfg_tp (N := num9_14) bk rfl (δ C) (.halt .h0) (tapeList9 C mf rm [] ++ [(.s0, true)])
      ((U10_8.RA C mf).length + 2 + rm.length) (by simp [tapeList9, URTM.CTSH.U9_14.RA9_length, un]; omega)
    have e : finCfg9 C [] mf rm = ⟨.halt .h0, (((U10_8.RA C mf).length + 2 + rm.length : ℕ) : ℤ),
        CTSH.Sim.tp bk (tapeList9 C mf rm [] ++ [(.s0, true)])⟩ := by
      simp [finCfg9]
    rw [e, this]
    exact ⟨_, rfl⟩
  · have := numCfg_tp (N := num9_14) bk rfl (δ C) (.halt .h1)
      (bk :: un (U10_8.Hi C 0) ++ ((Sy.s0, true) : TS) :: (Sy.s7, true) ::
        (un (rm.map U10_8.up) ++ (Sy.s1, true) :: un (v.map U10_8.lo)))
      (U10_8.RA C 0).length (by simp [U10_8.RA, prod, U10_8.Lo_zero, un])
    have e : finCfg9 C (.Y :: v) mf rm = ⟨.halt .h1, (((U10_8.RA C 0).length : ℕ) : ℤ),
        CTSH.Sim.tp bk (bk :: un (U10_8.Hi C 0) ++ ((Sy.s0, true) : TS) :: (Sy.s7, true) ::
          (un (rm.map U10_8.up) ++ (Sy.s1, true) :: un (v.map U10_8.lo)))⟩ := by
      simp [finCfg9]
    rw [e, this]
    exact ⟨_, rfl⟩

/-- **The readout is right on every code of a halting ID of `T9`** (after erasing the tags). -/
theorem readU_fin (C : CTSH) (vf : List Ch) (mf : ℕ) (hmf : mf ≤ C.length) (rm : List Ch)
    (hv : vf = [] ∨ ∃ v, vf = .Y :: v) (hm : vf = [] ∨ mf = 0) (g : Code)
    (hg : Spec.toID (numCfg num9_14 (δ C) (finCfg9 C vf mf rm)).pos g =
      numCfg num9_14 (δ C) (finCfg9 C vf mf rm)) :
    readU (eraseCode g) = some (C.length, (vf, mf)) := by
  obtain ⟨p, hp⟩ := U10_8.finCfg_window C vf mf rm hm
  have h1 := toID_erase (numCfg num9_14 (δ C) (finCfg9 C vf mf rm)).pos g
  rw [hg, fin_erase C vf mf rm hv hm, hp] at h1
  have hpos : (numCfg num9_14 (δ C) (finCfg9 C vf mf rm)).pos = (p : ℤ) - δ C := by
    have h1 := congrArg Spec.ID.pos (fin_erase C vf mf rm hv hm)
    have h2 := congrArg Spec.ID.pos hp
    simp only [eraseID] at h1
    rw [h1, h2]; rfl
  rw [hpos] at h1
  rw [PadInv.readU_toID h1]
  exact U10_8.readU_window C mf hmf rm vf _ p

/-! ### The run-level simulation and the exit layer -/

theorem runSim_U9_14 (C : CTSH) (w : List Ch) :
    RunSim (CStep C) (Halting C) (Spec.Step U) (Spec.Halted U)
      (fun y γ => ∃ g, Spec.toID γ.pos g = γ ∧ readU (eraseCode g) = some (C.length, y))
      (w, 0) (Spec.toID 0 (encList C w)) := by
  have hmain := URTM.CTSH.U9_14.urtm9_14_simulates_ctsh C w
  rw [encList_eq9]
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
    exact ⟨_, (haltsAt_numCfg_iff (N := num9_14) T9 (δ C) _ _).mpr ⟨N, _, hN, rfl⟩, g, hg,
      readU_fin C vf mf hmf rm hv hm g hg⟩
  · obtain ⟨γ, hγ⟩ := hU
    obtain ⟨N, c', h, -⟩ := (haltsAt_numCfg_iff (N := num9_14) T9 (δ C) _ γ).mp hγ
    exact hmain.2.2.mp (fun n (f : CTSH.ID) hc => hn ⟨f, U10_8.rtg_of_cstepN hc.1, hc.2⟩) N c' h

/-- **Decoder** of URTM(9,14): erase the tags, then the (10,8) decoder. -/
def d9_14 (g : Code) : Option Code := Chain10_8.d10_8 (eraseCode g)

theorem d9_14_toID (p : ℤ) (g g' : Code) (h : toID p g = toID p g') : d9_14 g = d9_14 g' :=
  Chain10_8.d10_8_toID p _ _ (by rw [toID_erase, toID_erase, h])

theorem eraseCode_primrec : Primrec eraseCode := by
  have hm : Primrec₂ (fun (_ : Code) (x : ℕ) => x % 8) :=
    (Primrec.nat_mod.comp Primrec.snd (Primrec.const 8)).to₂
  exact Primrec.pair Primrec.fst (Primrec.pair
    (Primrec.list_map (Primrec.fst.comp Primrec.snd) hm)
    (Primrec.list_map (Primrec.snd.comp Primrec.snd) hm))

theorem d9_14_computable : Computable d9_14 :=
  ComputableDec.d10_8_computable.comp eraseCode_primrec.to_comp

theorem hout (n : ℕ) (a : Code) :
    RunSim TagToCTSH.stepC TagToCTSH.haltC (Spec.Step U) (Halted U)
      (fun y γ => ∃ g, toID γ.pos g = γ ∧ d9_14 g = Fin.decM y)
      (Fin.encMid (tbl n) a) (toID 0 (Chain10_8.c10_8 (n, a))) := by
  rw [Chain10_8.encMid_eq]
  have h := (Chain10_8.runSim_carry (Chain10_8.ctshOf (tbl n)) (Chain10_8.wordOf (tbl n) a, 0)).trans
    (runSim_U9_14 (Chain10_8.ctshOf (tbl n)) (Chain10_8.wordOf (tbl n) a))
  refine ⟨fun y hy => ?_, h.2⟩
  obtain ⟨γ, hγ, s', rfl, g, hg, hr⟩ := h.1 y hy
  exact ⟨γ, hγ, g, hg, by simp [d9_14, Chain10_8.d10_8, hr, Chain10_8.decM_eq]⟩

/-! ### The main theorems -/

theorem strictBody_U9_14 : DropGen.StrictBody U Chain10_8.c10_8 d9_14 :=
  strictBody_of_chain U Chain10_8.c10_8 d9_14
    (fun n => L0.CStep (tbl n)) (fun n => L0.CHalt (tbl n)) (fun n => Fin.Inv1 (tbl n))
    (fun _ => TagToCTSH.stepC) (fun _ => TagToCTSH.haltC)
    (fun n => Fin.encMid (tbl n)) Fin.decM
    (fun _ _ _ => isIDOf_encList9 _ _)
    Fin.hin1
    (fun n => Fin.mid (tbl n))
    (fun n a _ => hout n a)
    d9_14_toID

/-- **URTM(9,14) is a UTM in the strict sense of Morita Def. 7.1.** -/
theorem isUTMStrict_U : IsUTMStrict U :=
  DropGen.isUTMStrict_of_body ComputableEnc.c10_8_computable d9_14_computable strictBody_U9_14

/-- **Existence of URTM(9,14)** in the exact sense of Morita's Def. 7.1. No hypotheses. -/
theorem exists_urtm_9_14 :
    ∃ U : List Quint, Deterministic U ∧ Reversible U ∧ NStates U = 9 ∧ NSyms U = 14 ∧
      IsUTMStrict U :=
  ⟨U, U_det, U_rev, U_counts.1, U_counts.2, isUTMStrict_U⟩

end URTM.Univ.U9_14
