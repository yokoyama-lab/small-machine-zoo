/-
  **The block-converted machines** (docs/24 P7b): the common part of (4,46), (5,45), (6,37),
  (7,32), (8,28), (9,27).

  `T' = bconv T sp qs ss` (`URTM.KStateBlocks`) has states `Fin k` and symbols `KSym S`
  (`pl s`: plain, `ctr i s`: counter). Its configurations are `benc T sp c`: the plain image of
  `c`, except that in a real state the cell under the head is `ctr (v p) s`.

  * `numB N n`: the numbering of `T'` from a numbering `N` of the base machine with symbols
    `< n`: states `Fin k` by value, pseudo-states after them; `pl s ↦ N.sym s`,
    `ctr i s ↦ n·(i+1) + N.sym s`. So a plain tape of `T'` has the same numbers as the base
    machine's tape.
  * `encB q K z`: the code of the encoded initial ID from the base machine's code `z`: only the
    state and the cell under the head change (`encB_eq`).
  * `numCfg_benc_halt`: a halting configuration of `T'` on a list tape has the base machine's
    window with the new state number. Hence the base machine's readout serves `T'`.
  * `isUTMStrict_block`: `IsUTMStrict (numT (numB …) T')` from the base machine's encoder, its
    final shapes with a readout, and the CTSH theorem of `T'`.
  * `readM_fin`: the final shapes of the one-cell-per-letter family read by `MoritaGen.readM`,
    for an arbitrary numbering of the two pseudo-states.
-/
import LeanUniv.MoritaGen
import URTM.KStateBlocks

namespace URTM.Univ.BlockGen

set_option linter.unusedSectionVars false

open URTM URTM.CTSH URTM.Univ.KToSpec URTM.Univ.NumGen
open URTM.KState (Tgt Cfg Machine HaltsIn KSym)
open URTM.KStateBlocks (BSpec benc rst)
open URTM.Univ.U10_8 (loN)

/-! ### Numbering of the block machine -/

section Num
variable {Q P S : Type} [DecidableEq P] {k : ℕ}

/-- States `Fin k` by value; pseudo-states after them, by position in `ps`. -/
def stB (ps : List P) : Tgt (Fin k) P → ℕ
  | .go x => x.val
  | .halt h => k + ps.idxOf h

/-- `pl s ↦ N.sym s`, `ctr i s ↦ n·(i+1) + N.sym s`. -/
def syB (N : Numbering Q P S) (n : ℕ) : KSym S → ℕ
  | .pl s => N.sym s
  | .ctr i s => n * (i + 1) + N.sym s

theorem stB_inj (ps : List P) (hp : ∀ p, p ∈ ps) : Function.Injective (stB (k := k) ps) := by
  intro a b h
  cases a with
  | go a =>
    cases b with
    | go b => simp only [stB] at h; rw [Fin.ext h]
    | halt b => simp only [stB] at h; have := a.isLt; omega
  | halt a =>
    cases b with
    | go b => simp only [stB] at h; have := b.isLt; omega
    | halt b =>
      simp only [stB] at h
      have h' : ps.idxOf a = ps.idxOf b := by omega
      rw [(List.idxOf_inj (hp a)).mp h']

theorem syB_inj (N : Numbering Q P S) (n : ℕ) (hn : ∀ s, N.sym s < n) :
    Function.Injective (syB N n) := by
  intro a b h
  cases a with
  | pl s =>
    cases b with
    | pl s' => simp only [syB] at h; rw [N.sym_inj h]
    | ctr j s' =>
      simp only [syB, Nat.mul_succ] at h
      have := hn s
      omega
  | ctr i s =>
    cases b with
    | pl s' =>
      simp only [syB, Nat.mul_succ] at h
      have := hn s'
      omega
    | ctr j s' =>
      simp only [syB] at h
      have hpos : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) (hn s)
      have h1 := congrArg (· / n) h
      simp only [Nat.mul_add_div hpos, Nat.div_eq_of_lt (hn s), Nat.div_eq_of_lt (hn s')] at h1
      have hij : i = j := by omega
      subst hij
      have h2 : N.sym s = N.sym s' := by omega
      rw [N.sym_inj h2]

/-- **Numbering of the block machine** from a numbering of the base machine. -/
def numB (N : Numbering Q P S) (n : ℕ) (hn : ∀ s, N.sym s < n) (ps : List P)
    (hp : ∀ p, p ∈ ps) : Numbering (Fin k) P (KSym S) :=
  ⟨stB ps, syB N n, stB_inj ps hp, syB_inj N n hn⟩

end Num

/-! ### The encoder: the base code with a counter under the head -/

/-- The base code `z` with state `q` and `K` added to the cell under the head. -/
def encB (q K : ℕ) (z : Spec.Code) : Spec.Code :=
  (q, z.2.1, (K + z.2.2.getD 0 0) :: z.2.2.tail)

theorem toID_encB (q K : ℕ) (z : Spec.Code) :
    Spec.toID 0 (encB q K z) =
      ⟨q, 0, fun x => (if x = 0 then K else 0) + (Spec.toID 0 z).tape x⟩ := by
  simp only [Spec.toID, encB]
  congr 1
  funext x
  by_cases h1 : (0 : ℤ) ≤ x
  · rw [if_pos h1, if_pos h1]
    by_cases h2 : x = 0
    · subst h2; simp
    · obtain ⟨j, hj⟩ : ∃ j : ℕ, x = ((j + 1 : ℕ) : ℤ) := ⟨(x - 1).toNat, by omega⟩
      subst hj
      rw [if_neg h2]
      simp only [sub_zero, Int.toNat_natCast, List.getD_cons_succ, Nat.zero_add]
      rcases z.2.2 with _ | ⟨a, t⟩ <;> simp
  · rw [if_neg h1, if_neg h1, if_neg (by omega)]
    simp

open Primrec in
theorem encB_primrec (q K : ℕ) : Primrec (encB q K) :=
  pair (const q) (pair (fst.comp snd) (list_cons.comp
    (nat_add.comp (const K) ((list_getD 0).comp (snd.comp snd) (const 0)))
    (list_tail.comp (snd.comp snd))))

/-- The encoded initial ID is an ID of `U`. -/
theorem isIDOf_encB (U : List Quint) (q K : ℕ) (z : Spec.Code) (A B : List ℕ)
    (hq : q ∈ Spec.states U) (hl : ∀ a ∈ z.2.1, a ∈ A) (hr : ∀ a ∈ z.2.2, a ∈ B)
    (hA : ∀ a ∈ A ++ B, a = 0 ∨ a ∈ Spec.symbols U)
    (hK : ∀ a ∈ 0 :: B, K + a = 0 ∨ K + a ∈ Spec.symbols U) :
    Spec.IsIDOf U (Spec.toID 0 (encB q K z)) := by
  refine isIDOf_toID U 0 _ hq fun a ha => ?_
  simp only [encB, List.mem_append, List.mem_cons] at ha
  rcases ha with ha | rfl | ha
  · exact hA a (List.mem_append_left _ (hl a ha))
  · refine hK _ ?_
    rcases h : z.2.2 with _ | ⟨b, t⟩
    · simp
    · simp only [List.getD_cons_zero]
      exact List.mem_cons_of_mem _ (hr b (by rw [h]; simp))
  · exact hA a (List.mem_append_right _ (hr a (List.mem_of_mem_tail ha)))

section Typed
variable {Q P S : Type} [DecidableEq Q] [DecidableEq P] [DecidableEq S] {k : ℕ}
  (N : Numbering Q P S) (n : ℕ) (hn : ∀ s, N.sym s < n) (ps : List P) (hp : ∀ p, p ∈ ps)
  (T : Machine Q P S) (sp : BSpec Q k)

/-- The numbered image of an encoded configuration in a real state: the base tape numbers, plus
    `n·(v p + 1)` on the cell under the head. -/
theorem numCfg_benc_go (δ : ℤ) (c : Cfg Q P S) (p : Q) (hc : c.st = .go p) :
    numCfg (numB N n hn ps hp) δ (benc T sp c) =
      ⟨(rst T sp .h p).val, c.pos - δ,
        fun x => (if x = c.pos - δ then n * (sp.v p + 1) else 0) + N.sym (c.tape (x + δ))⟩ := by
  simp only [numCfg, benc, hc]
  congr 1
  funext x
  by_cases h : x + δ = c.pos
  · rw [if_pos h, if_pos (by omega)]; rfl
  · rw [if_neg h, if_neg (by omega)]; simp [numB, syB]

/-- **The encoder is the numbered, shifted encoded initial configuration**, given that the base
    code `z` is the numbered, shifted base initial configuration. -/
theorem encB_eq (δ : ℤ) (c : Cfg Q P S) (p : Q) (hc : c.st = .go p) (z : Spec.Code)
    (hz : Spec.toID 0 z = numCfg N δ c) :
    Spec.toID 0 (encB (rst T sp .h p).val (n * (sp.v p + 1)) z) =
      numCfg (numB N n hn ps hp) δ (benc T sp c) := by
  have hpos : c.pos - δ = 0 := (congrArg Spec.ID.pos hz).symm
  rw [toID_encB, numCfg_benc_go N n hn ps hp T sp δ c p hc, hz, hpos]
  rfl

/-- **A halting configuration on a list tape**: the encoded configuration has the base machine's
    window, with the state number of the block machine. -/
theorem numCfg_benc_halt (bk : S) (hbk : N.sym bk = 0) (δ : ℤ) (h : P) (L : List S) (p : ℕ)
    (hp' : p ≤ L.length) :
    numCfg (numB N n hn ps hp) δ (benc T sp ⟨.halt h, p, Sim.tp bk L⟩) =
      Spec.toID ((p : ℤ) - δ) (window (k + ps.idxOf h) (L.map N.sym) p) := by
  have h1 := numCfg_tp (N := N) bk hbk δ (.halt h) L p hp'
  have h2 : numCfg (numB N n hn ps hp) δ (benc T sp ⟨.halt h, p, Sim.tp bk L⟩) =
      ⟨k + ps.idxOf h, (numCfg N δ ⟨.halt h, p, Sim.tp bk L⟩).pos,
        (numCfg N δ ⟨.halt h, p, Sim.tp bk L⟩).tape⟩ := rfl
  rw [h2, h1]
  rfl

/-- **Body form** (docs/26) of `isUTMStrict_block` (no primitive recursiveness needed): a block-converted machine is a UTM in the strict sense of Morita Def. 7.1, given the base
    machine's encoder `enc0` (with `encEq`), the CTSH theorem of `T'` (halting forward `hsimF`,
    non-halting `hsimN`), and a readout `readN` that is right on the base machine's final
    shapes with the block machine's state numbers (`hfin`). -/
theorem strictBody_block (T' : Machine (Fin k) P (KSym S)) (bk : S) (hbk : N.sym bk = 0)
    (q0 : Q) (encC : CTSH → List Ch → Cfg Q P S)
    (finC : CTSH → List Ch → ℕ → List Ch → Cfg Q P S) (δ : CTSH → ℤ)
    (enc0 : CTSH → List Ch → Spec.Code)
    (hencEq : ∀ C w, Spec.toID 0 (enc0 C w) = numCfg N (δ C) (encC C w))
    (hq0 : ∀ C w, (encC C w).st = .go q0)
    (hsimF : ∀ C w n vf mf, CHaltsIn C n (w, 0) (vf, mf) →
      ∃ M rm, n ≤ M ∧ HaltsIn T' M (benc T sp (encC C w)) (benc T sp (finC C vf mf rm)))
    (hsimN : ∀ C w, (∀ n f, ¬ CHaltsIn C n (w, 0) f) →
      ∀ M c, ¬ HaltsIn T' M (benc T sp (encC C w)) c)
    (readN : Spec.Code → Option (ℕ × List ℕ))
    (hinv : ∀ p g g', Spec.toID p g = Spec.toID p g' → readN g = readN g')
    (hfin : ∀ C vf mf rm, Halting C (vf, mf) → ∃ (h : P) (L : List S) (p : ℕ), p ≤ L.length ∧
      finC C vf mf rm = ⟨.halt h, p, Sim.tp bk L⟩ ∧
      readN (window (k + ps.idxOf h) (L.map N.sym) p) = some (C.length, vf.map loN))
    (A B : List ℕ) (hl : ∀ C w, ∀ a ∈ (enc0 C w).2.1, a ∈ A)
    (hr : ∀ C w, ∀ a ∈ (enc0 C w).2.2, a ∈ B)
    (hU0 : (rst T sp .h q0).val ∈ Spec.states (numT (numB N n hn ps hp) T'))
    (hUA : ∀ a ∈ A ++ B, a = 0 ∨ a ∈ Spec.symbols (numT (numB N n hn ps hp) T'))
    (hUK : ∀ a ∈ 0 :: B, n * (sp.v q0 + 1) + a = 0 ∨
      n * (sp.v q0 + 1) + a ∈ Spec.symbols (numT (numB N n hn ps hp) T')) :
    DropGen.StrictBody (numT (numB N n hn ps hp) T')
      (ChainGen.cOf (fun C w => encB (rst T sp .h q0).val (n * (sp.v q0 + 1)) (enc0 C w)))
      (GenDec.dOf readN) := by
  refine ChainGen.strictBody_of_ctsh _
    (fun C w => encB (rst T sp .h q0).val (n * (sp.v q0 + 1)) (enc0 C w)) readN
    (fun C w => isIDOf_encB _ _ _ _ A B hU0 (hl C w) (hr C w) hUA hUK) (fun C w => ?_) hinv
  rw [encB_eq N n hn ps hp T sp (δ C) (encC C w) q0 (hq0 C w) _ (hencEq C w)]
  refine runSim_of_sim _ T' _ C w _ (fun f c => ∃ rm, c = benc T sp (finC C f.1 f.2 rm)) _
    (fun m f hf => ?_) (hsimN C w) (fun f c hf hc => ?_)
  · obtain ⟨M, rm, -, h⟩ := hsimF C w m f.1 f.2 hf
    exact ⟨M, _, h, rm, rfl⟩
  · obtain ⟨rm, rfl⟩ := hc
    obtain ⟨h, L, p, hp', hfin', hrd⟩ := hfin C f.1 f.2 rm hf
    rw [hfin']
    exact ⟨_, (numCfg_benc_halt N n hn ps hp T sp bk hbk (δ C) h L p hp').symm, hrd⟩

/-- **A block-converted machine is a UTM in the strict sense of Morita Def. 7.1**, given the base
    machine's encoder `enc0` (with `encEq`), the CTSH theorem of `T'` (halting forward `hsimF`,
    non-halting `hsimN`), and a readout `readN` that is right on the base machine's final
    shapes with the block machine's state numbers (`hfin`). -/
theorem isUTMStrict_block (T' : Machine (Fin k) P (KSym S)) (bk : S) (hbk : N.sym bk = 0)
    (q0 : Q) (encC : CTSH → List Ch → Cfg Q P S)
    (finC : CTSH → List Ch → ℕ → List Ch → Cfg Q P S) (δ : CTSH → ℤ)
    (enc0 : CTSH → List Ch → Spec.Code) (henc0 : Primrec₂ enc0)
    (hencEq : ∀ C w, Spec.toID 0 (enc0 C w) = numCfg N (δ C) (encC C w))
    (hq0 : ∀ C w, (encC C w).st = .go q0)
    (hsimF : ∀ C w n vf mf, CHaltsIn C n (w, 0) (vf, mf) →
      ∃ M rm, n ≤ M ∧ HaltsIn T' M (benc T sp (encC C w)) (benc T sp (finC C vf mf rm)))
    (hsimN : ∀ C w, (∀ n f, ¬ CHaltsIn C n (w, 0) f) →
      ∀ M c, ¬ HaltsIn T' M (benc T sp (encC C w)) c)
    (readN : Spec.Code → Option (ℕ × List ℕ)) (hread : Primrec readN)
    (hinv : ∀ p g g', Spec.toID p g = Spec.toID p g' → readN g = readN g')
    (hfin : ∀ C vf mf rm, Halting C (vf, mf) → ∃ (h : P) (L : List S) (p : ℕ), p ≤ L.length ∧
      finC C vf mf rm = ⟨.halt h, p, Sim.tp bk L⟩ ∧
      readN (window (k + ps.idxOf h) (L.map N.sym) p) = some (C.length, vf.map loN))
    (A B : List ℕ) (hl : ∀ C w, ∀ a ∈ (enc0 C w).2.1, a ∈ A)
    (hr : ∀ C w, ∀ a ∈ (enc0 C w).2.2, a ∈ B)
    (hU0 : (rst T sp .h q0).val ∈ Spec.states (numT (numB N n hn ps hp) T'))
    (hUA : ∀ a ∈ A ++ B, a = 0 ∨ a ∈ Spec.symbols (numT (numB N n hn ps hp) T'))
    (hUK : ∀ a ∈ 0 :: B, n * (sp.v q0 + 1) + a = 0 ∨
      n * (sp.v q0 + 1) + a ∈ Spec.symbols (numT (numB N n hn ps hp) T')) :
    Spec.IsUTMStrict (numT (numB N n hn ps hp) T') :=
  ChainGen.isUTMStrict_of_body_ctsh ((encB_primrec _ _).comp₂ henc0) hread
    (strictBody_block N n hn ps hp T sp T' bk hbk q0 encC finC δ enc0 hencEq hq0 hsimF hsimN readN
      hinv hfin A B hl hr hU0 hUA hUK)

end Typed

/-! ### The entries of the base encoders -/

theorem encM_left (q0 x s : ℕ) (C : CTSH) (w : List Ch) :
    ∀ a ∈ (MoritaGen.encM q0 x s C w).2.1, a ∈ [x, 0, s, 1, 2] := by
  intro a ha
  simp only [MoritaGen.encM, List.mem_append, List.mem_cons, List.mem_flatMap, List.mem_map,
    List.not_mem_nil, or_false] at ha
  rcases ha with (rfl | rfl | ⟨u, -, rfl | ⟨c, -, rfl⟩⟩) | rfl
  · simp
  · simp
  · simp
  · cases c <;> simp [loN]
  · simp

theorem encM_right (q0 x s : ℕ) (C : CTSH) (w : List Ch) :
    ∀ a ∈ (MoritaGen.encM q0 x s C w).2.2, a ∈ [1, 2] := by
  intro a ha
  obtain ⟨c, -, rfl⟩ := List.mem_map.mp ha
  cases c <;> simp [loN]

/-! ### The final shapes of the one-cell-per-letter family, for any numbering of the pseudo-states -/

open MoritaGen in
/-- The final shapes of the one-cell-per-letter family (as in `isUTMStrict_morita`) are read by
    `readM (stn hhalt) (N.sym st) e` when the pseudo-states are numbered by `stn`. -/
theorem readM_fin {Q P S : Type} [DecidableEq S] (N : Numbering Q P S) (lo : Ch → S)
    (st bk : S) (hnull hhalt : P) (e : ℕ) (hlo : ∀ c, N.sym (lo c) = loN c)
    (hls : ∀ c, lo c ≠ st) (stn : P → ℕ) (hnh : stn hnull ≠ stn hhalt)
    (finC : CTSH → List Ch → ℕ → List Ch → Cfg Q P S)
    (hnullfin : ∀ C mf rm, mf ≤ C.length → ∃ (L : List S) (p : ℕ), p ≤ L.length ∧
      finC C [] mf rm = ⟨.halt hnull, p, Sim.tp bk L⟩ ∧ L.count st = C.length)
    (hhaltfin : ∀ C v rm, ∃ (A : List S) (mk : S) (p : ℕ), p ≤ (A ++ mk :: v.map lo).length ∧
      finC C (.Y :: v) 0 rm = ⟨.halt hhalt, p, Sim.tp bk (A ++ mk :: v.map lo)⟩ ∧
      (A ++ [mk]).count st - e = C.length ∧ N.sym mk ≠ 0 ∧ N.sym mk ≠ 1 ∧ N.sym mk ≠ 2)
    (C : CTSH) (vf : List Ch) (mf : ℕ) (rm : List Ch) (hf : Halting C (vf, mf)) :
    ∃ (h : P) (L : List S) (p : ℕ), p ≤ L.length ∧
      finC C vf mf rm = ⟨.halt h, p, Sim.tp bk L⟩ ∧
      readM (stn hhalt) (N.sym st) e (window (stn h) (L.map N.sym) p) =
        some (C.length, vf.map loN) := by
  obtain ⟨hk, hv | hv⟩ := hf
  · obtain ⟨v, hv1, hv2⟩ := hv
    simp only at hv1 hv2
    subst hv1 hv2
    obtain ⟨A, mk, p, hp, hfin, hc, hm0, hm1, hm2⟩ := hhaltfin C v rm
    refine ⟨hhalt, _, p, hp, hfin, ?_⟩
    rw [List.map_append, List.map_cons, map_lo N lo hlo, readM_halt _ _ _ _ _ hm0 hm1 hm2]
    have hcnt : (A.map N.sym ++ N.sym mk :: v.map loN).count (N.sym st) =
        (A ++ [mk]).count st := by
      rw [← map_lo N lo hlo, ← List.map_cons, ← List.map_append,
        List.count_map_of_injective _ _ N.sym_inj]
      simp [List.count_append, List.count_cons, count_lo lo st hls]
    rw [hcnt, hc]
  · simp only at hv
    subst hv
    obtain ⟨L, p, hp, hfin, hc⟩ := hnullfin C mf rm (by simp [CTSH.k] at hk; omega)
    refine ⟨hnull, L, p, hp, hfin, ?_⟩
    rw [readM_null _ _ _ _ hnh, List.count_map_of_injective _ _ N.sym_inj, hc]
    rfl

end URTM.Univ.BlockGen
