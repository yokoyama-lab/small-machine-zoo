/-
  **Morita's hand-designed machines with one cell per letter** (docs/24 P7a): the common part
  of (13,7), (15,6), (17,5) and (24,4).

  These four machines share the rule region `Sim.RA lo st bk` of `URTM.CTSHSim` (the rules in
  lower case, separated by `∗`, one phase marker `b`) and Morita's initial ID

      b ϕ₁(w^R_{k−1}) ∗ ⋯ ∗ ϕ₁(w^R_1) ∗ b x q_begin ϕ₁(w) b        (x = `$` or `b`).

  * `encM q0 x s C w`: the Spec code of that ID (list level; `encM_primrec`, `encM_eq`,
    `isIDOf_encM`).
  * `readM hs s e g`: the readout from a code `g` of the halting ID. With `L` the whole window:
    in the pseudo-state `hs` (Morita's `halt`, final CTSH ID `(Y v, 0)`) it returns
    `(#∗ in L − e, 1 :: the lower-case letters at the right end of L)`; in any other state
    (Morita's `null`, final CTSH ID `(λ, m)`) it returns `(#∗ in L, [])`.
    It sees only the state and the window list and ignores trailing blanks (`readM_toID`),
    and it is primitive recursive (`readM_primrec`).
  * `isUTMStrict_morita`: `IsUTMStrict (numT N T)` from the machine's CTSH theorem and the
    shapes of its initial and final configurations.
-/
import LeanUniv.NumGen
import LeanUniv.ChainGen

namespace URTM.Univ.MoritaGen
open URTM URTM.CTSH URTM.Univ.KToSpec URTM.Univ.NumGen
open URTM.Univ.U10_8 (loN)
open URTM.KState (Tgt Cfg Machine HaltsIn)

/-! ### The list-level encoder -/

/-- **Encoder** (list level). State `q0` (`begin`); left of the head, nearest first: the
    separator `x`, the phase marker `b = 0`, then for each production `∗ ϕ₁(w_i)` (`∗ = s`),
    then the left end `b`; from the head: `ϕ₁(w)`. -/
def encM (q0 x s : ℕ) (C : CTSH) (w : List Ch) : Spec.Code :=
  (q0, x :: 0 :: C.flatMap (fun u => s :: u.map loN) ++ [0], w.map loN)

open Primrec in
theorem encM_primrec (q0 x s : ℕ) : Primrec₂ (encM q0 x s) := by
  have C := (fst : Primrec fun p : URTM.CTSH.CTSH × List Ch => p.1)
  have w := (snd : Primrec fun p : URTM.CTSH.CTSH × List Ch => p.2)
  have fl := list_flatMap C
    (list_cons.comp (const s) (list_map snd (ComputableEnc.loN_primrec.comp snd).to₂)).to₂
  exact (pair (const q0) (pair (list_append.comp (list_cons.comp (const x)
    (list_cons.comp (const 0) fl)) (const [0]))
    (list_map w (ComputableEnc.loN_primrec.comp snd).to₂))).of_eq fun _ => rfl

/-- The encoded initial ID is an ID of `U`. -/
theorem isIDOf_encM (U : List Quint) (q0 x s : ℕ) (h0 : q0 ∈ Spec.states U)
    (hs : ∀ a ∈ [1, 2, x, s], a = 0 ∨ a ∈ Spec.symbols U) (C : CTSH) (w : List Ch) :
    Spec.IsIDOf U (Spec.toID 0 (encM q0 x s C w)) := by
  have hlo : ∀ c : Ch, loN c = 1 ∨ loN c = 2 := by intro c; cases c <;> simp [loN]
  have key : ∀ a, (a = 0 ∨ a = 1 ∨ a = 2 ∨ a = x ∨ a = s) → a = 0 ∨ a ∈ Spec.symbols U := by
    rintro a (rfl | rfl | rfl | rfl | rfl)
    · exact .inl rfl
    · exact hs _ (by simp)
    · exact hs _ (by simp)
    · exact hs _ (by simp)
    · exact hs _ (by simp)
  refine isIDOf_toID U 0 _ h0 fun a ha => key a ?_
  simp only [encM, List.mem_append, List.mem_cons, List.mem_flatMap, List.mem_map,
    List.not_mem_nil, or_false] at ha
  rcases ha with ((rfl | rfl | ⟨u, -, rfl | ⟨c, -, rfl⟩⟩) | rfl) | ⟨c, -, rfl⟩
  · simp
  · simp
  · simp
  · rcases hlo c with h | h <;> simp [h]
  · simp
  · rcases hlo c with h | h <;> simp [h]

/-! ### The typed rule region, numbered -/

section Typed
variable {Q P S : Type} (N : Numbering Q P S) (lo : Ch → S) (st bk : S)

theorem map_lo (hlo : ∀ c, N.sym (lo c) = loN c) (u : List Ch) :
    (u.map lo).map N.sym = u.map loN := by
  rw [List.map_map]
  exact List.map_congr_left fun c _ => hlo c

theorem Hi_zero_rev (hlo : ∀ c, N.sym (lo c) = loN c) (C : CTSH) :
    ((Sim.Hi lo st C 0).map N.sym).reverse = C.flatMap (fun u => N.sym st :: u.map loN) := by
  induction C with
  | nil => rfl
  | cons u C ih =>
    have : Sim.Hi lo st (u :: C) 0 = Sim.Hi lo st C 0 ++ (u.reverse.map lo ++ [st]) := by
      simp [Sim.Hi]
    rw [this, List.map_append, List.reverse_append, ih]
    simp [map_lo N lo hlo]

/-- The encoder is the numbered, shifted typed initial configuration. -/
theorem encM_eq (hbk : N.sym bk = 0) (hlo : ∀ c, N.sym (lo c) = loN c) (q : Q) (x : S)
    (C : CTSH) (w : List Ch) :
    Spec.toID 0 (encM (N.st (.go q)) (N.sym x) (N.sym st) C w) =
      numCfg N (((Sim.RA lo st bk C 0).length + 2 : ℕ) : ℤ)
        ⟨.go q, (((Sim.RA lo st bk C 0).length + 2 : ℕ) : ℤ),
          Sim.tp bk (bk :: Sim.RA lo st bk C 0 ++ x :: w.map lo)⟩ := by
  have hL : bk :: Sim.RA lo st bk C 0 ++ x :: w.map lo =
      (bk :: Sim.RA lo st bk C 0 ++ [x]) ++ w.map lo := by simp
  have hp : (Sim.RA lo st bk C 0).length + 2 =
      ((bk :: Sim.RA lo st bk C 0 ++ [x]).map N.sym).length := by simp
  rw [numCfg_tp bk hbk _ _ _ _ (by simp), sub_self]
  congr 1
  simp only [window]
  rw [hL, List.map_append, List.take_left' hp.symm, List.drop_left' hp.symm]
  simp only [encM, Sim.RA_zero, List.map_append, List.map_cons, List.map_nil,
    List.reverse_append, List.reverse_cons, List.reverse_nil, Hi_zero_rev N lo st hlo,
    map_lo N lo hlo, hbk]
  simp

variable [DecidableEq S]

theorem count_lo (hls : ∀ c, lo c ≠ st) (u : List Ch) : (u.map lo).count st = 0 :=
  List.count_eq_zero.mpr fun h => by
    obtain ⟨c, -, hc⟩ := List.mem_map.mp h
    exact hls c hc

theorem count_blk (hls : ∀ c, lo c ≠ st) (L : List (List Ch)) :
    ((L.map (fun w => w.reverse.map lo ++ [st])).flatten).count st = L.length := by
  induction L with
  | nil => rfl
  | cons u L ih =>
    simp only [List.map_cons, List.flatten_cons, List.count_append, count_lo lo st hls, ih,
      List.count_singleton_self, List.length_cons]
    omega

/-- The rule region holds exactly `|C|` separators `∗`, in every phase. -/
theorem count_RA (hls : ∀ c, lo c ≠ st) (hbs : bk ≠ st) (C : CTSH) {m : ℕ}
    (hm : m ≤ C.length) : (Sim.RA lo st bk C m).count st = C.length := by
  simp only [Sim.RA, Sim.Hi, Sim.Lo, List.count_append, List.count_cons, count_blk lo st hls,
    count_lo lo st hls]
  split
  · simp [hbs]; omega
  · simp only [Sim.LoCore, List.count_append, count_blk lo st hls, List.count_singleton_self]
    simp [hbs]; omega

end Typed

/-! ### The readout -/

/-- The lower-case letters (`1 = y`, `2 = n`) at the right end of the window, trailing blanks
    aside. -/
def lowSuffix (L : List ℕ) : List ℕ :=
  ((L.reverse.dropWhile (· == 0)).takeWhile (fun a => a == 1 || a == 2)).reverse

/-- The readout on the state `q` and the whole window list `L`. -/
def readL (hs s e : ℕ) (q : ℕ) (L : List ℕ) : ℕ × List ℕ :=
  if q = hs then (L.count s - e, 1 :: lowSuffix L) else (L.count s, [])

/-- **Readout** (list level) from a code `g` of the halting ID: `(|C|, ϕ₁(vf))`. -/
def readM (hs s e : ℕ) (g : Spec.Code) : Option (ℕ × List ℕ) :=
  some (readL hs s e g.1 (g.2.1.reverse ++ g.2.2))

theorem lowSuffix_padL (k : ℕ) (L : List ℕ) :
    lowSuffix (List.replicate k 0 ++ L) = lowSuffix L := by
  simp only [lowSuffix, List.reverse_append, List.reverse_replicate]
  have H := PadInv.dw_append_rep_true (p := (· == 0)) rfl L.reverse k
  rcases hA : L.reverse.dropWhile (· == 0) with _ | ⟨x, t⟩
  · rw [H.1 hA]
  · rw [(H.2 x t hA).1, ← List.cons_append,
      PadInv.tw_append_rep (p := fun a => a == 1 || a == 2) rfl]

theorem lowSuffix_padR (k : ℕ) (L : List ℕ) :
    lowSuffix (L ++ List.replicate k 0) = lowSuffix L := by
  simp only [lowSuffix, List.reverse_append, List.reverse_replicate]
  rw [PadInv.dw_rep_append (p := (· == 0)) rfl]

theorem count_padL {s : ℕ} (hs : s ≠ 0) (k : ℕ) (L : List ℕ) :
    (List.replicate k 0 ++ L).count s = L.count s := by
  simp [List.count_append, List.count_replicate, Ne.symm hs]

theorem count_padR {s : ℕ} (hs : s ≠ 0) (k : ℕ) (L : List ℕ) :
    (L ++ List.replicate k 0).count s = L.count s := by
  simp [List.count_append, List.count_replicate, Ne.symm hs]

/-- **The readout depends only on the ID**, not on the code chosen for it. -/
theorem readM_toID (hs s e : ℕ) (h0 : s ≠ 0) {p : ℤ} {g g' : Spec.Code}
    (h : Spec.toID p g = Spec.toID p g') : readM hs s e g = readM hs s e g' :=
  congrArg some (read_toID (readL hs s e)
    (fun q k L => by simp only [readL, count_padL h0, lowSuffix_padL])
    (fun q k L => by simp only [readL, count_padR h0, lowSuffix_padR]) h)

theorem lowSuffix_mark (A : List ℕ) (m : ℕ) (hm0 : m ≠ 0) (hm1 : m ≠ 1) (hm2 : m ≠ 2)
    (v : List Ch) : lowSuffix (A ++ m :: v.map loN) = v.map loN := by
  have hX : ∀ a ∈ (v.map loN).reverse, (a == 1 || a == 2) = true := by
    intro a ha
    rw [List.mem_reverse] at ha
    obtain ⟨c, -, rfl⟩ := List.mem_map.mp ha
    cases c <;> rfl
  have hm : (m == 1 || m == 2) = false := by simp [hm1, hm2]
  have hd : ((v.map loN).reverse ++ m :: A.reverse).dropWhile (· == 0) =
      (v.map loN).reverse ++ m :: A.reverse := by
    rcases hv : (v.map loN).reverse with _ | ⟨a, X⟩
    · simp [hm0]
    · have ha := hX a (by rw [hv]; simp)
      have : (a == 0) = false := by
        rcases Nat.eq_zero_or_pos a with h | h
        · subst h; simp at ha
        · simpa using Nat.pos_iff_ne_zero.mp h
      simp [this]
  simp only [lowSuffix, List.reverse_append, List.reverse_cons, List.append_assoc,
    List.singleton_append]
  rw [hd, (U10_8.takeWhile_append_of_all hX m hm _).1, List.reverse_reverse]

theorem readM_null (hs s e q : ℕ) (hq : q ≠ hs) (L : List ℕ) (p : ℕ) :
    readM hs s e (window q L p) = some (L.count s, []) := by
  simp only [readM, window_whole, window_st, readL, if_neg hq]

theorem readM_halt (hs s e : ℕ) (A : List ℕ) (m : ℕ) (hm0 : m ≠ 0) (hm1 : m ≠ 1)
    (hm2 : m ≠ 2) (v : List Ch) (p : ℕ) :
    readM hs s e (window hs (A ++ m :: v.map loN) p) =
      some ((A ++ m :: v.map loN).count s - e, (Ch.Y :: v).map loN) := by
  simp only [readM, window_whole, window_st, readL, if_true, lowSuffix_mark A m hm0 hm1 hm2]
  rfl

open Primrec in
theorem lowSuffix_primrec : Primrec lowSuffix := by
  have p0 : Primrec fun a : ℕ => a == 0 := Primrec.beq.comp .id (const 0)
  have p12 : Primrec fun a : ℕ => a == 1 || a == 2 :=
    Primrec.or.comp (Primrec.beq.comp .id (const 1)) (Primrec.beq.comp .id (const 2))
  exact list_reverse.comp ((list_takeWhile p12).comp ((list_dropWhile p0).comp list_reverse))

open Primrec in
theorem readM_primrec (hs s e : ℕ) : Primrec (readM hs s e) := by
  have hL : Primrec fun g : Spec.Code => g.2.1.reverse ++ g.2.2 :=
    list_append.comp (list_reverse.comp (fst.comp snd)) (snd.comp snd)
  have hc : Primrec fun g : Spec.Code => (g.2.1.reverse ++ g.2.2).count s :=
    ComputableDec.list_count (const s) hL
  exact (option_some.comp (Primrec.ite (Primrec.eq.comp fst (const hs))
    (pair (nat_sub.comp hc (const e)) (list_cons.comp (const 1) (lowSuffix_primrec.comp hL)))
    (pair hc (const [])))).of_eq fun g => by simp only [readM, readL]

/-! ### The family theorem -/

/-- **Body form** (docs/26) of `isUTMStrict_morita`: the body of `IsUTMStrict` for the encoder
    `cOf (encM …)` and the decoder `dOf (readM …)`. Same hypotheses. Original statement:
    a machine of the one-cell-per-letter family is a UTM in the strict sense of Morita
    Def. 7.1. Hypotheses: the numbering sends the blank to `0`, `y, n` to `1, 2`; the initial
    configuration is Morita's; the machine's CTSH theorem (`hsim`); the final configuration for
    `(λ, m)` is in the pseudo-state `hnull` on a list tape with exactly `|C|` separators; the
    final configuration for `(Y v, 0)` is in the pseudo-state `hhalt` on a list tape that ends
    with a marker `mk` followed by `ϕ₁(v)` and holds `|C| + e` separators. -/
theorem strictBody_morita {Q P S : Type} [DecidableEq S] (N : Numbering Q P S)
    (T : Machine Q P S) (lo : Ch → S) (st bk x : S) (q0 : Q) (hnull hhalt : P) (e : ℕ)
    (hbk : N.sym bk = 0) (hlo : ∀ c, N.sym (lo c) = loN c) (hls : ∀ c, lo c ≠ st)
    (hst0 : N.sym st ≠ 0) (hnh : hnull ≠ hhalt)
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
      finC C [] mf rm = ⟨.halt hnull, p, Sim.tp bk L⟩ ∧ L.count st = C.length)
    (hhaltfin : ∀ C v rm, ∃ (A : List S) (mk : S) (p : ℕ), p ≤ (A ++ mk :: v.map lo).length ∧
      finC C (.Y :: v) 0 rm = ⟨.halt hhalt, p, Sim.tp bk (A ++ mk :: v.map lo)⟩ ∧
      (A ++ [mk]).count st - e = C.length ∧ N.sym mk ≠ 0 ∧ N.sym mk ≠ 1 ∧ N.sym mk ≠ 2)
    (hU0 : N.st (.go q0) ∈ Spec.states (numT N T))
    (hUs : ∀ a ∈ [1, 2, N.sym x, N.sym st], a = 0 ∨ a ∈ Spec.symbols (numT N T)) :
    DropGen.StrictBody (numT N T) (ChainGen.cOf (encM (N.st (.go q0)) (N.sym x) (N.sym st)))
      (GenDec.dOf (readM (N.st (.halt hhalt)) (N.sym st) e)) := by
  refine ChainGen.strictBody_of_ctsh (numT N T) (encM (N.st (.go q0)) (N.sym x) (N.sym st))
    (readM (N.st (.halt hhalt)) (N.sym st) e)
    (fun C w => isIDOf_encM _ _ _ _ hU0 hUs C w) (fun C w => ?_)
    (fun p g g' h => readM_toID _ _ _ hst0 h)
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
      simp only [hfin]
      refine read_of_tp N bk hbk _ _ _ p hp _ _ ?_
      rw [readM_null _ _ _ _ (fun h => hnh (Tgt.halt.inj (N.st_inj h))),
        List.count_map_of_injective _ _ N.sym_inj, hc]
      rfl

/-- **A machine of the one-cell-per-letter family is a UTM in the strict sense of Morita
    Def. 7.1.** Hypotheses: the numbering sends the blank to `0`, `y, n` to `1, 2`; the initial
    configuration is Morita's; the machine's CTSH theorem (`hsim`); the final configuration for
    `(λ, m)` is in the pseudo-state `hnull` on a list tape with exactly `|C|` separators; the
    final configuration for `(Y v, 0)` is in the pseudo-state `hhalt` on a list tape that ends
    with a marker `mk` followed by `ϕ₁(v)` and holds `|C| + e` separators. -/
theorem isUTMStrict_morita {Q P S : Type} [DecidableEq S] (N : Numbering Q P S)
    (T : Machine Q P S) (lo : Ch → S) (st bk x : S) (q0 : Q) (hnull hhalt : P) (e : ℕ)
    (hbk : N.sym bk = 0) (hlo : ∀ c, N.sym (lo c) = loN c) (hls : ∀ c, lo c ≠ st)
    (hst0 : N.sym st ≠ 0) (hnh : hnull ≠ hhalt)
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
      finC C [] mf rm = ⟨.halt hnull, p, Sim.tp bk L⟩ ∧ L.count st = C.length)
    (hhaltfin : ∀ C v rm, ∃ (A : List S) (mk : S) (p : ℕ), p ≤ (A ++ mk :: v.map lo).length ∧
      finC C (.Y :: v) 0 rm = ⟨.halt hhalt, p, Sim.tp bk (A ++ mk :: v.map lo)⟩ ∧
      (A ++ [mk]).count st - e = C.length ∧ N.sym mk ≠ 0 ∧ N.sym mk ≠ 1 ∧ N.sym mk ≠ 2)
    (hU0 : N.st (.go q0) ∈ Spec.states (numT N T))
    (hUs : ∀ a ∈ [1, 2, N.sym x, N.sym st], a = 0 ∨ a ∈ Spec.symbols (numT N T)) :
    Spec.IsUTMStrict (numT N T) :=
  ChainGen.isUTMStrict_of_body_ctsh (encM_primrec _ _ _) (readM_primrec _ _ _)
    (strictBody_morita N T lo st bk x q0 hnull hhalt e hbk hlo hls hst0 hnh encC finC henc hsim
      hnullfin hhaltfin hU0 hUs)

end URTM.Univ.MoritaGen
