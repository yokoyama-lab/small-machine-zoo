/-
  **URTM(85,2) as a Spec table, and its universality in the sense of Def. 7.1** (docs/24 P7c).

  `U = numT num M`: the 2-symbol machine `URTM.Gen.FS85_2.M` (153 quintuples; the symbol
  reduction of docs/23 applied to Morita's (13,7), record of autoresearch/frontier), numbered by
  `go n ↦ n + 2` (pseudo-states `h0, h1 ↦ 0, 1` do not occur in `M`), `false, true ↦ 0, 1`.

  A configuration of (13,7) is encoded with 3 bits per cell (`FewSym.enc`, code `FS85_2.code`),
  the head on the first bit of its block. `M` has no halting quintuples: where (13,7) would apply
  its halting quintuple (`begin` or `case_y_1` reading the blank), `M` has no quintuple for the
  state `ρ begin = 2` / `ρ case_y_1 = 7` on `0`, and halts inside the block without having moved
  (`hrun_q`). So the final tape is the 3-bit encoding of the final tape of (13,7) (`fin85_eq`).

  * `encList C w`: the bits of the (13,7) initial code (`MoritaGen.encM`), `encList_eq`.
  * `readU g`: cut both lists of the code into blocks of 3 bits from the head outwards, decode
    each block to a symbol number of (13,7) (`decB`), and apply the (13,7) readout
    `MoritaGen.readL` with the state `ρ case_y_1 + 2 = 9` in the role of `halt`.
    `readU_toID`: it depends only on the ID; `readU_primrec`.
  * `isUTMStrict_U`: `IsUTMStrict U` by `ChainGen.isUTMStrict_of_ctsh`.
-/
import LeanUniv.BlockGen
import LeanUniv.ReadGen
import LeanUniv.U13_7
import URTM.CTSH85_2Main

namespace URTM.Univ.U85_2
open URTM URTM.CTSH URTM.Gen.K13_7 URTM.Univ.KToSpec URTM.Univ.NumGen URTM.Univ.MoritaGen
open URTM.KState (Tgt Cfg Machine HaltsIn)
open URTM.FewSym (bits enc pre glob hrun hfuel LCfg ovl ovl_block)
open URTM.Gen.FS85_2 (M E code)
open URTM.CTSH.U85_2 (E85 fin85 f13 urtm85_2_simulates_ctsh)
open URTM.CTSH.U13_7 (nm13 encC13 finCfg13)
open URTM.Univ.U10_8 (loN)
open URTM.Univ.U13_7 (lo13 hls)

/-! ### Numbering and the Spec table -/

/-- `go n ↦ n + 2`; the pseudo-states (which do not occur in `M`) `h0, h1 ↦ 0, 1`. -/
def stN : Tgt ℕ Ps → ℕ
  | .go n => n + 2
  | .halt .h0 => 0
  | .halt .h1 => 1

def syN : Bool → ℕ
  | false => 0
  | true => 1

theorem stN_inj : Function.Injective stN := by
  intro a b h
  rcases a with a | a <;> rcases b with b | b
  · simp only [stN] at h; rw [show a = b by omega]
  · cases b <;> simp only [stN] at h <;> omega
  · cases a <;> simp only [stN] at h <;> omega
  · cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

theorem syN_inj : Function.Injective syN := by
  intro a b h
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

/-- The numbering of URTM(85,2). -/
def num : Numbering ℕ Ps Bool := ⟨stN, syN, stN_inj, syN_inj⟩

/-- **URTM(85,2) as a Spec table** (153 quintuples). -/
def U : List Quint := numT num M

/-- **Counts** (Morita's convention): 85 states, 2 symbols. -/
theorem U_counts : Spec.NStates U = 85 ∧ Spec.NSyms U = 2 := by decide +kernel
theorem U_det : Spec.Deterministic U := by decide +kernel
theorem U_rev : Spec.Reversible U := by decide +kernel

/-- `U` has no halting quintuple and no pseudo-state: every target state has outgoing
    quintuples, and no quintuple is a 0-shift. It halts where no quintuple applies. -/
theorem U_noPseudo : ∀ r ∈ U, r.q ∈ U.map Quint.p ∧ r.d ≠ .Z := by decide +kernel

/-! ### Blocks of fixed length -/

section Blocks
variable {α β : Type}

theorem getD_flatMap_block (c : α → List β) (k : ℕ) (hk : 0 < k) (hlen : ∀ a, (c a).length = k)
    (bk : α) (d : β) (hbk : ∀ i, (c bk).getD i d = d) :
    ∀ (L : List α) (n : ℕ), (L.flatMap c).getD n d = (c (L.getD (n / k) bk)).getD (n % k) d
  | [], n => (hbk (n % k)).symm
  | a :: L, n => by
    rw [List.flatMap_cons]
    by_cases h : n < k
    · rw [List.getD_append _ _ _ _ (by rw [hlen]; exact h), Nat.div_eq_of_lt h, Nat.mod_eq_of_lt h]
      rfl
    · have h1 : n / k = (n - k) / k + 1 := by
        rw [← Nat.sub_add_cancel (Nat.le_of_not_lt h), Nat.add_div_right _ hk, Nat.add_sub_cancel]
      have h2 : n % k = (n - k) % k := by
        rw [← Nat.sub_add_cancel (Nat.le_of_not_lt h), Nat.add_mod_right, Nat.add_sub_cancel]
      rw [List.getD_append_right _ _ _ _ (by rw [hlen]; omega), hlen,
        getD_flatMap_block c k hk hlen bk d hbk L (n - k), h1, h2]
      rfl

theorem take_flatMap_block (c : α → List β) (k : ℕ) (hlen : ∀ a, (c a).length = k) :
    ∀ (L : List α) (p : ℕ), (L.flatMap c).take (k * p) = (L.take p).flatMap c
  | _, 0 => by simp
  | [], p + 1 => by simp
  | a :: L, p + 1 => by
    rw [List.flatMap_cons, List.take_succ_cons, List.flatMap_cons,
      show k * (p + 1) = (c a).length + k * p by rw [hlen, Nat.mul_succ, Nat.add_comm],
      List.take_length_add_append, take_flatMap_block c k hlen L p]

theorem drop_flatMap_block (c : α → List β) (k : ℕ) (hlen : ∀ a, (c a).length = k) :
    ∀ (L : List α) (p : ℕ), (L.flatMap c).drop (k * p) = (L.drop p).flatMap c
  | _, 0 => by simp
  | [], p + 1 => by simp
  | a :: L, p + 1 => by
    rw [List.flatMap_cons, List.drop_succ_cons,
      show k * (p + 1) = (c a).length + k * p by rw [hlen, Nat.mul_succ, Nat.add_comm],
      List.drop_length_add_append, drop_flatMap_block c k hlen L p]

end Blocks

/-- **The block encoding of a list tape is a list tape.** -/
theorem bits_tp {S : Type} (c : S → List Bool) (k : ℕ) (hk : 0 < k)
    (hlen : ∀ s, (c s).length = k) (bk : S) (hbk : ∀ i, (c bk).getD i false = false)
    (L : List S) : bits c k (Sim.tp bk L) = Sim.tp false (L.flatMap c) := by
  funext i
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  cases i with
  | ofNat n =>
    have h1 : (Int.ofNat n) / ((k' + 1 : ℕ) : ℤ) = ((n / (k' + 1) : ℕ) : ℤ) := rfl
    have h2 : ((Int.ofNat n) % ((k' + 1 : ℕ) : ℤ)).toNat = n % (k' + 1) := rfl
    simp only [bits, h1, h2, Sim.tp_ofNat]
    exact (getD_flatMap_block c (k' + 1) hk hlen bk false hbk L n).symm
  | negSucc m =>
    have h1 : (Int.negSucc m) / ((k' + 1 : ℕ) : ℤ) = Int.negSucc (m / (k' + 1)) := rfl
    simp only [bits, h1]
    exact hbk _

/-! ### The list-level encoder -/

/-- The code of a (13,7) symbol number, as numbers. -/
def cfwd (a : ℕ) : List ℕ :=
  [[0, 0, 0], [1, 0, 0], [1, 0, 1], [0, 0, 1], [0, 1, 0], [1, 1, 0], [1, 1, 1]].getD a [0, 0, 0]

/-- The code read from right to left. -/
def crev (a : ℕ) : List ℕ := (cfwd a).reverse

/-- The bits of a (13,7) code, with state `q`: every cell becomes its 3 bits. -/
def encBits (q : ℕ) (z : Spec.Code) : Spec.Code := (q, z.2.1.flatMap crev, z.2.2.flatMap cfwd)

/-- **Encoder** (list level): the bits of Morita's (13,7) initial ID, in state `ρ begin + 2 = 4`. -/
def encList (C : CTSH) (w : List Ch) : Spec.Code :=
  encBits 4 (encM (U13_7.num.st (.go .q0)) (U13_7.num.sym .s6) (U13_7.num.sym .s5) C w)

theorem cfwd_length (a : ℕ) : (cfwd a).length = 3 := by
  unfold cfwd
  rcases a with _ | _ | _ | _ | _ | _ | _ | a <;> simp [List.getD]

theorem cfwd_mem (a b : ℕ) (h : b ∈ cfwd a) : b = 0 ∨ b = 1 := by
  unfold cfwd at h
  rcases a with _ | _ | _ | _ | _ | _ | _ | a <;> simp [List.getD] at h <;> omega

theorem code_map (s : Sy) : (code s).map syN = cfwd (U13_7.num.sym s) := by cases s <;> rfl

theorem flatMap_code (L : List Sy) :
    (L.flatMap code).map num.sym = (L.map U13_7.num.sym).flatMap cfwd := by
  rw [List.map_flatMap, List.flatMap_map]
  exact List.flatMap_congr fun s _ => code_map s

theorem reverse_flatMap_cfwd (Z : List ℕ) : (Z.flatMap cfwd).reverse = Z.reverse.flatMap crev := by
  rw [List.reverse_flatMap]; rfl

/-- The bits of a window are the window of the bits. -/
theorem encBits_window (q s : ℕ) (Y : List ℕ) (p : ℕ) :
    encBits q (window s Y p) = window q (Y.flatMap cfwd) (3 * p) := by
  simp only [encBits, window, take_flatMap_block cfwd 3 cfwd_length,
    drop_flatMap_block cfwd 3 cfwd_length, reverse_flatMap_cfwd]

/-- The (13,7) encoder as a window of the numbered initial tape. -/
theorem encM_window {Q P S : Type} (N : Numbering Q P S) (lo : Ch → S) (st bk : S)
    (hbk : N.sym bk = 0) (hlo : ∀ c, N.sym (lo c) = loN c) (q : Q) (x : S) (C : CTSH)
    (w : List Ch) :
    encM (N.st (.go q)) (N.sym x) (N.sym st) C w =
      window (N.st (.go q)) ((bk :: Sim.RA lo st bk C 0 ++ x :: w.map lo).map N.sym)
        ((Sim.RA lo st bk C 0).length + 2) := by
  have hL : bk :: Sim.RA lo st bk C 0 ++ x :: w.map lo =
      (bk :: Sim.RA lo st bk C 0 ++ [x]) ++ w.map lo := by simp
  have hp : (Sim.RA lo st bk C 0).length + 2 =
      ((bk :: Sim.RA lo st bk C 0 ++ [x]).map N.sym).length := by simp
  simp only [window]
  rw [hL, List.map_append, List.take_left' hp.symm, List.drop_left' hp.symm]
  simp only [encM, Sim.RA_zero, List.map_append, List.map_cons, List.map_nil,
    List.reverse_append, List.reverse_cons, List.reverse_nil, Hi_zero_rev N lo st hlo,
    map_lo N lo hlo, hbk]
  simp

theorem hlo : ∀ c, U13_7.num.sym (lo13 c) = loN c := by intro c; cases c <;> decide

/-- The initial list tape of (13,7). -/
def L0 (C : CTSH) (w : List Ch) : List Sy :=
  Sy.s0 :: Sim.RA lo13 .s5 .s0 C 0 ++ Sy.s6 :: w.map lo13

/-- The head position of the (13,7) initial configuration. -/
def P0 (C : CTSH) : ℕ := (Sim.RA lo13 .s5 .s0 C 0).length + 2

theorem henc13 (C : CTSH) (w : List Ch) :
    encC13 C w = ⟨.go .q0, ((P0 C : ℕ) : ℤ), Sim.tp .s0 (L0 C w)⟩ := by
  simp [encC13, URTM.CTSH.U13_7.encC, URTM.CTSH.U13_7.rep, URTM.CTSH.U13_7.tapeList, nm13,
    lo13, L0, P0]

theorem hE : (0 : ℕ) < E.k ∧ (∀ s, (E.code s).length = E.k) ∧
    ∀ i, (E.code Sy.s0).getD i false = false := by
  refine ⟨by decide, fun s => by cases s <;> rfl, fun i => ?_⟩
  rcases i with _ | _ | _ | i <;> rfl

/-- The encoded initial configuration, on a list tape of bits. -/
theorem E85_enc (C : CTSH) (w : List Ch) :
    E85 (encC13 C w) = ⟨.go 2, ((3 * P0 C : ℕ) : ℤ), Sim.tp false ((L0 C w).flatMap code)⟩ := by
  rw [henc13]
  simp only [E85, enc]
  rw [bits_tp E.code E.k hE.1 hE.2.1 Sy.s0 hE.2.2]
  simp [E, URTM.Gen.FS85_2.ρ, URTM.Gen.FS85_2.ce]

/-- The encoder is the numbered, shifted encoded initial configuration. -/
theorem encList_eq (C : CTSH) (w : List Ch) :
    Spec.toID 0 (encList C w) = numCfg num ((3 * P0 C : ℕ) : ℤ) (E85 (encC13 C w)) := by
  have hp : 3 * P0 C ≤ ((L0 C w).flatMap code).length := by
    have : ((L0 C w).flatMap code).length = 3 * (L0 C w).length := by
      induction (L0 C w) with
      | nil => rfl
      | cons s L ih =>
        rw [List.flatMap_cons, List.length_append, ih, List.length_cons]
        have := hE.2.1 s
        simp only [E] at this
        omega
    rw [this]
    simp [L0, P0]
  rw [E85_enc, numCfg_tp (N := num) false rfl _ _ _ _ hp, sub_self, flatMap_code]
  congr 1
  rw [encList, encM_window U13_7.num lo13 .s5 .s0 (by decide) hlo .q0 .s6 C w, encBits_window]
  rfl

/-- The encoded initial ID is an ID of U (`c(n, α) ∈ ID(U)` of Morita Def. 7.1). -/
theorem isIDOf_encList (C : CTSH) (w : List Ch) : Spec.IsIDOf U (Spec.toID 0 (encList C w)) := by
  have h0 : (4 : ℕ) ∈ Spec.states U := by decide +kernel
  have h1 : (1 : ℕ) ∈ Spec.symbols U := by decide +kernel
  refine isIDOf_toID U 0 _ h0 fun a ha => ?_
  simp only [encList, encBits, List.mem_append, List.mem_flatMap, crev, List.mem_reverse] at ha
  rcases ha with ⟨b, -, hb⟩ | ⟨b, -, hb⟩ <;> rcases cfwd_mem b a hb with rfl | rfl <;>
    first | exact .inl rfl | exact .inr h1

open Primrec in
theorem cfwd_primrec : Primrec cfwd :=
  (list_getD [0, 0, 0]).comp (const _) .id

open Primrec in
theorem encBits_primrec (q : ℕ) : Primrec (encBits q) :=
  pair (const q) (pair
    (list_flatMap (fst.comp snd) ((list_reverse.comp cfwd_primrec).comp snd).to₂)
    (list_flatMap (snd.comp snd) (cfwd_primrec.comp snd).to₂))

theorem encList_primrec : Primrec₂ encList :=
  (encBits_primrec 4).comp₂ (encM_primrec _ _ _)

/-! ### The readout -/

/-- Decode a list of bits in blocks of 3 by `d` (missing bits are blanks). -/
def decB (d : ℕ → ℕ → ℕ → ℕ) : List ℕ → List ℕ
  | [] => []
  | [a] => [d a 0 0]
  | [a, b] => [d a b 0]
  | a :: b :: c :: t => d a b c :: decB d t

/-- The symbol number of (13,7) with the code number `i = 4·b₀ + 2·b₁ + b₂`. -/
def tab (i : ℕ) : ℕ := [0, 3, 4, 0, 1, 2, 5, 6].getD i 0

/-- Decoder of a block read from left to right. -/
def dR (a b c : ℕ) : ℕ := tab (4 * a + 2 * b + c)

/-- Decoder of a block read from right to left. -/
def dL (a b c : ℕ) : ℕ := tab (4 * c + 2 * b + a)

/-- The symbols of (13,7) on the window `(l, r)` of bits (left end first). -/
def symsOf (l r : List ℕ) : List ℕ := (decB dL l).reverse ++ decB dR r

/-- **Readout** (list level) from a code `g` of the halting ID: `(|C|, ϕ₁(vf))`. -/
def readU (g : Spec.Code) : Option (ℕ × List ℕ) :=
  some (readL 9 5 0 g.1 (symsOf g.2.1 g.2.2))

theorem decB_cfwd (a : ℕ) (ha : a < 7) (t : List ℕ) : decB dR (cfwd a ++ t) = a :: decB dR t := by
  match a, ha with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | 6, _ => rfl

theorem decB_crev (a : ℕ) (ha : a < 7) (t : List ℕ) : decB dL (crev a ++ t) = a :: decB dL t := by
  match a, ha with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | 6, _ => rfl

theorem decB_flatMap_cfwd (Z : List ℕ) (hZ : ∀ a ∈ Z, a < 7) : decB dR (Z.flatMap cfwd) = Z := by
  induction Z with
  | nil => rfl
  | cons a Z ih =>
    rw [List.flatMap_cons, decB_cfwd a (hZ a (by simp)), ih fun b hb => hZ b (by simp [hb])]

theorem decB_flatMap_crev (Z : List ℕ) (hZ : ∀ a ∈ Z, a < 7) : decB dL (Z.flatMap crev) = Z := by
  induction Z with
  | nil => rfl
  | cons a Z ih =>
    rw [List.flatMap_cons, decB_crev a (hZ a (by simp)), ih fun b hb => hZ b (by simp [hb])]

/-- **The symbols of a window of bits**: decoding the bits of a (13,7) list gives the list. -/
theorem symsOf_window (q : ℕ) (Y : List ℕ) (hY : ∀ a ∈ Y, a < 7) (p : ℕ) :
    symsOf (window q (Y.flatMap cfwd) (3 * p)).2.1 (window q (Y.flatMap cfwd) (3 * p)).2.2 = Y := by
  simp only [symsOf, window, take_flatMap_block cfwd 3 cfwd_length,
    drop_flatMap_block cfwd 3 cfwd_length, reverse_flatMap_cfwd]
  rw [decB_flatMap_crev _ fun a ha => hY a (List.mem_of_mem_take (List.mem_reverse.mp ha)),
    decB_flatMap_cfwd _ fun a ha => hY a (List.mem_of_mem_drop ha), List.reverse_reverse,
    List.take_append_drop]

/-! #### Trailing blanks -/

theorem decB_zeros (d : ℕ → ℕ → ℕ → ℕ) (hd : d 0 0 0 = 0) :
    ∀ j, ∃ j', decB d (List.replicate j 0) = List.replicate j' 0
  | 0 => ⟨0, rfl⟩
  | 1 => ⟨1, by simp [decB, hd]⟩
  | 2 => ⟨1, by simp [decB, List.replicate_succ, hd]⟩
  | j + 3 => by
    obtain ⟨j', h⟩ := decB_zeros d hd j
    exact ⟨j' + 1, by simp [List.replicate_succ, decB, h, hd]⟩

theorem decB_pad (d : ℕ → ℕ → ℕ → ℕ) (hd : d 0 0 0 = 0) :
    ∀ (l : List ℕ) (j : ℕ), ∃ j', decB d (l ++ List.replicate j 0) = decB d l ++ List.replicate j' 0
  | [], j => by simpa [decB] using decB_zeros d hd j
  | [a], j => by
    match j with
    | 0 => exact ⟨0, by simp⟩
    | 1 => exact ⟨0, by simp [decB]⟩
    | j + 2 =>
      obtain ⟨j', h⟩ := decB_zeros d hd j
      exact ⟨j', by simp [List.replicate_succ, decB, h]⟩
  | [a, b], j => by
    match j with
    | 0 => exact ⟨0, by simp⟩
    | j + 1 =>
      obtain ⟨j', h⟩ := decB_zeros d hd j
      exact ⟨j', by simp [List.replicate_succ, decB, h]⟩
  | a :: b :: c :: t, j => by
    obtain ⟨j', h⟩ := decB_pad d hd t j
    exact ⟨j', by simp [decB, h]⟩

/-- **The readout depends only on the ID**, not on the code chosen for it. -/
theorem readU_toID {p : ℤ} {g g' : Spec.Code} (h : Spec.toID p g = Spec.toID p g') :
    readU g = readU g' := by
  refine congrArg some (ReadGen.read_toID2 (fun s l r => readL 9 5 0 s (symsOf l r)) ?_ ?_ h)
  · intro s k l r
    obtain ⟨j, hj⟩ := decB_pad dL rfl l k
    simp only [symsOf, hj, List.reverse_append, List.reverse_replicate, List.append_assoc]
    simp only [readL, count_padL (by decide : (5 : ℕ) ≠ 0), lowSuffix_padL]
  · intro s k l r
    obtain ⟨j, hj⟩ := decB_pad dR rfl r k
    simp only [symsOf, hj, ← List.append_assoc]
    simp only [readL, count_padR (by decide : (5 : ℕ) ≠ 0), lowSuffix_padR]

/-! #### Computability of the readout -/

theorem unf_nil {γ : Type} (out : List ℕ → γ) (nxt : List ℕ → List ℕ) (f : ℕ) :
    ComputableDec.unf (fun l : List ℕ => l.isEmpty) out nxt f [] = [] := by
  cases f <;> rfl

/-- `decB` as a fuel-bounded unfolding (`ComputableDec.unf`). -/
theorem decB_eq_unf (d : ℕ → ℕ → ℕ → ℕ) : ∀ (l : List ℕ) (f : ℕ), l.length ≤ f →
    decB d l = ComputableDec.unf (fun l : List ℕ => l.isEmpty)
      (fun l => d (l.getD 0 0) (l.getD 1 0) (l.getD 2 0)) (fun l => l.drop 3) f l
  | [], f, _ => (unf_nil _ _ f).symm
  | [a], f + 1, _ => by
    show [d a 0 0] = d a 0 0 :: ComputableDec.unf _ _ _ f []
    rw [unf_nil]
  | [a, b], f + 1, _ => by
    show [d a b 0] = d a b 0 :: ComputableDec.unf _ _ _ f []
    rw [unf_nil]
  | a :: b :: c :: t, f + 1, h => by
    have ih := decB_eq_unf d t f (by simp only [List.length_cons] at h; omega)
    show d a b c :: decB d t = d a b c :: ComputableDec.unf _ _ _ f t
    rw [ih]

open Primrec in
theorem tab_primrec : Primrec tab := (list_getD 0).comp (const _) .id

open Primrec in
theorem decB_primrec (d : ℕ → ℕ → ℕ → ℕ)
    (hd : Primrec fun l : List ℕ => d (l.getD 0 0) (l.getD 1 0) (l.getD 2 0)) :
    Primrec (decB d) :=
  (ComputableDec.unf_primrec (α := List ℕ) (ComputableDec.list_isEmpty.comp snd).to₂
    (hd.comp snd).to₂ (list_drop.comp (const 3) snd).to₂ list_length .id).of_eq fun l =>
      (decB_eq_unf d l l.length (Nat.le_refl _)).symm

open Primrec in
theorem readU_primrec : Primrec readU := by
  have g0 : Primrec fun l : List ℕ => l.getD 0 0 := (list_getD 0).comp .id (const 0)
  have g1 : Primrec fun l : List ℕ => l.getD 1 0 := (list_getD 0).comp .id (const 1)
  have g2 : Primrec fun l : List ℕ => l.getD 2 0 := (list_getD 0).comp .id (const 2)
  have hR : Primrec (decB dR) := decB_primrec dR (tab_primrec.comp (nat_add.comp
    (nat_add.comp (nat_mul.comp (const 4) g0) (nat_mul.comp (const 2) g1)) g2))
  have hL : Primrec (decB dL) := decB_primrec dL (tab_primrec.comp (nat_add.comp
    (nat_add.comp (nat_mul.comp (const 4) g2) (nat_mul.comp (const 2) g1)) g0))
  have hs : Primrec fun g : Spec.Code => symsOf g.2.1 g.2.2 :=
    list_append.comp (list_reverse.comp (hL.comp (fst.comp snd))) (hR.comp (snd.comp snd))
  have hc : Primrec fun g : Spec.Code => (symsOf g.2.1 g.2.2).count 5 :=
    ComputableDec.list_count (const 5) hs
  exact (option_some.comp (Primrec.ite (Primrec.eq.comp fst (const 9))
    (pair (nat_sub.comp hc (const 0)) (list_cons.comp (const 1) (lowSuffix_primrec.comp hs)))
    (pair hc (const [])))).of_eq fun g => by simp only [readU, readL]

/-! ### The final configurations -/

/-- Where (13,7) would apply a halting quintuple, `M` halts at once inside the block. -/
theorem hrun_q (h : Ps) :
    hrun M (hfuel E) ⟨E.ρ (f13 h), E.ce (f13 h), E.code Sy.s0⟩ =
      some ⟨E.ρ (f13 h), 0, E.code Sy.s0⟩ := by
  cases h <;> decide +kernel

/-- The state numbers of the two final states: `null ↦ ρ begin + 2 = 4`, `halt ↦ ρ case_y_1 + 2 = 9`. -/
def stn (h : Ps) : ℕ := stN (.go (E.ρ (f13 h)))

/-- **The final configuration of (85,2)** for a (13,7) final configuration on a list tape whose
    head cell is blank: the 3-bit encoding, in the state `ρ (f13 h)`. -/
theorem fin85_of (h : Ps) (p : ℕ) (L : List Sy) (hb : Sim.tp Sy.s0 L (p : ℤ) = Sy.s0) :
    pre M E (SimLemmas.unhalt f13 ⟨.halt h, (p : ℤ), Sim.tp Sy.s0 L⟩) =
      ⟨.go (E.ρ (f13 h)), ((3 * p : ℕ) : ℤ), Sim.tp false (L.flatMap code)⟩ := by
  have hu : SimLemmas.unhalt f13 (⟨.halt h, (p : ℤ), Sim.tp Sy.s0 L⟩ : Cfg St Ps Sy) =
      ⟨.go (f13 h), (p : ℤ), Sim.tp Sy.s0 L⟩ := rfl
  have hu2 := Conv55.upd_self (Sim.tp Sy.s0 L) (p : ℤ)
  rw [hb] at hu2
  rw [hu]
  simp only [pre, hb, hrun_q h, glob]
  rw [ovl_block hE.1 hE.2.1, hu2, bits_tp E.code E.k hE.1 hE.2.1 Sy.s0 hE.2.2]
  simp [E]

/-- The cell under the head of a final configuration of (13,7) is blank. -/
theorem head13 (C : CTSH) (vf : List Ch) (mf : ℕ) (rm : List Ch) (hf : Halting C (vf, mf)) :
    (finCfg13 C vf mf rm).tape (finCfg13 C vf mf rm).pos = Sy.s0 := by
  cases vf with
  | nil =>
    have e : finCfg13 C [] mf rm = ⟨.halt .h0,
        (((URTM.CTSH.U13_7.finList nm13 C [] mf rm).length : ℕ) : ℤ),
        Sim.tp .s0 (URTM.CTSH.U13_7.finList nm13 C [] mf rm)⟩ := by
      simp [finCfg13, URTM.CTSH.U13_7.finCfg, URTM.CTSH.U13_7.finList,
        URTM.CTSH.U13_7.tapeList, nm13]
      omega
    rw [e]
    simp only [Sim.tp_ofNat]
    rw [List.getD_eq_default _ _ (Nat.le_refl _)]
  | cons c v =>
    have hm : mf = 0 := by
      rcases hf.2 with ⟨v', -, h2⟩ | h
      · exact h2
      · simp at h
    subst hm
    have e : finCfg13 C (c :: v) 0 rm = ⟨.halt .h1,
        (((Sy.s0 :: Sim.Hi lo13 .s5 C 0).length : ℕ) : ℤ),
        Sim.tp .s0 ((Sy.s0 :: Sim.Hi lo13 .s5 C 0) ++ Sy.s0 ::
          (Sy.s6 :: rm.map lo13 ++ Sy.s3 :: v.map lo13))⟩ := by
      simp [finCfg13, URTM.CTSH.U13_7.finCfg, URTM.CTSH.U13_7.finList, nm13, lo13,
        Sim.RA_zero]
    rw [e]
    exact Sim.tp_at _ _ _

/-- The final configuration of (13,7) for `(λ, m)` (as in `U13_7.isUTMStrict_U`). -/
theorem hnullfin13 (C : CTSH) (mf : ℕ) (rm : List Ch) (hm : mf ≤ C.length) :
    ∃ (L : List Sy) (p : ℕ), p ≤ L.length ∧
      finCfg13 C [] mf rm = ⟨.halt .h0, p, Sim.tp .s0 L⟩ ∧ L.count .s5 = C.length := by
  refine ⟨URTM.CTSH.U13_7.finList nm13 C [] mf rm,
    (URTM.CTSH.U13_7.RA nm13 C mf).length + 2 + rm.length, ?_, ?_, ?_⟩
  · simp [URTM.CTSH.U13_7.finList, URTM.CTSH.U13_7.tapeList]; omega
  · simp [finCfg13, URTM.CTSH.U13_7.finCfg, nm13]
  · have h := count_RA lo13 Sy.s5 Sy.s0 hls (by decide) C hm
    simp only [URTM.CTSH.U13_7.finList, URTM.CTSH.U13_7.tapeList, List.map_nil,
      List.append_nil, List.count_cons, List.count_append]
    rw [show (URTM.CTSH.U13_7.RA nm13 C mf).count Sy.s5 = C.length from h,
      show (rm.map (URTM.CTSH.U13_7.lo nm13)).count Sy.s5 = 0 from count_lo lo13 _ hls rm]
    simp [nm13]

/-- The final configuration of (13,7) for `(Y v, 0)` (as in `U13_7.isUTMStrict_U`). -/
theorem hhaltfin13 (C : CTSH) (v rm : List Ch) :
    ∃ (A : List Sy) (mk : Sy) (p : ℕ), p ≤ (A ++ mk :: v.map lo13).length ∧
      finCfg13 C (.Y :: v) 0 rm = ⟨.halt .h1, p, Sim.tp .s0 (A ++ mk :: v.map lo13)⟩ ∧
      (A ++ [mk]).count .s5 - 0 = C.length ∧ U13_7.num.sym mk ≠ 0 ∧ U13_7.num.sym mk ≠ 1 ∧
      U13_7.num.sym mk ≠ 2 := by
  refine ⟨Sy.s0 :: URTM.CTSH.U13_7.RA nm13 C 0 ++ Sy.s6 :: rm.map lo13, Sy.s3,
    (URTM.CTSH.U13_7.RA nm13 C 0).length, ?_, ?_, ?_, by decide, by decide, by decide⟩
  · simp; omega
  · simp [finCfg13, URTM.CTSH.U13_7.finCfg, URTM.CTSH.U13_7.finList, nm13, lo13]
  · have h := count_RA lo13 Sy.s5 Sy.s0 hls (by decide) C (Nat.zero_le _)
    simp only [List.count_cons, List.count_append, List.count_nil]
    rw [show (URTM.CTSH.U13_7.RA nm13 C 0).count Sy.s5 = C.length from h,
      show (rm.map lo13).count Sy.s5 = 0 from count_lo lo13 _ hls rm]
    simp

theorem length_flatMap_code (L : List Sy) : (L.flatMap code).length = 3 * L.length := by
  induction L with
  | nil => rfl
  | cons s L ih =>
    rw [List.flatMap_cons, List.length_append, ih, List.length_cons]
    have := hE.2.1 s
    simp only [E] at this
    omega

theorem sym13_lt (s : Sy) : U13_7.num.sym s < 7 := by cases s <;> decide

/-! ### The run-level simulation and the main theorem -/

/-- **URTM(85,2) simulates every CTSH at the level of Spec** (run level, exact readback). -/
theorem runSim_U (C : CTSH) (w : List Ch) :
    RunSim (CStep C) (Halting C) (Spec.Step U) (Spec.Halted U)
      (fun y γ => ∃ g, Spec.toID γ.pos g = γ ∧ readU g = some (C.length, y.1.map loN))
      (w, 0) (Spec.toID 0 (encList C w)) := by
  rw [encList_eq]
  obtain ⟨-, -, -, -, -, -, hF, -, hN⟩ := urtm85_2_simulates_ctsh C w
  refine runSim_of_sim num M _ C w (E85 (encC13 C w)) (fun f c => ∃ rm, c = fin85 C f.1 f.2 rm) _
    (fun n f hf => ?_) (fun hn => hN.mp hn) (fun f c hf hc => ?_)
  · obtain ⟨N, rm, -, h⟩ := hF n f.1 f.2 hf
    exact ⟨N, _, h, rm, rfl⟩
  · obtain ⟨rm, rfl⟩ := hc
    obtain ⟨vf, mf⟩ := f
    obtain ⟨h, L, p, hp, hfin, hrd⟩ := BlockGen.readM_fin U13_7.num lo13 .s5 .s0 .h0 .h1 0 hlo
      hls stn (by decide) finCfg13 hnullfin13 hhaltfin13 C vf mf rm hf
    have hb : Sim.tp Sy.s0 L (p : ℤ) = Sy.s0 := by
      have := head13 C vf mf rm hf
      rw [hfin] at this
      exact this
    have e : fin85 C vf mf rm = ⟨.go (E.ρ (f13 h)), ((3 * p : ℕ) : ℤ),
        Sim.tp false (L.flatMap code)⟩ := by
      rw [fin85, hfin]
      exact fin85_of h p L hb
    simp only [e]
    refine read_of_tp num false rfl _ _ _ _ (by rw [length_flatMap_code]; omega) _ _ ?_
    rw [flatMap_code]
    simp only [readU, window_st]
    rw [symsOf_window _ _ (fun a ha => by
      obtain ⟨s, -, rfl⟩ := List.mem_map.mp ha
      exact sym13_lt s) p]
    simp only [readM, window_whole, window_st] at hrd
    exact hrd

/-- **URTM(85,2) is a UTM in the strict sense of Morita Def. 7.1.** -/
theorem isUTMStrict_U : Spec.IsUTMStrict U :=
  ChainGen.isUTMStrict_of_ctsh U encList readU encList_primrec readU_primrec isIDOf_encList
    runSim_U (fun _ _ _ h => readU_toID h)

end URTM.Univ.U85_2
