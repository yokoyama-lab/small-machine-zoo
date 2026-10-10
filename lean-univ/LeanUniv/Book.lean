/-
  **The tables without the halting quintuples are UTMs in the sense of Morita Def. 7.1**
  (docs/26).

  The witnesses of `FinalMorita`, `Final10_8` and `FinalBlocks` are the tables of Morita's
  description files (or their block conversions): the book's table plus two 0-shift quintuples
  into the pseudo-states `halt`/`null` (`U<m>_<n>.U_halting`). Here those two quintuples `H` are
  removed (`DropGen.dropT U H`), which gives the table as printed in the book, where the two
  entries read `(halt)` and `(null)` and are not quintuples. For the six block conversions the
  "book table" is the analogue (the block machines are not in the book): the block conversion
  without the images of the two halting quintuples.

  For each machine `B<m>_<n>`:
  * `B<m>_<n>_book`: `H` is exactly the list of quintuples of the description-file table that
    enter a state without outgoing quintuples, the number of quintuples drops by 2, and **every
    quintuple of `B<m>_<n>` enters a state with outgoing quintuples** (no pseudo-state is left);
  * `B<m>_<n>_counts`: the state and symbol counts are those of the description-file table;
  * `isUTMStrict_B<m>_<n>`: `IsUTMStrict`, by `DropGen.isUTMStrict_drop` (same encoder; the
    decoder first puts the halting ID back into the pseudo-state).

  The final statements are in `FinalBook.lean`.
-/
import LeanUniv.FinalMorita
import LeanUniv.FinalBlocks
import LeanUniv.Final10_8
import LeanUniv.DropGen

namespace URTM.Univ.Book
open URTM URTM.Spec URTM.Univ.DropGen

/-! ### The one-cell-per-letter family: (13,7), (15,6), (17,5), (24,4) -/

section Morita
open URTM.Univ.MoritaGen

/-- The two halting quintuples of the description file of (13,7). -/
def H13_7 : List Quint := [⟨0, 0, 0, .Z, 13⟩, ⟨1, 0, 0, .Z, 14⟩]
/-- **URTM(13,7) as in the book** (57 quintuples). -/
def B13_7 : List Quint := dropT U13_7.U H13_7

theorem B13_7_book :
    H13_7 = U13_7.U.filter (fun r => decide (r.q ∉ U13_7.U.map Quint.p)) ∧
    B13_7.length = 57 ∧ ∀ r ∈ B13_7, r.q ∈ B13_7.map Quint.p := by decide +kernel
theorem B13_7_counts : NStates B13_7 = 13 ∧ NSyms B13_7 = 7 := by decide +kernel
theorem B13_7_det : Deterministic B13_7 := deterministic_dropT _ U13_7.U_det
theorem B13_7_rev : Reversible B13_7 := reversible_dropT _ U13_7.U_rev
theorem isUTMStrict_B13_7 : IsUTMStrict B13_7 :=
  ChainGen.isUTMStrict_drop_ctsh (encM_primrec _ _ _) (readM_primrec _ _ _) U13_7.body_U
    U13_7.U_det (by decide +kernel) _ (fun _ _ => rfl) (by decide +kernel) (by decide +kernel)

/-- The two halting quintuples of the description file of (15,6). -/
def H15_6 : List Quint := [⟨1, 0, 0, .Z, 15⟩, ⟨2, 4, 4, .Z, 16⟩]
/-- **URTM(15,6) as in the book** (62 quintuples). -/
def B15_6 : List Quint := dropT U15_6.U H15_6

theorem B15_6_book :
    H15_6 = U15_6.U.filter (fun r => decide (r.q ∉ U15_6.U.map Quint.p)) ∧
    B15_6.length = 62 ∧ ∀ r ∈ B15_6, r.q ∈ B15_6.map Quint.p := by decide +kernel
theorem B15_6_counts : NStates B15_6 = 15 ∧ NSyms B15_6 = 6 := by decide +kernel
theorem B15_6_det : Deterministic B15_6 := deterministic_dropT _ U15_6.U_det
theorem B15_6_rev : Reversible B15_6 := reversible_dropT _ U15_6.U_rev
theorem isUTMStrict_B15_6 : IsUTMStrict B15_6 :=
  ChainGen.isUTMStrict_drop_ctsh (encM_primrec _ _ _) (readM_primrec _ _ _) U15_6.body_U
    U15_6.U_det (by decide +kernel) _ (fun _ _ => rfl) (by decide +kernel) (by decide +kernel)

/-- The two halting quintuples of the description file of (17,5). -/
def H17_5 : List Quint := [⟨1, 0, 0, .Z, 17⟩, ⟨2, 4, 4, .Z, 18⟩]
/-- **URTM(17,5) as in the book** (67 quintuples). -/
def B17_5 : List Quint := dropT U17_5.U H17_5

theorem B17_5_book :
    H17_5 = U17_5.U.filter (fun r => decide (r.q ∉ U17_5.U.map Quint.p)) ∧
    B17_5.length = 67 ∧ ∀ r ∈ B17_5, r.q ∈ B17_5.map Quint.p := by decide +kernel
theorem B17_5_counts : NStates B17_5 = 17 ∧ NSyms B17_5 = 5 := by decide +kernel
theorem B17_5_det : Deterministic B17_5 := deterministic_dropT _ U17_5.U_det
theorem B17_5_rev : Reversible B17_5 := reversible_dropT _ U17_5.U_rev
theorem isUTMStrict_B17_5 : IsUTMStrict B17_5 :=
  ChainGen.isUTMStrict_drop_ctsh (encM_primrec _ _ _) (readM_primrec _ _ _) U17_5.body_U
    U17_5.U_det (by decide +kernel) _ (fun _ _ => rfl) (by decide +kernel) (by decide +kernel)

/-- The two halting quintuples of the description file of (24,4). -/
def H24_4 : List Quint := [⟨0, 0, 0, .Z, 24⟩, ⟨2, 0, 0, .Z, 25⟩]
/-- **URTM(24,4) as in the book** (82 quintuples). -/
def B24_4 : List Quint := dropT U24_4.U H24_4

theorem B24_4_book :
    H24_4 = U24_4.U.filter (fun r => decide (r.q ∉ U24_4.U.map Quint.p)) ∧
    B24_4.length = 82 ∧ ∀ r ∈ B24_4, r.q ∈ B24_4.map Quint.p := by decide +kernel
theorem B24_4_counts : NStates B24_4 = 24 ∧ NSyms B24_4 = 4 := by decide +kernel
theorem B24_4_det : Deterministic B24_4 := deterministic_dropT _ U24_4.U_det
theorem B24_4_rev : Reversible B24_4 := reversible_dropT _ U24_4.U_rev
theorem isUTMStrict_B24_4 : IsUTMStrict B24_4 :=
  ChainGen.isUTMStrict_drop_ctsh (encM_primrec _ _ _) (readM_primrec _ _ _) U24_4.body_U
    U24_4.U_det (by decide +kernel) _ (fun _ _ => rfl) (by decide +kernel) (by decide +kernel)

end Morita

/-! ### (32,3) -/

/-- The two halting quintuples of the description file of (32,3). -/
def H32_3 : List Quint := [⟨0, 0, 0, .Z, 32⟩, ⟨2, 0, 0, .Z, 33⟩]
/-- **URTM(32,3) as in the book** (82 quintuples). -/
def B32_3 : List Quint := dropT U32_3.U H32_3

theorem B32_3_book :
    H32_3 = U32_3.U.filter (fun r => decide (r.q ∉ U32_3.U.map Quint.p)) ∧
    B32_3.length = 82 ∧ ∀ r ∈ B32_3, r.q ∈ B32_3.map Quint.p := by decide +kernel
theorem B32_3_counts : NStates B32_3 = 32 ∧ NSyms B32_3 = 3 := by decide +kernel
theorem B32_3_det : Deterministic B32_3 := deterministic_dropT _ U32_3.U_det
theorem B32_3_rev : Reversible B32_3 := reversible_dropT _ U32_3.U_rev
theorem isUTMStrict_B32_3 : IsUTMStrict B32_3 :=
  ChainGen.isUTMStrict_drop_ctsh U32_3.encList_primrec U32_3.readU_primrec U32_3.body_U
    U32_3.U_det (by decide +kernel) 0 (fun _ _ => rfl) (by decide +kernel) (by decide +kernel)

/-! ### (10,8) -/

/-- The two halting quintuples of the description file of (10,8). -/
def H10_8 : List Quint := [⟨0, 0, 0, .Z, 10⟩, ⟨1, 0, 0, .Z, 11⟩]
/-- **URTM(10,8) as in the book** (61 quintuples). -/
def B10_8 : List Quint := dropT U10_8.U H10_8

theorem B10_8_book :
    H10_8 = U10_8.U.filter (fun r => decide (r.q ∉ U10_8.U.map Quint.p)) ∧
    B10_8.length = 61 ∧ ∀ r ∈ B10_8, r.q ∈ B10_8.map Quint.p := by decide +kernel
theorem B10_8_counts : NStates B10_8 = 10 ∧ NSyms B10_8 = 8 := by decide +kernel
theorem B10_8_det : Deterministic B10_8 := deterministic_dropT _ U10_8.U_det
theorem B10_8_rev : Reversible B10_8 := reversible_dropT _ U10_8.U_rev
theorem isUTMStrict_B10_8 : IsUTMStrict B10_8 :=
  isUTMStrict_drop ComputableEnc.c10_8_computable ComputableDec.d10_8_computable U10_8.U_det
    (by decide +kernel) (fun _ _ _ => by show (0 : ℕ) ∈ _; decide +kernel) (by decide +kernel)
    Chain10_8.strictBody_U10_8

/-! ### The six block conversions -/

section Blocks
/-- The images of the two halting quintuples of (10,8) in (4,46). -/
def H4_46 : List Quint := [⟨2, 16, 0, .Z, 4⟩, ⟨3, 56, 0, .Z, 5⟩]
/-- **URTM(4,46) without the halting quintuples** (155 quintuples). -/
def B4_46 : List Quint := dropT U4_46.U H4_46

theorem B4_46_book :
    H4_46 = U4_46.U.filter (fun r => decide (r.q ∉ U4_46.U.map Quint.p)) ∧
    B4_46.length = 155 ∧ ∀ r ∈ B4_46, r.q ∈ B4_46.map Quint.p := by decide +kernel
theorem B4_46_counts : NStates B4_46 = 4 ∧ NSyms B4_46 = 46 := by decide +kernel
theorem B4_46_det : Deterministic B4_46 := deterministic_dropT _ U4_46.U_det
theorem B4_46_rev : Reversible B4_46 := reversible_dropT _ U4_46.U_rev
theorem isUTMStrict_B4_46 : IsUTMStrict B4_46 :=
  ChainGen.isUTMStrict_drop_ctsh
    ((BlockGen.encB_primrec _ _).comp₂ ComputableEnc.encList_primrec) Base10_8.readN_primrec
    (Base10_8.strictBody_block10 URTM.Gen.KB4_46.spB URTM.Gen.KB4_46.TpyB U4_46.hsim
      (by decide +kernel) (by decide +kernel) (by decide +kernel))
    U4_46.U_det (by decide +kernel) _ (fun _ _ => rfl) (by decide +kernel) (by decide +kernel)

/-- The images of the two halting quintuples of (15,6) in (5,45). -/
def H5_45 : List Quint := [⟨4, 42, 0, .Z, 5⟩, ⟨4, 40, 4, .Z, 6⟩]
/-- **URTM(5,45) without the halting quintuples** (162 quintuples). -/
def B5_45 : List Quint := dropT U5_45.U H5_45

theorem B5_45_book :
    H5_45 = U5_45.U.filter (fun r => decide (r.q ∉ U5_45.U.map Quint.p)) ∧
    B5_45.length = 162 ∧ ∀ r ∈ B5_45, r.q ∈ B5_45.map Quint.p := by decide +kernel
theorem B5_45_counts : NStates B5_45 = 5 ∧ NSyms B5_45 = 45 := by decide +kernel
theorem B5_45_det : Deterministic B5_45 := deterministic_dropT _ U5_45.U_det
theorem B5_45_rev : Reversible B5_45 := reversible_dropT _ U5_45.U_rev
theorem isUTMStrict_B5_45 : IsUTMStrict B5_45 :=
  ChainGen.isUTMStrict_drop_ctsh
    ((BlockGen.encB_primrec _ _).comp₂ (MoritaGen.encM_primrec _ _ _)) (MoritaGen.readM_primrec _ _ _)
    (Base15_6.strictBody_block15 URTM.Gen.KB5_45.spB URTM.Gen.KB5_45.TpyB U5_45.hsim
      (by decide +kernel) (by decide +kernel) (by decide +kernel))
    U5_45.U_det (by decide +kernel) _ (fun _ _ => rfl) (by decide +kernel) (by decide +kernel)

/-- The images of the two halting quintuples of (10,8) in (6,37). -/
def H6_37 : List Quint := [⟨4, 24, 0, .Z, 6⟩, ⟨3, 16, 0, .Z, 7⟩]
/-- **URTM(6,37) without the halting quintuples** (179 quintuples). -/
def B6_37 : List Quint := dropT U6_37.U H6_37

theorem B6_37_book :
    H6_37 = U6_37.U.filter (fun r => decide (r.q ∉ U6_37.U.map Quint.p)) ∧
    B6_37.length = 179 ∧ ∀ r ∈ B6_37, r.q ∈ B6_37.map Quint.p := by decide +kernel
theorem B6_37_counts : NStates B6_37 = 6 ∧ NSyms B6_37 = 37 := by decide +kernel
theorem B6_37_det : Deterministic B6_37 := deterministic_dropT _ U6_37.U_det
theorem B6_37_rev : Reversible B6_37 := reversible_dropT _ U6_37.U_rev
theorem isUTMStrict_B6_37 : IsUTMStrict B6_37 :=
  ChainGen.isUTMStrict_drop_ctsh
    ((BlockGen.encB_primrec _ _).comp₂ ComputableEnc.encList_primrec) Base10_8.readN_primrec
    (Base10_8.strictBody_block10 URTM.Gen.KB6_37.spB URTM.Gen.KB6_37.TpyB U6_37.hsim
      (by decide +kernel) (by decide +kernel) (by decide +kernel))
    U6_37.U_det (by decide +kernel) _ (fun _ _ => rfl) (by decide +kernel) (by decide +kernel)

/-- The images of the two halting quintuples of (15,6) in (7,32). -/
def H7_32 : List Quint := [⟨6, 18, 0, .Z, 7⟩, ⟨6, 28, 4, .Z, 8⟩]
/-- **URTM(7,32) without the halting quintuples** (166 quintuples). -/
def B7_32 : List Quint := dropT U7_32.U H7_32

theorem B7_32_book :
    H7_32 = U7_32.U.filter (fun r => decide (r.q ∉ U7_32.U.map Quint.p)) ∧
    B7_32.length = 166 ∧ ∀ r ∈ B7_32, r.q ∈ B7_32.map Quint.p := by decide +kernel
theorem B7_32_counts : NStates B7_32 = 7 ∧ NSyms B7_32 = 32 := by decide +kernel
theorem B7_32_det : Deterministic B7_32 := deterministic_dropT _ U7_32.U_det
theorem B7_32_rev : Reversible B7_32 := reversible_dropT _ U7_32.U_rev
theorem isUTMStrict_B7_32 : IsUTMStrict B7_32 :=
  ChainGen.isUTMStrict_drop_ctsh
    ((BlockGen.encB_primrec _ _).comp₂ (MoritaGen.encM_primrec _ _ _)) (MoritaGen.readM_primrec _ _ _)
    (Base15_6.strictBody_block15 URTM.Gen.KB7_32.spB URTM.Gen.KB7_32.TpyB U7_32.hsim
      (by decide +kernel) (by decide +kernel) (by decide +kernel))
    U7_32.U_det (by decide +kernel) _ (fun _ _ => rfl) (by decide +kernel) (by decide +kernel)

/-- The images of the two halting quintuples of (17,5) in (8,28). -/
def H8_28 : List Quint := [⟨7, 40, 0, .Z, 8⟩, ⟨7, 39, 4, .Z, 9⟩]
/-- **URTM(8,28) without the halting quintuples** (167 quintuples). -/
def B8_28 : List Quint := dropT U8_28.U H8_28

theorem B8_28_book :
    H8_28 = U8_28.U.filter (fun r => decide (r.q ∉ U8_28.U.map Quint.p)) ∧
    B8_28.length = 167 ∧ ∀ r ∈ B8_28, r.q ∈ B8_28.map Quint.p := by decide +kernel
theorem B8_28_counts : NStates B8_28 = 8 ∧ NSyms B8_28 = 28 := by decide +kernel
theorem B8_28_det : Deterministic B8_28 := deterministic_dropT _ U8_28.U_det
theorem B8_28_rev : Reversible B8_28 := reversible_dropT _ U8_28.U_rev
theorem isUTMStrict_B8_28 : IsUTMStrict B8_28 :=
  ChainGen.isUTMStrict_drop_ctsh
    ((BlockGen.encB_primrec _ _).comp₂ (MoritaGen.encM_primrec _ _ _)) (MoritaGen.readM_primrec _ _ _)
    (Base17_5.strictBody_block17 URTM.Gen.KB8_28.spB URTM.Gen.KB8_28.TpyB U8_28.hsim
      (by decide +kernel) (by decide +kernel) (by decide +kernel))
    U8_28.U_det (by decide +kernel) _ (fun _ _ => rfl) (by decide +kernel) (by decide +kernel)

/-- The images of the two halting quintuples of (15,6) in (9,27). -/
def H9_27 : List Quint := [⟨4, 30, 0, .Z, 9⟩, ⟨8, 22, 4, .Z, 10⟩]
/-- **URTM(9,27) without the halting quintuples** (162 quintuples). -/
def B9_27 : List Quint := dropT U9_27.U H9_27

theorem B9_27_book :
    H9_27 = U9_27.U.filter (fun r => decide (r.q ∉ U9_27.U.map Quint.p)) ∧
    B9_27.length = 162 ∧ ∀ r ∈ B9_27, r.q ∈ B9_27.map Quint.p := by decide +kernel
theorem B9_27_counts : NStates B9_27 = 9 ∧ NSyms B9_27 = 27 := by decide +kernel
theorem B9_27_det : Deterministic B9_27 := deterministic_dropT _ U9_27.U_det
theorem B9_27_rev : Reversible B9_27 := reversible_dropT _ U9_27.U_rev
theorem isUTMStrict_B9_27 : IsUTMStrict B9_27 :=
  ChainGen.isUTMStrict_drop_ctsh
    ((BlockGen.encB_primrec _ _).comp₂ (MoritaGen.encM_primrec _ _ _)) (MoritaGen.readM_primrec _ _ _)
    (Base15_6.strictBody_block15 URTM.Gen.KB9_27.spB URTM.Gen.KB9_27.TpyB U9_27.hsim
      (by decide +kernel) (by decide +kernel) (by decide +kernel))
    U9_27.U_det (by decide +kernel) _ (fun _ _ => rfl) (by decide +kernel) (by decide +kernel)

end Blocks

end URTM.Univ.Book
