/-
  **Five block-converted URTMs with two symbols merged** (results/symmerge-2026-10-04):
  (4,46)→(4,45), (5,45)→(5,42), (6,37)→(6,36), (7,32)→(7,31), (8,28)→(8,26).

  Each machine is `SymMerge.mapQ h U`, where `U` is the block-converted table of
  `LeanUniv/U<m>_<n>.lean` and `h = symMap pairs` sends each listed number to the other symbol of
  its merged pair (the identity elsewhere). The pairs are those of the README of
  results/symmerge-2026-10-04, in the numbering of `BlockGen.numB` (plain `s ↦ N.sym s`,
  counter `c<i>_s ↦ n·(i+1) + N.sym s`, `n` = the number of symbols of the base machine):

  | table  | base   | `n` | merged pairs (README names)                  | `h`                        |
  |--------|--------|-----|-----------------------------------------------|----------------------------|
  | (4,45) | (10,8) | 8   | c1_nd = c6_*                                  | 62 ↦ 19                    |
  | (5,42) | (15,6) | 6   | c8_yd = c1_b, c8_b = c1_n, yd = c1_y          | 59 ↦ 12, 54 ↦ 14, 13 ↦ 5   |
  | (6,36) | (10,8) | 8   | c5_nd = c1_*                                  | 51 ↦ 22                    |
  | (7,31) | (15,6) | 6   | c4_b = yd                                     | 30 ↦ 5                     |
  | (8,26) | (17,5) | 5   | $ = c2_y, c4_$ = c2_n                         | 16 ↦ 4, 29 ↦ 17            |

  When a pair has a plain symbol (`< n`), the counter is sent to it, so `h` is the identity on the
  plain symbols `List.range n`, the only symbols of the halting IDs (`BlockHalt`); the section
  of `h` used by the decoder is then `id`.

  Per machine: the counts, determinism and reversibility by `decide +kernel`; universality by
  `SymMerge.isUTMStrict_mapQ` from the strong form `BlockHalt.isUTMStrictHalt_block<base>` of the
  unmerged table (whose hypotheses are those of `U<m>_<n>.isUTMStrict_U`, plus `U_det`).
-/
import LeanUniv.U4_46
import LeanUniv.U5_45
import LeanUniv.U6_37
import LeanUniv.U7_32
import LeanUniv.U8_28
import LeanUniv.BlockHalt

namespace URTM.Univ.MergeBlocks
open URTM URTM.Univ.SymMerge

/-! ### (4,46) → (4,45): c1_nd = c6_* -/

namespace M4_45
open URTM.Gen.KB4_46 (spB TpyB)

/-- c6_* (62) ↦ c1_nd (19). -/
def h : ℕ → ℕ := symMap [(62, 19)]

/-- **URTM(4,45)**: URTM(4,46) with c6_* and c1_nd merged. -/
def U : List Quint := mapQ h U4_46.U

theorem U_counts : Spec.NStates U = 4 ∧ Spec.NSyms U = 45 := by decide +kernel
theorem U_det : Spec.Deterministic U := by decide +kernel
theorem U_rev : Spec.Reversible U := by decide +kernel

/-- The strong form of Def. 7.1 for URTM(4,46). -/
theorem strong : IsUTMStrictHalt U4_46.U (List.range 8) :=
  BlockHalt.isUTMStrictHalt_block10 spB TpyB U4_46.hsim U4_46.U_det (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

/-- **URTM(4,45) is a UTM in the strict sense of Morita Def. 7.1.** -/
theorem isUTMStrict_U : Spec.IsUTMStrict U :=
  isUTMStrict_mapQ (s := id) strong U_det (symMap_primrec _) Primrec.id rfl rfl (by decide)

end M4_45

/-! ### (5,45) → (5,42): c8_yd = c1_b, c8_b = c1_n, yd = c1_y -/

namespace M5_42
open URTM.Gen.KB5_45 (spB TpyB)

/-- c8_yd (59) ↦ c1_b (12), c8_b (54) ↦ c1_n (14), c1_y (13) ↦ yd (5). -/
def h : ℕ → ℕ := symMap [(59, 12), (54, 14), (13, 5)]

/-- **URTM(5,42)**: URTM(5,45) with three pairs of symbols merged. -/
def U : List Quint := mapQ h U5_45.U

theorem U_counts : Spec.NStates U = 5 ∧ Spec.NSyms U = 42 := by decide +kernel
theorem U_det : Spec.Deterministic U := by decide +kernel
theorem U_rev : Spec.Reversible U := by decide +kernel

/-- The strong form of Def. 7.1 for URTM(5,45). -/
theorem strong : IsUTMStrictHalt U5_45.U (List.range 6) :=
  BlockHalt.isUTMStrictHalt_block15 spB TpyB U5_45.hsim U5_45.U_det (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

/-- **URTM(5,42) is a UTM in the strict sense of Morita Def. 7.1.** -/
theorem isUTMStrict_U : Spec.IsUTMStrict U :=
  isUTMStrict_mapQ (s := id) strong U_det (symMap_primrec _) Primrec.id rfl rfl (by decide)

end M5_42

/-! ### (6,37) → (6,36): c5_nd = c1_* -/

namespace M6_36
open URTM.Gen.KB6_37 (spB TpyB)

/-- c5_nd (51) ↦ c1_* (22). -/
def h : ℕ → ℕ := symMap [(51, 22)]

/-- **URTM(6,36)**: URTM(6,37) with c5_nd and c1_* merged. -/
def U : List Quint := mapQ h U6_37.U

theorem U_counts : Spec.NStates U = 6 ∧ Spec.NSyms U = 36 := by decide +kernel
theorem U_det : Spec.Deterministic U := by decide +kernel
theorem U_rev : Spec.Reversible U := by decide +kernel

/-- The strong form of Def. 7.1 for URTM(6,37). -/
theorem strong : IsUTMStrictHalt U6_37.U (List.range 8) :=
  BlockHalt.isUTMStrictHalt_block10 spB TpyB U6_37.hsim U6_37.U_det (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

/-- **URTM(6,36) is a UTM in the strict sense of Morita Def. 7.1.** -/
theorem isUTMStrict_U : Spec.IsUTMStrict U :=
  isUTMStrict_mapQ (s := id) strong U_det (symMap_primrec _) Primrec.id rfl rfl (by decide)

end M6_36

/-! ### (7,32) → (7,31): c4_b = yd -/

namespace M7_31
open URTM.Gen.KB7_32 (spB TpyB)

/-- c4_b (30) ↦ yd (5). -/
def h : ℕ → ℕ := symMap [(30, 5)]

/-- **URTM(7,31)**: URTM(7,32) with c4_b and yd merged. -/
def U : List Quint := mapQ h U7_32.U

theorem U_counts : Spec.NStates U = 7 ∧ Spec.NSyms U = 31 := by decide +kernel
theorem U_det : Spec.Deterministic U := by decide +kernel
theorem U_rev : Spec.Reversible U := by decide +kernel

/-- The strong form of Def. 7.1 for URTM(7,32). -/
theorem strong : IsUTMStrictHalt U7_32.U (List.range 6) :=
  BlockHalt.isUTMStrictHalt_block15 spB TpyB U7_32.hsim U7_32.U_det (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

/-- **URTM(7,31) is a UTM in the strict sense of Morita Def. 7.1.** -/
theorem isUTMStrict_U : Spec.IsUTMStrict U :=
  isUTMStrict_mapQ (s := id) strong U_det (symMap_primrec _) Primrec.id rfl rfl (by decide)

end M7_31

/-! ### (8,28) → (8,26): $ = c2_y, c4_$ = c2_n -/

namespace M8_26
open URTM.Gen.KB8_28 (spB TpyB)

/-- c2_y (16) ↦ $ (4), c4_$ (29) ↦ c2_n (17). -/
def h : ℕ → ℕ := symMap [(16, 4), (29, 17)]

/-- **URTM(8,26)**: URTM(8,28) with two pairs of symbols merged. -/
def U : List Quint := mapQ h U8_28.U

theorem U_counts : Spec.NStates U = 8 ∧ Spec.NSyms U = 26 := by decide +kernel
theorem U_det : Spec.Deterministic U := by decide +kernel
theorem U_rev : Spec.Reversible U := by decide +kernel

/-- The strong form of Def. 7.1 for URTM(8,28). -/
theorem strong : IsUTMStrictHalt U8_28.U (List.range 5) :=
  BlockHalt.isUTMStrictHalt_block17 spB TpyB U8_28.hsim U8_28.U_det (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

/-- **URTM(8,26) is a UTM in the strict sense of Morita Def. 7.1.** -/
theorem isUTMStrict_U : Spec.IsUTMStrict U :=
  isUTMStrict_mapQ (s := id) strong U_det (symMap_primrec _) Primrec.id rfl rfl (by decide)

end M8_26

end URTM.Univ.MergeBlocks
