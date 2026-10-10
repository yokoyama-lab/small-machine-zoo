-- 生成物（tools/gen_three_cover.py）。手で編集しない。
/-
  全数検査の束ね（`lvl4` の定理から `lvl0 cov = true` へ。証明書の再計算はしない）。
-/
import URTM.ThreeCov.P000
import URTM.ThreeCov.P001
import URTM.ThreeCov.P002
import URTM.ThreeCov.P003
import URTM.ThreeCov.P004
import URTM.ThreeCov.P005
import URTM.ThreeCov.P006
import URTM.ThreeCov.P007
import URTM.ThreeCov.P008
import URTM.ThreeCov.P009
import URTM.ThreeCov.P010
import URTM.ThreeCov.P011
import URTM.ThreeCov.P012
import URTM.ThreeCov.P013
import URTM.ThreeCov.P014
import URTM.ThreeCov.P015
import URTM.ThreeCov.P016
import URTM.ThreeCov.P017
import URTM.ThreeCov.P018
import URTM.ThreeCov.P019
import URTM.ThreeCov.P020
import URTM.ThreeCov.P021
import URTM.ThreeCov.P022
import URTM.ThreeCov.P023
import URTM.ThreeCov.P024
import URTM.ThreeCov.P025
import URTM.ThreeCov.P026
import URTM.ThreeCov.P027
import URTM.ThreeCov.P028
import URTM.ThreeCov.P029
import URTM.ThreeCov.P030
import URTM.ThreeCov.P031
import URTM.ThreeCov.P032
import URTM.ThreeCov.P033
import URTM.ThreeCov.P034
import URTM.ThreeCov.P035
import URTM.ThreeCov.P036
import URTM.ThreeCov.P037
import URTM.ThreeCov.P038
import URTM.ThreeCov.P039
import URTM.ThreeCov.P040
import URTM.ThreeCov.P041
import URTM.ThreeCov.P042
import URTM.ThreeCov.P043
import URTM.ThreeCov.P044
import URTM.ThreeCov.P045
import URTM.ThreeCov.P046
import URTM.ThreeCov.P047
import URTM.ThreeCov.P048
import URTM.ThreeCov.P049
import URTM.ThreeCov.P050
import URTM.ThreeCov.P051
import URTM.ThreeCov.P052
import URTM.ThreeCov.P053
import URTM.ThreeCov.P054
import URTM.ThreeCov.P055
import URTM.ThreeCov.P056
import URTM.ThreeCov.P057
import URTM.ThreeCov.P058
import URTM.ThreeCov.P059
import URTM.ThreeCov.P060
import URTM.ThreeCov.P061

namespace URTM.Three

theorem l3_0_0_0 : lvl3 0 0 0 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_0_0_0_0]; rfl
  | 1, _ => rw [l4_0_0_0_1]; rfl
  | 2, _ => rw [l4_0_0_0_2]; rfl
  | 3, _ => rw [l4_0_0_0_3]; rfl
  | 4, _ => rw [l4_0_0_0_4]; rfl
  | 5, _ => rw [l4_0_0_0_5]; rfl
  | 6, _ => rw [l4_0_0_0_6]; rfl
  | _ + 7, h => omega

theorem l3_0_0_1 : lvl3 0 0 1 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_0_0_1_0]; rfl
  | 1, _ => rfl
  | 2, _ => rw [l4_0_0_1_2]; rfl
  | 3, _ => rw [l4_0_0_1_3]; rfl
  | 4, _ => rw [l4_0_0_1_4]; rfl
  | 5, _ => rw [l4_0_0_1_5]; rfl
  | 6, _ => rw [l4_0_0_1_6]; rfl
  | _ + 7, h => omega

theorem l3_0_0_2 : lvl3 0 0 2 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_0_0_2_0]; rfl
  | 1, _ => rw [l4_0_0_2_1]; rfl
  | 2, _ => rfl
  | 3, _ => rw [l4_0_0_2_3]; rfl
  | 4, _ => rw [l4_0_0_2_4]; rfl
  | 5, _ => rw [l4_0_0_2_5]; rfl
  | 6, _ => rw [l4_0_0_2_6]; rfl
  | _ + 7, h => omega

theorem l3_0_0_3 : lvl3 0 0 3 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_0_0_3_0]; rfl
  | 1, _ => rw [l4_0_0_3_1]; rfl
  | 2, _ => rw [l4_0_0_3_2]; rfl
  | 3, _ => rfl
  | 4, _ => rw [l4_0_0_3_4]; rfl
  | 5, _ => rw [l4_0_0_3_5]; rfl
  | 6, _ => rw [l4_0_0_3_6]; rfl
  | _ + 7, h => omega

theorem l3_0_0_4 : lvl3 0 0 4 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_0_0_4_0]; rfl
  | 1, _ => rw [l4_0_0_4_1]; rfl
  | 2, _ => rw [l4_0_0_4_2]; rfl
  | 3, _ => rw [l4_0_0_4_3]; rfl
  | 4, _ => rfl
  | 5, _ => rw [l4_0_0_4_5]; rfl
  | 6, _ => rw [l4_0_0_4_6]; rfl
  | _ + 7, h => omega

theorem l3_0_0_5 : lvl3 0 0 5 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_0_0_5_0]; rfl
  | 1, _ => rw [l4_0_0_5_1]; rfl
  | 2, _ => rw [l4_0_0_5_2]; rfl
  | 3, _ => rw [l4_0_0_5_3]; rfl
  | 4, _ => rw [l4_0_0_5_4]; rfl
  | 5, _ => rfl
  | 6, _ => rw [l4_0_0_5_6]; rfl
  | _ + 7, h => omega

theorem l3_0_0_6 : lvl3 0 0 6 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_0_0_6_0]; rfl
  | 1, _ => rw [l4_0_0_6_1]; rfl
  | 2, _ => rw [l4_0_0_6_2]; rfl
  | 3, _ => rw [l4_0_0_6_3]; rfl
  | 4, _ => rw [l4_0_0_6_4]; rfl
  | 5, _ => rw [l4_0_0_6_5]; rfl
  | 6, _ => rfl
  | _ + 7, h => omega

theorem l3_0_1_0 : lvl3 0 1 0 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_0_1_0_0]; rfl
  | 1, _ => rfl
  | 2, _ => rw [l4_0_1_0_2]; rfl
  | 3, _ => rw [l4_0_1_0_3]; rfl
  | 4, _ => rw [l4_0_1_0_4]; rfl
  | 5, _ => rw [l4_0_1_0_5]; rfl
  | 6, _ => rw [l4_0_1_0_6]; rfl
  | _ + 7, h => omega

theorem l3_0_1_2 : lvl3 0 1 2 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_0_1_2_0]; rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rw [l4_0_1_2_3]; rfl
  | 4, _ => rw [l4_0_1_2_4]; rfl
  | 5, _ => rw [l4_0_1_2_5]; rfl
  | 6, _ => rw [l4_0_1_2_6]; rfl
  | _ + 7, h => omega

theorem l3_0_1_3 : lvl3 0 1 3 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_0_1_3_0]; rfl
  | 1, _ => rfl
  | 2, _ => rw [l4_0_1_3_2]; rfl
  | 3, _ => rfl
  | 4, _ => rw [l4_0_1_3_4]; rfl
  | 5, _ => rw [l4_0_1_3_5]; rfl
  | 6, _ => rw [l4_0_1_3_6]; rfl
  | _ + 7, h => omega

theorem l3_0_1_4 : lvl3 0 1 4 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_0_1_4_0]; rfl
  | 1, _ => rfl
  | 2, _ => rw [l4_0_1_4_2]; rfl
  | 3, _ => rw [l4_0_1_4_3]; rfl
  | 4, _ => rfl
  | 5, _ => rw [l4_0_1_4_5]; rfl
  | 6, _ => rw [l4_0_1_4_6]; rfl
  | _ + 7, h => omega

theorem l3_0_1_5 : lvl3 0 1 5 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_0_1_5_0]; rfl
  | 1, _ => rfl
  | 2, _ => rw [l4_0_1_5_2]; rfl
  | 3, _ => rw [l4_0_1_5_3]; rfl
  | 4, _ => rw [l4_0_1_5_4]; rfl
  | 5, _ => rfl
  | 6, _ => rw [l4_0_1_5_6]; rfl
  | _ + 7, h => omega

theorem l3_0_1_6 : lvl3 0 1 6 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_0_1_6_0]; rfl
  | 1, _ => rfl
  | 2, _ => rw [l4_0_1_6_2]; rfl
  | 3, _ => rw [l4_0_1_6_3]; rfl
  | 4, _ => rw [l4_0_1_6_4]; rfl
  | 5, _ => rw [l4_0_1_6_5]; rfl
  | 6, _ => rfl
  | _ + 7, h => omega

theorem l3_0_2_0 : lvl3 0 2 0 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_0_2_0_0]; rfl
  | 1, _ => rw [l4_0_2_0_1]; rfl
  | 2, _ => rfl
  | 3, _ => rw [l4_0_2_0_3]; rfl
  | 4, _ => rw [l4_0_2_0_4]; rfl
  | 5, _ => rw [l4_0_2_0_5]; rfl
  | 6, _ => rw [l4_0_2_0_6]; rfl
  | _ + 7, h => omega

theorem l3_0_2_1 : lvl3 0 2 1 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_0_2_1_0]; rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rw [l4_0_2_1_3]; rfl
  | 4, _ => rw [l4_0_2_1_4]; rfl
  | 5, _ => rw [l4_0_2_1_5]; rfl
  | 6, _ => rw [l4_0_2_1_6]; rfl
  | _ + 7, h => omega

theorem l3_0_2_3 : lvl3 0 2 3 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_0_2_3_0]; rfl
  | 1, _ => rw [l4_0_2_3_1]; rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rw [l4_0_2_3_4]; rfl
  | 5, _ => rw [l4_0_2_3_5]; rfl
  | 6, _ => rw [l4_0_2_3_6]; rfl
  | _ + 7, h => omega

theorem l3_0_2_4 : lvl3 0 2 4 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_0_2_4_0]; rfl
  | 1, _ => rw [l4_0_2_4_1]; rfl
  | 2, _ => rfl
  | 3, _ => rw [l4_0_2_4_3]; rfl
  | 4, _ => rfl
  | 5, _ => rw [l4_0_2_4_5]; rfl
  | 6, _ => rw [l4_0_2_4_6]; rfl
  | _ + 7, h => omega

theorem l3_0_2_5 : lvl3 0 2 5 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_0_2_5_0]; rfl
  | 1, _ => rw [l4_0_2_5_1]; rfl
  | 2, _ => rfl
  | 3, _ => rw [l4_0_2_5_3]; rfl
  | 4, _ => rw [l4_0_2_5_4]; rfl
  | 5, _ => rfl
  | 6, _ => rw [l4_0_2_5_6]; rfl
  | _ + 7, h => omega

theorem l3_0_2_6 : lvl3 0 2 6 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_0_2_6_0]; rfl
  | 1, _ => rw [l4_0_2_6_1]; rfl
  | 2, _ => rfl
  | 3, _ => rw [l4_0_2_6_3]; rfl
  | 4, _ => rw [l4_0_2_6_4]; rfl
  | 5, _ => rw [l4_0_2_6_5]; rfl
  | 6, _ => rfl
  | _ + 7, h => omega

theorem l3_0_3_0 : lvl3 0 3 0 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_0_3_0_0]; rfl
  | 1, _ => rw [l4_0_3_0_1]; rfl
  | 2, _ => rw [l4_0_3_0_2]; rfl
  | 3, _ => rfl
  | 4, _ => rw [l4_0_3_0_4]; rfl
  | 5, _ => rw [l4_0_3_0_5]; rfl
  | 6, _ => rw [l4_0_3_0_6]; rfl
  | _ + 7, h => omega

theorem l3_0_3_1 : lvl3 0 3 1 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_0_3_1_0]; rfl
  | 1, _ => rfl
  | 2, _ => rw [l4_0_3_1_2]; rfl
  | 3, _ => rfl
  | 4, _ => rw [l4_0_3_1_4]; rfl
  | 5, _ => rw [l4_0_3_1_5]; rfl
  | 6, _ => rw [l4_0_3_1_6]; rfl
  | _ + 7, h => omega

theorem l3_0_3_2 : lvl3 0 3 2 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_0_3_2_0]; rfl
  | 1, _ => rw [l4_0_3_2_1]; rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rw [l4_0_3_2_4]; rfl
  | 5, _ => rw [l4_0_3_2_5]; rfl
  | 6, _ => rw [l4_0_3_2_6]; rfl
  | _ + 7, h => omega

theorem l3_0_3_4 : lvl3 0 3 4 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_0_3_4_0]; rfl
  | 1, _ => rw [l4_0_3_4_1]; rfl
  | 2, _ => rw [l4_0_3_4_2]; rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rw [l4_0_3_4_5]; rfl
  | 6, _ => rw [l4_0_3_4_6]; rfl
  | _ + 7, h => omega

theorem l3_0_3_5 : lvl3 0 3 5 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_0_3_5_0]; rfl
  | 1, _ => rw [l4_0_3_5_1]; rfl
  | 2, _ => rw [l4_0_3_5_2]; rfl
  | 3, _ => rfl
  | 4, _ => rw [l4_0_3_5_4]; rfl
  | 5, _ => rfl
  | 6, _ => rw [l4_0_3_5_6]; rfl
  | _ + 7, h => omega

theorem l3_0_3_6 : lvl3 0 3 6 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_0_3_6_0]; rfl
  | 1, _ => rw [l4_0_3_6_1]; rfl
  | 2, _ => rw [l4_0_3_6_2]; rfl
  | 3, _ => rfl
  | 4, _ => rw [l4_0_3_6_4]; rfl
  | 5, _ => rw [l4_0_3_6_5]; rfl
  | 6, _ => rfl
  | _ + 7, h => omega

theorem l3_0_4_0 : lvl3 0 4 0 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_0_4_0_0]; rfl
  | 1, _ => rw [l4_0_4_0_1]; rfl
  | 2, _ => rw [l4_0_4_0_2]; rfl
  | 3, _ => rw [l4_0_4_0_3]; rfl
  | 4, _ => rfl
  | 5, _ => rw [l4_0_4_0_5]; rfl
  | 6, _ => rw [l4_0_4_0_6]; rfl
  | _ + 7, h => omega

theorem l3_0_4_1 : lvl3 0 4 1 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_0_4_1_0]; rfl
  | 1, _ => rfl
  | 2, _ => rw [l4_0_4_1_2]; rfl
  | 3, _ => rw [l4_0_4_1_3]; rfl
  | 4, _ => rfl
  | 5, _ => rw [l4_0_4_1_5]; rfl
  | 6, _ => rw [l4_0_4_1_6]; rfl
  | _ + 7, h => omega

theorem l3_0_4_2 : lvl3 0 4 2 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_0_4_2_0]; rfl
  | 1, _ => rw [l4_0_4_2_1]; rfl
  | 2, _ => rfl
  | 3, _ => rw [l4_0_4_2_3]; rfl
  | 4, _ => rfl
  | 5, _ => rw [l4_0_4_2_5]; rfl
  | 6, _ => rw [l4_0_4_2_6]; rfl
  | _ + 7, h => omega

theorem l3_0_4_3 : lvl3 0 4 3 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_0_4_3_0]; rfl
  | 1, _ => rw [l4_0_4_3_1]; rfl
  | 2, _ => rw [l4_0_4_3_2]; rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rw [l4_0_4_3_5]; rfl
  | 6, _ => rw [l4_0_4_3_6]; rfl
  | _ + 7, h => omega

theorem l3_0_4_5 : lvl3 0 4 5 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_0_4_5_0]; rfl
  | 1, _ => rw [l4_0_4_5_1]; rfl
  | 2, _ => rw [l4_0_4_5_2]; rfl
  | 3, _ => rw [l4_0_4_5_3]; rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | 6, _ => rw [l4_0_4_5_6]; rfl
  | _ + 7, h => omega

theorem l3_0_4_6 : lvl3 0 4 6 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_0_4_6_0]; rfl
  | 1, _ => rw [l4_0_4_6_1]; rfl
  | 2, _ => rw [l4_0_4_6_2]; rfl
  | 3, _ => rw [l4_0_4_6_3]; rfl
  | 4, _ => rfl
  | 5, _ => rw [l4_0_4_6_5]; rfl
  | 6, _ => rfl
  | _ + 7, h => omega

theorem l3_0_5_0 : lvl3 0 5 0 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_0_5_0_0]; rfl
  | 1, _ => rw [l4_0_5_0_1]; rfl
  | 2, _ => rw [l4_0_5_0_2]; rfl
  | 3, _ => rw [l4_0_5_0_3]; rfl
  | 4, _ => rw [l4_0_5_0_4]; rfl
  | 5, _ => rfl
  | 6, _ => rw [l4_0_5_0_6]; rfl
  | _ + 7, h => omega

theorem l3_0_5_1 : lvl3 0 5 1 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_0_5_1_0]; rfl
  | 1, _ => rfl
  | 2, _ => rw [l4_0_5_1_2]; rfl
  | 3, _ => rw [l4_0_5_1_3]; rfl
  | 4, _ => rw [l4_0_5_1_4]; rfl
  | 5, _ => rfl
  | 6, _ => rw [l4_0_5_1_6]; rfl
  | _ + 7, h => omega

theorem l3_0_5_2 : lvl3 0 5 2 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_0_5_2_0]; rfl
  | 1, _ => rw [l4_0_5_2_1]; rfl
  | 2, _ => rfl
  | 3, _ => rw [l4_0_5_2_3]; rfl
  | 4, _ => rw [l4_0_5_2_4]; rfl
  | 5, _ => rfl
  | 6, _ => rw [l4_0_5_2_6]; rfl
  | _ + 7, h => omega

theorem l3_0_5_3 : lvl3 0 5 3 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_0_5_3_0]; rfl
  | 1, _ => rw [l4_0_5_3_1]; rfl
  | 2, _ => rw [l4_0_5_3_2]; rfl
  | 3, _ => rfl
  | 4, _ => rw [l4_0_5_3_4]; rfl
  | 5, _ => rfl
  | 6, _ => rw [l4_0_5_3_6]; rfl
  | _ + 7, h => omega

theorem l3_0_5_4 : lvl3 0 5 4 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_0_5_4_0]; rfl
  | 1, _ => rw [l4_0_5_4_1]; rfl
  | 2, _ => rw [l4_0_5_4_2]; rfl
  | 3, _ => rw [l4_0_5_4_3]; rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | 6, _ => rw [l4_0_5_4_6]; rfl
  | _ + 7, h => omega

theorem l3_0_5_6 : lvl3 0 5 6 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_0_5_6_0]; rfl
  | 1, _ => rw [l4_0_5_6_1]; rfl
  | 2, _ => rw [l4_0_5_6_2]; rfl
  | 3, _ => rw [l4_0_5_6_3]; rfl
  | 4, _ => rw [l4_0_5_6_4]; rfl
  | 5, _ => rfl
  | 6, _ => rfl
  | _ + 7, h => omega

theorem l3_0_6_0 : lvl3 0 6 0 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_0_6_0_0]; rfl
  | 1, _ => rw [l4_0_6_0_1]; rfl
  | 2, _ => rw [l4_0_6_0_2]; rfl
  | 3, _ => rw [l4_0_6_0_3]; rfl
  | 4, _ => rw [l4_0_6_0_4]; rfl
  | 5, _ => rw [l4_0_6_0_5]; rfl
  | 6, _ => rfl
  | _ + 7, h => omega

theorem l3_0_6_1 : lvl3 0 6 1 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_0_6_1_0]; rfl
  | 1, _ => rfl
  | 2, _ => rw [l4_0_6_1_2]; rfl
  | 3, _ => rw [l4_0_6_1_3]; rfl
  | 4, _ => rw [l4_0_6_1_4]; rfl
  | 5, _ => rw [l4_0_6_1_5]; rfl
  | 6, _ => rfl
  | _ + 7, h => omega

theorem l3_0_6_2 : lvl3 0 6 2 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_0_6_2_0]; rfl
  | 1, _ => rw [l4_0_6_2_1]; rfl
  | 2, _ => rfl
  | 3, _ => rw [l4_0_6_2_3]; rfl
  | 4, _ => rw [l4_0_6_2_4]; rfl
  | 5, _ => rw [l4_0_6_2_5]; rfl
  | 6, _ => rfl
  | _ + 7, h => omega

theorem l3_0_6_3 : lvl3 0 6 3 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_0_6_3_0]; rfl
  | 1, _ => rw [l4_0_6_3_1]; rfl
  | 2, _ => rw [l4_0_6_3_2]; rfl
  | 3, _ => rfl
  | 4, _ => rw [l4_0_6_3_4]; rfl
  | 5, _ => rw [l4_0_6_3_5]; rfl
  | 6, _ => rfl
  | _ + 7, h => omega

theorem l3_0_6_4 : lvl3 0 6 4 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_0_6_4_0]; rfl
  | 1, _ => rw [l4_0_6_4_1]; rfl
  | 2, _ => rw [l4_0_6_4_2]; rfl
  | 3, _ => rw [l4_0_6_4_3]; rfl
  | 4, _ => rfl
  | 5, _ => rw [l4_0_6_4_5]; rfl
  | 6, _ => rfl
  | _ + 7, h => omega

theorem l3_0_6_5 : lvl3 0 6 5 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_0_6_5_0]; rfl
  | 1, _ => rw [l4_0_6_5_1]; rfl
  | 2, _ => rw [l4_0_6_5_2]; rfl
  | 3, _ => rw [l4_0_6_5_3]; rfl
  | 4, _ => rw [l4_0_6_5_4]; rfl
  | 5, _ => rfl
  | 6, _ => rfl
  | _ + 7, h => omega

theorem l3_1_0_0 : lvl3 1 0 0 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_1_0_0_0]; rfl
  | 1, _ => rfl
  | 2, _ => rw [l4_1_0_0_2]; rfl
  | 3, _ => rw [l4_1_0_0_3]; rfl
  | 4, _ => rw [l4_1_0_0_4]; rfl
  | 5, _ => rw [l4_1_0_0_5]; rfl
  | 6, _ => rw [l4_1_0_0_6]; rfl
  | _ + 7, h => omega

theorem l3_1_0_2 : lvl3 1 0 2 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_1_0_2_0]; rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rw [l4_1_0_2_3]; rfl
  | 4, _ => rw [l4_1_0_2_4]; rfl
  | 5, _ => rw [l4_1_0_2_5]; rfl
  | 6, _ => rw [l4_1_0_2_6]; rfl
  | _ + 7, h => omega

theorem l3_1_0_3 : lvl3 1 0 3 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_1_0_3_0]; rfl
  | 1, _ => rfl
  | 2, _ => rw [l4_1_0_3_2]; rfl
  | 3, _ => rfl
  | 4, _ => rw [l4_1_0_3_4]; rfl
  | 5, _ => rw [l4_1_0_3_5]; rfl
  | 6, _ => rw [l4_1_0_3_6]; rfl
  | _ + 7, h => omega

theorem l3_1_0_4 : lvl3 1 0 4 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_1_0_4_0]; rfl
  | 1, _ => rfl
  | 2, _ => rw [l4_1_0_4_2]; rfl
  | 3, _ => rw [l4_1_0_4_3]; rfl
  | 4, _ => rfl
  | 5, _ => rw [l4_1_0_4_5]; rfl
  | 6, _ => rw [l4_1_0_4_6]; rfl
  | _ + 7, h => omega

theorem l3_1_0_5 : lvl3 1 0 5 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_1_0_5_0]; rfl
  | 1, _ => rfl
  | 2, _ => rw [l4_1_0_5_2]; rfl
  | 3, _ => rw [l4_1_0_5_3]; rfl
  | 4, _ => rw [l4_1_0_5_4]; rfl
  | 5, _ => rfl
  | 6, _ => rw [l4_1_0_5_6]; rfl
  | _ + 7, h => omega

theorem l3_1_0_6 : lvl3 1 0 6 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_1_0_6_0]; rfl
  | 1, _ => rfl
  | 2, _ => rw [l4_1_0_6_2]; rfl
  | 3, _ => rw [l4_1_0_6_3]; rfl
  | 4, _ => rw [l4_1_0_6_4]; rfl
  | 5, _ => rw [l4_1_0_6_5]; rfl
  | 6, _ => rfl
  | _ + 7, h => omega

theorem l3_1_2_0 : lvl3 1 2 0 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_1_2_0_0]; rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rw [l4_1_2_0_3]; rfl
  | 4, _ => rw [l4_1_2_0_4]; rfl
  | 5, _ => rw [l4_1_2_0_5]; rfl
  | 6, _ => rw [l4_1_2_0_6]; rfl
  | _ + 7, h => omega

theorem l3_1_2_3 : lvl3 1 2 3 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_1_2_3_0]; rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rw [l4_1_2_3_4]; rfl
  | 5, _ => rw [l4_1_2_3_5]; rfl
  | 6, _ => rw [l4_1_2_3_6]; rfl
  | _ + 7, h => omega

theorem l3_1_2_4 : lvl3 1 2 4 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_1_2_4_0]; rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rw [l4_1_2_4_3]; rfl
  | 4, _ => rfl
  | 5, _ => rw [l4_1_2_4_5]; rfl
  | 6, _ => rw [l4_1_2_4_6]; rfl
  | _ + 7, h => omega

theorem l3_1_2_5 : lvl3 1 2 5 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_1_2_5_0]; rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rw [l4_1_2_5_3]; rfl
  | 4, _ => rw [l4_1_2_5_4]; rfl
  | 5, _ => rfl
  | 6, _ => rw [l4_1_2_5_6]; rfl
  | _ + 7, h => omega

theorem l3_1_2_6 : lvl3 1 2 6 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_1_2_6_0]; rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rw [l4_1_2_6_3]; rfl
  | 4, _ => rw [l4_1_2_6_4]; rfl
  | 5, _ => rw [l4_1_2_6_5]; rfl
  | 6, _ => rfl
  | _ + 7, h => omega

theorem l3_1_3_0 : lvl3 1 3 0 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_1_3_0_0]; rfl
  | 1, _ => rfl
  | 2, _ => rw [l4_1_3_0_2]; rfl
  | 3, _ => rfl
  | 4, _ => rw [l4_1_3_0_4]; rfl
  | 5, _ => rw [l4_1_3_0_5]; rfl
  | 6, _ => rw [l4_1_3_0_6]; rfl
  | _ + 7, h => omega

theorem l3_1_3_2 : lvl3 1 3 2 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_1_3_2_0]; rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rw [l4_1_3_2_4]; rfl
  | 5, _ => rw [l4_1_3_2_5]; rfl
  | 6, _ => rw [l4_1_3_2_6]; rfl
  | _ + 7, h => omega

theorem l3_1_3_4 : lvl3 1 3 4 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_1_3_4_0]; rfl
  | 1, _ => rfl
  | 2, _ => rw [l4_1_3_4_2]; rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rw [l4_1_3_4_5]; rfl
  | 6, _ => rw [l4_1_3_4_6]; rfl
  | _ + 7, h => omega

theorem l3_1_3_5 : lvl3 1 3 5 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_1_3_5_0]; rfl
  | 1, _ => rfl
  | 2, _ => rw [l4_1_3_5_2]; rfl
  | 3, _ => rfl
  | 4, _ => rw [l4_1_3_5_4]; rfl
  | 5, _ => rfl
  | 6, _ => rw [l4_1_3_5_6]; rfl
  | _ + 7, h => omega

theorem l3_1_3_6 : lvl3 1 3 6 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_1_3_6_0]; rfl
  | 1, _ => rfl
  | 2, _ => rw [l4_1_3_6_2]; rfl
  | 3, _ => rfl
  | 4, _ => rw [l4_1_3_6_4]; rfl
  | 5, _ => rw [l4_1_3_6_5]; rfl
  | 6, _ => rfl
  | _ + 7, h => omega

theorem l3_1_4_0 : lvl3 1 4 0 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_1_4_0_0]; rfl
  | 1, _ => rfl
  | 2, _ => rw [l4_1_4_0_2]; rfl
  | 3, _ => rw [l4_1_4_0_3]; rfl
  | 4, _ => rfl
  | 5, _ => rw [l4_1_4_0_5]; rfl
  | 6, _ => rw [l4_1_4_0_6]; rfl
  | _ + 7, h => omega

theorem l3_1_4_2 : lvl3 1 4 2 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_1_4_2_0]; rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rw [l4_1_4_2_3]; rfl
  | 4, _ => rfl
  | 5, _ => rw [l4_1_4_2_5]; rfl
  | 6, _ => rw [l4_1_4_2_6]; rfl
  | _ + 7, h => omega

theorem l3_1_4_3 : lvl3 1 4 3 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_1_4_3_0]; rfl
  | 1, _ => rfl
  | 2, _ => rw [l4_1_4_3_2]; rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rw [l4_1_4_3_5]; rfl
  | 6, _ => rw [l4_1_4_3_6]; rfl
  | _ + 7, h => omega

theorem l3_1_4_5 : lvl3 1 4 5 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_1_4_5_0]; rfl
  | 1, _ => rfl
  | 2, _ => rw [l4_1_4_5_2]; rfl
  | 3, _ => rw [l4_1_4_5_3]; rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | 6, _ => rw [l4_1_4_5_6]; rfl
  | _ + 7, h => omega

theorem l3_1_4_6 : lvl3 1 4 6 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_1_4_6_0]; rfl
  | 1, _ => rfl
  | 2, _ => rw [l4_1_4_6_2]; rfl
  | 3, _ => rw [l4_1_4_6_3]; rfl
  | 4, _ => rfl
  | 5, _ => rw [l4_1_4_6_5]; rfl
  | 6, _ => rfl
  | _ + 7, h => omega

theorem l3_1_5_0 : lvl3 1 5 0 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_1_5_0_0]; rfl
  | 1, _ => rfl
  | 2, _ => rw [l4_1_5_0_2]; rfl
  | 3, _ => rw [l4_1_5_0_3]; rfl
  | 4, _ => rw [l4_1_5_0_4]; rfl
  | 5, _ => rfl
  | 6, _ => rw [l4_1_5_0_6]; rfl
  | _ + 7, h => omega

theorem l3_1_5_2 : lvl3 1 5 2 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_1_5_2_0]; rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rw [l4_1_5_2_3]; rfl
  | 4, _ => rw [l4_1_5_2_4]; rfl
  | 5, _ => rfl
  | 6, _ => rw [l4_1_5_2_6]; rfl
  | _ + 7, h => omega

theorem l3_1_5_3 : lvl3 1 5 3 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_1_5_3_0]; rfl
  | 1, _ => rfl
  | 2, _ => rw [l4_1_5_3_2]; rfl
  | 3, _ => rfl
  | 4, _ => rw [l4_1_5_3_4]; rfl
  | 5, _ => rfl
  | 6, _ => rw [l4_1_5_3_6]; rfl
  | _ + 7, h => omega

theorem l3_1_5_4 : lvl3 1 5 4 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_1_5_4_0]; rfl
  | 1, _ => rfl
  | 2, _ => rw [l4_1_5_4_2]; rfl
  | 3, _ => rw [l4_1_5_4_3]; rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | 6, _ => rw [l4_1_5_4_6]; rfl
  | _ + 7, h => omega

theorem l3_1_5_6 : lvl3 1 5 6 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_1_5_6_0]; rfl
  | 1, _ => rfl
  | 2, _ => rw [l4_1_5_6_2]; rfl
  | 3, _ => rw [l4_1_5_6_3]; rfl
  | 4, _ => rw [l4_1_5_6_4]; rfl
  | 5, _ => rfl
  | 6, _ => rfl
  | _ + 7, h => omega

theorem l3_1_6_0 : lvl3 1 6 0 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_1_6_0_0]; rfl
  | 1, _ => rfl
  | 2, _ => rw [l4_1_6_0_2]; rfl
  | 3, _ => rw [l4_1_6_0_3]; rfl
  | 4, _ => rw [l4_1_6_0_4]; rfl
  | 5, _ => rw [l4_1_6_0_5]; rfl
  | 6, _ => rfl
  | _ + 7, h => omega

theorem l3_1_6_2 : lvl3 1 6 2 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_1_6_2_0]; rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rw [l4_1_6_2_3]; rfl
  | 4, _ => rw [l4_1_6_2_4]; rfl
  | 5, _ => rw [l4_1_6_2_5]; rfl
  | 6, _ => rfl
  | _ + 7, h => omega

theorem l3_1_6_3 : lvl3 1 6 3 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_1_6_3_0]; rfl
  | 1, _ => rfl
  | 2, _ => rw [l4_1_6_3_2]; rfl
  | 3, _ => rfl
  | 4, _ => rw [l4_1_6_3_4]; rfl
  | 5, _ => rw [l4_1_6_3_5]; rfl
  | 6, _ => rfl
  | _ + 7, h => omega

theorem l3_1_6_4 : lvl3 1 6 4 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_1_6_4_0]; rfl
  | 1, _ => rfl
  | 2, _ => rw [l4_1_6_4_2]; rfl
  | 3, _ => rw [l4_1_6_4_3]; rfl
  | 4, _ => rfl
  | 5, _ => rw [l4_1_6_4_5]; rfl
  | 6, _ => rfl
  | _ + 7, h => omega

theorem l3_1_6_5 : lvl3 1 6 5 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_1_6_5_0]; rfl
  | 1, _ => rfl
  | 2, _ => rw [l4_1_6_5_2]; rfl
  | 3, _ => rw [l4_1_6_5_3]; rfl
  | 4, _ => rw [l4_1_6_5_4]; rfl
  | 5, _ => rfl
  | 6, _ => rfl
  | _ + 7, h => omega

theorem l3_2_0_0 : lvl3 2 0 0 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_2_0_0_0]; rfl
  | 1, _ => rw [l4_2_0_0_1]; rfl
  | 2, _ => rfl
  | 3, _ => rw [l4_2_0_0_3]; rfl
  | 4, _ => rw [l4_2_0_0_4]; rfl
  | 5, _ => rw [l4_2_0_0_5]; rfl
  | 6, _ => rw [l4_2_0_0_6]; rfl
  | _ + 7, h => omega

theorem l3_2_0_1 : lvl3 2 0 1 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_2_0_1_0]; rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rw [l4_2_0_1_3]; rfl
  | 4, _ => rw [l4_2_0_1_4]; rfl
  | 5, _ => rw [l4_2_0_1_5]; rfl
  | 6, _ => rw [l4_2_0_1_6]; rfl
  | _ + 7, h => omega

theorem l3_2_0_3 : lvl3 2 0 3 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_2_0_3_0]; rfl
  | 1, _ => rw [l4_2_0_3_1]; rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rw [l4_2_0_3_4]; rfl
  | 5, _ => rw [l4_2_0_3_5]; rfl
  | 6, _ => rw [l4_2_0_3_6]; rfl
  | _ + 7, h => omega

theorem l3_2_0_4 : lvl3 2 0 4 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_2_0_4_0]; rfl
  | 1, _ => rw [l4_2_0_4_1]; rfl
  | 2, _ => rfl
  | 3, _ => rw [l4_2_0_4_3]; rfl
  | 4, _ => rfl
  | 5, _ => rw [l4_2_0_4_5]; rfl
  | 6, _ => rw [l4_2_0_4_6]; rfl
  | _ + 7, h => omega

theorem l3_2_0_5 : lvl3 2 0 5 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_2_0_5_0]; rfl
  | 1, _ => rw [l4_2_0_5_1]; rfl
  | 2, _ => rfl
  | 3, _ => rw [l4_2_0_5_3]; rfl
  | 4, _ => rw [l4_2_0_5_4]; rfl
  | 5, _ => rfl
  | 6, _ => rw [l4_2_0_5_6]; rfl
  | _ + 7, h => omega

theorem l3_2_0_6 : lvl3 2 0 6 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_2_0_6_0]; rfl
  | 1, _ => rw [l4_2_0_6_1]; rfl
  | 2, _ => rfl
  | 3, _ => rw [l4_2_0_6_3]; rfl
  | 4, _ => rw [l4_2_0_6_4]; rfl
  | 5, _ => rw [l4_2_0_6_5]; rfl
  | 6, _ => rfl
  | _ + 7, h => omega

theorem l3_2_1_0 : lvl3 2 1 0 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_2_1_0_0]; rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rw [l4_2_1_0_3]; rfl
  | 4, _ => rw [l4_2_1_0_4]; rfl
  | 5, _ => rw [l4_2_1_0_5]; rfl
  | 6, _ => rw [l4_2_1_0_6]; rfl
  | _ + 7, h => omega

theorem l3_2_1_3 : lvl3 2 1 3 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_2_1_3_0]; rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rw [l4_2_1_3_4]; rfl
  | 5, _ => rw [l4_2_1_3_5]; rfl
  | 6, _ => rw [l4_2_1_3_6]; rfl
  | _ + 7, h => omega

theorem l3_2_1_4 : lvl3 2 1 4 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_2_1_4_0]; rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rw [l4_2_1_4_3]; rfl
  | 4, _ => rfl
  | 5, _ => rw [l4_2_1_4_5]; rfl
  | 6, _ => rw [l4_2_1_4_6]; rfl
  | _ + 7, h => omega

theorem l3_2_1_5 : lvl3 2 1 5 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_2_1_5_0]; rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rw [l4_2_1_5_3]; rfl
  | 4, _ => rw [l4_2_1_5_4]; rfl
  | 5, _ => rfl
  | 6, _ => rw [l4_2_1_5_6]; rfl
  | _ + 7, h => omega

theorem l3_2_1_6 : lvl3 2 1 6 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_2_1_6_0]; rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rw [l4_2_1_6_3]; rfl
  | 4, _ => rw [l4_2_1_6_4]; rfl
  | 5, _ => rw [l4_2_1_6_5]; rfl
  | 6, _ => rfl
  | _ + 7, h => omega

theorem l3_2_3_0 : lvl3 2 3 0 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_2_3_0_0]; rfl
  | 1, _ => rw [l4_2_3_0_1]; rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rw [l4_2_3_0_4]; rfl
  | 5, _ => rw [l4_2_3_0_5]; rfl
  | 6, _ => rw [l4_2_3_0_6]; rfl
  | _ + 7, h => omega

theorem l3_2_3_1 : lvl3 2 3 1 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_2_3_1_0]; rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rw [l4_2_3_1_4]; rfl
  | 5, _ => rw [l4_2_3_1_5]; rfl
  | 6, _ => rw [l4_2_3_1_6]; rfl
  | _ + 7, h => omega

theorem l3_2_3_4 : lvl3 2 3 4 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_2_3_4_0]; rfl
  | 1, _ => rw [l4_2_3_4_1]; rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rw [l4_2_3_4_5]; rfl
  | 6, _ => rw [l4_2_3_4_6]; rfl
  | _ + 7, h => omega

theorem l3_2_3_5 : lvl3 2 3 5 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_2_3_5_0]; rfl
  | 1, _ => rw [l4_2_3_5_1]; rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rw [l4_2_3_5_4]; rfl
  | 5, _ => rfl
  | 6, _ => rw [l4_2_3_5_6]; rfl
  | _ + 7, h => omega

theorem l3_2_3_6 : lvl3 2 3 6 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_2_3_6_0]; rfl
  | 1, _ => rw [l4_2_3_6_1]; rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rw [l4_2_3_6_4]; rfl
  | 5, _ => rw [l4_2_3_6_5]; rfl
  | 6, _ => rfl
  | _ + 7, h => omega

theorem l3_2_4_0 : lvl3 2 4 0 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_2_4_0_0]; rfl
  | 1, _ => rw [l4_2_4_0_1]; rfl
  | 2, _ => rfl
  | 3, _ => rw [l4_2_4_0_3]; rfl
  | 4, _ => rfl
  | 5, _ => rw [l4_2_4_0_5]; rfl
  | 6, _ => rw [l4_2_4_0_6]; rfl
  | _ + 7, h => omega

theorem l3_2_4_1 : lvl3 2 4 1 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_2_4_1_0]; rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rw [l4_2_4_1_3]; rfl
  | 4, _ => rfl
  | 5, _ => rw [l4_2_4_1_5]; rfl
  | 6, _ => rw [l4_2_4_1_6]; rfl
  | _ + 7, h => omega

theorem l3_2_4_3 : lvl3 2 4 3 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_2_4_3_0]; rfl
  | 1, _ => rw [l4_2_4_3_1]; rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rw [l4_2_4_3_5]; rfl
  | 6, _ => rw [l4_2_4_3_6]; rfl
  | _ + 7, h => omega

theorem l3_2_4_5 : lvl3 2 4 5 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_2_4_5_0]; rfl
  | 1, _ => rw [l4_2_4_5_1]; rfl
  | 2, _ => rfl
  | 3, _ => rw [l4_2_4_5_3]; rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | 6, _ => rw [l4_2_4_5_6]; rfl
  | _ + 7, h => omega

theorem l3_2_4_6 : lvl3 2 4 6 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_2_4_6_0]; rfl
  | 1, _ => rw [l4_2_4_6_1]; rfl
  | 2, _ => rfl
  | 3, _ => rw [l4_2_4_6_3]; rfl
  | 4, _ => rfl
  | 5, _ => rw [l4_2_4_6_5]; rfl
  | 6, _ => rfl
  | _ + 7, h => omega

theorem l3_2_5_0 : lvl3 2 5 0 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_2_5_0_0]; rfl
  | 1, _ => rw [l4_2_5_0_1]; rfl
  | 2, _ => rfl
  | 3, _ => rw [l4_2_5_0_3]; rfl
  | 4, _ => rw [l4_2_5_0_4]; rfl
  | 5, _ => rfl
  | 6, _ => rw [l4_2_5_0_6]; rfl
  | _ + 7, h => omega

theorem l3_2_5_1 : lvl3 2 5 1 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_2_5_1_0]; rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rw [l4_2_5_1_3]; rfl
  | 4, _ => rw [l4_2_5_1_4]; rfl
  | 5, _ => rfl
  | 6, _ => rw [l4_2_5_1_6]; rfl
  | _ + 7, h => omega

theorem l3_2_5_3 : lvl3 2 5 3 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_2_5_3_0]; rfl
  | 1, _ => rw [l4_2_5_3_1]; rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rw [l4_2_5_3_4]; rfl
  | 5, _ => rfl
  | 6, _ => rw [l4_2_5_3_6]; rfl
  | _ + 7, h => omega

theorem l3_2_5_4 : lvl3 2 5 4 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_2_5_4_0]; rfl
  | 1, _ => rw [l4_2_5_4_1]; rfl
  | 2, _ => rfl
  | 3, _ => rw [l4_2_5_4_3]; rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | 6, _ => rw [l4_2_5_4_6]; rfl
  | _ + 7, h => omega

theorem l3_2_5_6 : lvl3 2 5 6 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_2_5_6_0]; rfl
  | 1, _ => rw [l4_2_5_6_1]; rfl
  | 2, _ => rfl
  | 3, _ => rw [l4_2_5_6_3]; rfl
  | 4, _ => rw [l4_2_5_6_4]; rfl
  | 5, _ => rfl
  | 6, _ => rfl
  | _ + 7, h => omega

theorem l3_2_6_0 : lvl3 2 6 0 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_2_6_0_0]; rfl
  | 1, _ => rw [l4_2_6_0_1]; rfl
  | 2, _ => rfl
  | 3, _ => rw [l4_2_6_0_3]; rfl
  | 4, _ => rw [l4_2_6_0_4]; rfl
  | 5, _ => rw [l4_2_6_0_5]; rfl
  | 6, _ => rfl
  | _ + 7, h => omega

theorem l3_2_6_1 : lvl3 2 6 1 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_2_6_1_0]; rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rw [l4_2_6_1_3]; rfl
  | 4, _ => rw [l4_2_6_1_4]; rfl
  | 5, _ => rw [l4_2_6_1_5]; rfl
  | 6, _ => rfl
  | _ + 7, h => omega

theorem l3_2_6_3 : lvl3 2 6 3 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_2_6_3_0]; rfl
  | 1, _ => rw [l4_2_6_3_1]; rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rw [l4_2_6_3_4]; rfl
  | 5, _ => rw [l4_2_6_3_5]; rfl
  | 6, _ => rfl
  | _ + 7, h => omega

theorem l3_2_6_4 : lvl3 2 6 4 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_2_6_4_0]; rfl
  | 1, _ => rw [l4_2_6_4_1]; rfl
  | 2, _ => rfl
  | 3, _ => rw [l4_2_6_4_3]; rfl
  | 4, _ => rfl
  | 5, _ => rw [l4_2_6_4_5]; rfl
  | 6, _ => rfl
  | _ + 7, h => omega

theorem l3_2_6_5 : lvl3 2 6 5 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_2_6_5_0]; rfl
  | 1, _ => rw [l4_2_6_5_1]; rfl
  | 2, _ => rfl
  | 3, _ => rw [l4_2_6_5_3]; rfl
  | 4, _ => rw [l4_2_6_5_4]; rfl
  | 5, _ => rfl
  | 6, _ => rfl
  | _ + 7, h => omega

theorem l3_3_0_0 : lvl3 3 0 0 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_3_0_0_0]; rfl
  | 1, _ => rw [l4_3_0_0_1]; rfl
  | 2, _ => rw [l4_3_0_0_2]; rfl
  | 3, _ => rfl
  | 4, _ => rw [l4_3_0_0_4]; rfl
  | 5, _ => rw [l4_3_0_0_5]; rfl
  | 6, _ => rw [l4_3_0_0_6]; rfl
  | _ + 7, h => omega

theorem l3_3_0_1 : lvl3 3 0 1 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_3_0_1_0]; rfl
  | 1, _ => rfl
  | 2, _ => rw [l4_3_0_1_2]; rfl
  | 3, _ => rfl
  | 4, _ => rw [l4_3_0_1_4]; rfl
  | 5, _ => rw [l4_3_0_1_5]; rfl
  | 6, _ => rw [l4_3_0_1_6]; rfl
  | _ + 7, h => omega

theorem l3_3_0_2 : lvl3 3 0 2 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_3_0_2_0]; rfl
  | 1, _ => rw [l4_3_0_2_1]; rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rw [l4_3_0_2_4]; rfl
  | 5, _ => rw [l4_3_0_2_5]; rfl
  | 6, _ => rw [l4_3_0_2_6]; rfl
  | _ + 7, h => omega

theorem l3_3_0_4 : lvl3 3 0 4 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_3_0_4_0]; rfl
  | 1, _ => rw [l4_3_0_4_1]; rfl
  | 2, _ => rw [l4_3_0_4_2]; rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rw [l4_3_0_4_5]; rfl
  | 6, _ => rw [l4_3_0_4_6]; rfl
  | _ + 7, h => omega

theorem l3_3_0_5 : lvl3 3 0 5 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_3_0_5_0]; rfl
  | 1, _ => rw [l4_3_0_5_1]; rfl
  | 2, _ => rw [l4_3_0_5_2]; rfl
  | 3, _ => rfl
  | 4, _ => rw [l4_3_0_5_4]; rfl
  | 5, _ => rfl
  | 6, _ => rw [l4_3_0_5_6]; rfl
  | _ + 7, h => omega

theorem l3_3_0_6 : lvl3 3 0 6 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_3_0_6_0]; rfl
  | 1, _ => rw [l4_3_0_6_1]; rfl
  | 2, _ => rw [l4_3_0_6_2]; rfl
  | 3, _ => rfl
  | 4, _ => rw [l4_3_0_6_4]; rfl
  | 5, _ => rw [l4_3_0_6_5]; rfl
  | 6, _ => rfl
  | _ + 7, h => omega

theorem l3_3_1_0 : lvl3 3 1 0 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_3_1_0_0]; rfl
  | 1, _ => rfl
  | 2, _ => rw [l4_3_1_0_2]; rfl
  | 3, _ => rfl
  | 4, _ => rw [l4_3_1_0_4]; rfl
  | 5, _ => rw [l4_3_1_0_5]; rfl
  | 6, _ => rw [l4_3_1_0_6]; rfl
  | _ + 7, h => omega

theorem l3_3_1_2 : lvl3 3 1 2 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_3_1_2_0]; rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rw [l4_3_1_2_4]; rfl
  | 5, _ => rw [l4_3_1_2_5]; rfl
  | 6, _ => rw [l4_3_1_2_6]; rfl
  | _ + 7, h => omega

theorem l3_3_1_4 : lvl3 3 1 4 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_3_1_4_0]; rfl
  | 1, _ => rfl
  | 2, _ => rw [l4_3_1_4_2]; rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rw [l4_3_1_4_5]; rfl
  | 6, _ => rw [l4_3_1_4_6]; rfl
  | _ + 7, h => omega

theorem l3_3_1_5 : lvl3 3 1 5 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_3_1_5_0]; rfl
  | 1, _ => rfl
  | 2, _ => rw [l4_3_1_5_2]; rfl
  | 3, _ => rfl
  | 4, _ => rw [l4_3_1_5_4]; rfl
  | 5, _ => rfl
  | 6, _ => rw [l4_3_1_5_6]; rfl
  | _ + 7, h => omega

theorem l3_3_1_6 : lvl3 3 1 6 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_3_1_6_0]; rfl
  | 1, _ => rfl
  | 2, _ => rw [l4_3_1_6_2]; rfl
  | 3, _ => rfl
  | 4, _ => rw [l4_3_1_6_4]; rfl
  | 5, _ => rw [l4_3_1_6_5]; rfl
  | 6, _ => rfl
  | _ + 7, h => omega

theorem l3_3_2_0 : lvl3 3 2 0 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_3_2_0_0]; rfl
  | 1, _ => rw [l4_3_2_0_1]; rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rw [l4_3_2_0_4]; rfl
  | 5, _ => rw [l4_3_2_0_5]; rfl
  | 6, _ => rw [l4_3_2_0_6]; rfl
  | _ + 7, h => omega

theorem l3_3_2_1 : lvl3 3 2 1 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_3_2_1_0]; rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rw [l4_3_2_1_4]; rfl
  | 5, _ => rw [l4_3_2_1_5]; rfl
  | 6, _ => rw [l4_3_2_1_6]; rfl
  | _ + 7, h => omega

theorem l3_3_2_4 : lvl3 3 2 4 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_3_2_4_0]; rfl
  | 1, _ => rw [l4_3_2_4_1]; rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rw [l4_3_2_4_5]; rfl
  | 6, _ => rw [l4_3_2_4_6]; rfl
  | _ + 7, h => omega

theorem l3_3_2_5 : lvl3 3 2 5 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_3_2_5_0]; rfl
  | 1, _ => rw [l4_3_2_5_1]; rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rw [l4_3_2_5_4]; rfl
  | 5, _ => rfl
  | 6, _ => rw [l4_3_2_5_6]; rfl
  | _ + 7, h => omega

theorem l3_3_2_6 : lvl3 3 2 6 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_3_2_6_0]; rfl
  | 1, _ => rw [l4_3_2_6_1]; rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rw [l4_3_2_6_4]; rfl
  | 5, _ => rw [l4_3_2_6_5]; rfl
  | 6, _ => rfl
  | _ + 7, h => omega

theorem l3_3_4_0 : lvl3 3 4 0 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_3_4_0_0]; rfl
  | 1, _ => rw [l4_3_4_0_1]; rfl
  | 2, _ => rw [l4_3_4_0_2]; rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rw [l4_3_4_0_5]; rfl
  | 6, _ => rw [l4_3_4_0_6]; rfl
  | _ + 7, h => omega

theorem l3_3_4_1 : lvl3 3 4 1 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_3_4_1_0]; rfl
  | 1, _ => rfl
  | 2, _ => rw [l4_3_4_1_2]; rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rw [l4_3_4_1_5]; rfl
  | 6, _ => rw [l4_3_4_1_6]; rfl
  | _ + 7, h => omega

theorem l3_3_4_2 : lvl3 3 4 2 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_3_4_2_0]; rfl
  | 1, _ => rw [l4_3_4_2_1]; rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rw [l4_3_4_2_5]; rfl
  | 6, _ => rw [l4_3_4_2_6]; rfl
  | _ + 7, h => omega

theorem l3_3_4_5 : lvl3 3 4 5 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_3_4_5_0]; rfl
  | 1, _ => rw [l4_3_4_5_1]; rfl
  | 2, _ => rw [l4_3_4_5_2]; rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | 6, _ => rw [l4_3_4_5_6]; rfl
  | _ + 7, h => omega

theorem l3_3_4_6 : lvl3 3 4 6 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_3_4_6_0]; rfl
  | 1, _ => rw [l4_3_4_6_1]; rfl
  | 2, _ => rw [l4_3_4_6_2]; rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rw [l4_3_4_6_5]; rfl
  | 6, _ => rfl
  | _ + 7, h => omega

theorem l3_3_5_0 : lvl3 3 5 0 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_3_5_0_0]; rfl
  | 1, _ => rw [l4_3_5_0_1]; rfl
  | 2, _ => rw [l4_3_5_0_2]; rfl
  | 3, _ => rfl
  | 4, _ => rw [l4_3_5_0_4]; rfl
  | 5, _ => rfl
  | 6, _ => rw [l4_3_5_0_6]; rfl
  | _ + 7, h => omega

theorem l3_3_5_1 : lvl3 3 5 1 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_3_5_1_0]; rfl
  | 1, _ => rfl
  | 2, _ => rw [l4_3_5_1_2]; rfl
  | 3, _ => rfl
  | 4, _ => rw [l4_3_5_1_4]; rfl
  | 5, _ => rfl
  | 6, _ => rw [l4_3_5_1_6]; rfl
  | _ + 7, h => omega

theorem l3_3_5_2 : lvl3 3 5 2 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_3_5_2_0]; rfl
  | 1, _ => rw [l4_3_5_2_1]; rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rw [l4_3_5_2_4]; rfl
  | 5, _ => rfl
  | 6, _ => rw [l4_3_5_2_6]; rfl
  | _ + 7, h => omega

theorem l3_3_5_4 : lvl3 3 5 4 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_3_5_4_0]; rfl
  | 1, _ => rw [l4_3_5_4_1]; rfl
  | 2, _ => rw [l4_3_5_4_2]; rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | 6, _ => rw [l4_3_5_4_6]; rfl
  | _ + 7, h => omega

theorem l3_3_5_6 : lvl3 3 5 6 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_3_5_6_0]; rfl
  | 1, _ => rw [l4_3_5_6_1]; rfl
  | 2, _ => rw [l4_3_5_6_2]; rfl
  | 3, _ => rfl
  | 4, _ => rw [l4_3_5_6_4]; rfl
  | 5, _ => rfl
  | 6, _ => rfl
  | _ + 7, h => omega

theorem l3_3_6_0 : lvl3 3 6 0 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_3_6_0_0]; rfl
  | 1, _ => rw [l4_3_6_0_1]; rfl
  | 2, _ => rw [l4_3_6_0_2]; rfl
  | 3, _ => rfl
  | 4, _ => rw [l4_3_6_0_4]; rfl
  | 5, _ => rw [l4_3_6_0_5]; rfl
  | 6, _ => rfl
  | _ + 7, h => omega

theorem l3_3_6_1 : lvl3 3 6 1 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_3_6_1_0]; rfl
  | 1, _ => rfl
  | 2, _ => rw [l4_3_6_1_2]; rfl
  | 3, _ => rfl
  | 4, _ => rw [l4_3_6_1_4]; rfl
  | 5, _ => rw [l4_3_6_1_5]; rfl
  | 6, _ => rfl
  | _ + 7, h => omega

theorem l3_3_6_2 : lvl3 3 6 2 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_3_6_2_0]; rfl
  | 1, _ => rw [l4_3_6_2_1]; rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rw [l4_3_6_2_4]; rfl
  | 5, _ => rw [l4_3_6_2_5]; rfl
  | 6, _ => rfl
  | _ + 7, h => omega

theorem l3_3_6_4 : lvl3 3 6 4 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_3_6_4_0]; rfl
  | 1, _ => rw [l4_3_6_4_1]; rfl
  | 2, _ => rw [l4_3_6_4_2]; rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rw [l4_3_6_4_5]; rfl
  | 6, _ => rfl
  | _ + 7, h => omega

theorem l3_3_6_5 : lvl3 3 6 5 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_3_6_5_0]; rfl
  | 1, _ => rw [l4_3_6_5_1]; rfl
  | 2, _ => rw [l4_3_6_5_2]; rfl
  | 3, _ => rfl
  | 4, _ => rw [l4_3_6_5_4]; rfl
  | 5, _ => rfl
  | 6, _ => rfl
  | _ + 7, h => omega

theorem l3_4_0_0 : lvl3 4 0 0 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_4_0_0_0]; rfl
  | 1, _ => rw [l4_4_0_0_1]; rfl
  | 2, _ => rw [l4_4_0_0_2]; rfl
  | 3, _ => rw [l4_4_0_0_3]; rfl
  | 4, _ => rfl
  | 5, _ => rw [l4_4_0_0_5]; rfl
  | 6, _ => rw [l4_4_0_0_6]; rfl
  | _ + 7, h => omega

theorem l3_4_0_1 : lvl3 4 0 1 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_4_0_1_0]; rfl
  | 1, _ => rfl
  | 2, _ => rw [l4_4_0_1_2]; rfl
  | 3, _ => rw [l4_4_0_1_3]; rfl
  | 4, _ => rfl
  | 5, _ => rw [l4_4_0_1_5]; rfl
  | 6, _ => rw [l4_4_0_1_6]; rfl
  | _ + 7, h => omega

theorem l3_4_0_2 : lvl3 4 0 2 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_4_0_2_0]; rfl
  | 1, _ => rw [l4_4_0_2_1]; rfl
  | 2, _ => rfl
  | 3, _ => rw [l4_4_0_2_3]; rfl
  | 4, _ => rfl
  | 5, _ => rw [l4_4_0_2_5]; rfl
  | 6, _ => rw [l4_4_0_2_6]; rfl
  | _ + 7, h => omega

theorem l3_4_0_3 : lvl3 4 0 3 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_4_0_3_0]; rfl
  | 1, _ => rw [l4_4_0_3_1]; rfl
  | 2, _ => rw [l4_4_0_3_2]; rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rw [l4_4_0_3_5]; rfl
  | 6, _ => rw [l4_4_0_3_6]; rfl
  | _ + 7, h => omega

theorem l3_4_0_5 : lvl3 4 0 5 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_4_0_5_0]; rfl
  | 1, _ => rw [l4_4_0_5_1]; rfl
  | 2, _ => rw [l4_4_0_5_2]; rfl
  | 3, _ => rw [l4_4_0_5_3]; rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | 6, _ => rw [l4_4_0_5_6]; rfl
  | _ + 7, h => omega

theorem l3_4_0_6 : lvl3 4 0 6 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_4_0_6_0]; rfl
  | 1, _ => rw [l4_4_0_6_1]; rfl
  | 2, _ => rw [l4_4_0_6_2]; rfl
  | 3, _ => rw [l4_4_0_6_3]; rfl
  | 4, _ => rfl
  | 5, _ => rw [l4_4_0_6_5]; rfl
  | 6, _ => rfl
  | _ + 7, h => omega

theorem l3_4_1_0 : lvl3 4 1 0 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_4_1_0_0]; rfl
  | 1, _ => rfl
  | 2, _ => rw [l4_4_1_0_2]; rfl
  | 3, _ => rw [l4_4_1_0_3]; rfl
  | 4, _ => rfl
  | 5, _ => rw [l4_4_1_0_5]; rfl
  | 6, _ => rw [l4_4_1_0_6]; rfl
  | _ + 7, h => omega

theorem l3_4_1_2 : lvl3 4 1 2 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_4_1_2_0]; rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rw [l4_4_1_2_3]; rfl
  | 4, _ => rfl
  | 5, _ => rw [l4_4_1_2_5]; rfl
  | 6, _ => rw [l4_4_1_2_6]; rfl
  | _ + 7, h => omega

theorem l3_4_1_3 : lvl3 4 1 3 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_4_1_3_0]; rfl
  | 1, _ => rfl
  | 2, _ => rw [l4_4_1_3_2]; rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rw [l4_4_1_3_5]; rfl
  | 6, _ => rw [l4_4_1_3_6]; rfl
  | _ + 7, h => omega

theorem l3_4_1_5 : lvl3 4 1 5 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_4_1_5_0]; rfl
  | 1, _ => rfl
  | 2, _ => rw [l4_4_1_5_2]; rfl
  | 3, _ => rw [l4_4_1_5_3]; rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | 6, _ => rw [l4_4_1_5_6]; rfl
  | _ + 7, h => omega

theorem l3_4_1_6 : lvl3 4 1 6 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_4_1_6_0]; rfl
  | 1, _ => rfl
  | 2, _ => rw [l4_4_1_6_2]; rfl
  | 3, _ => rw [l4_4_1_6_3]; rfl
  | 4, _ => rfl
  | 5, _ => rw [l4_4_1_6_5]; rfl
  | 6, _ => rfl
  | _ + 7, h => omega

theorem l3_4_2_0 : lvl3 4 2 0 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_4_2_0_0]; rfl
  | 1, _ => rw [l4_4_2_0_1]; rfl
  | 2, _ => rfl
  | 3, _ => rw [l4_4_2_0_3]; rfl
  | 4, _ => rfl
  | 5, _ => rw [l4_4_2_0_5]; rfl
  | 6, _ => rw [l4_4_2_0_6]; rfl
  | _ + 7, h => omega

theorem l3_4_2_1 : lvl3 4 2 1 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_4_2_1_0]; rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rw [l4_4_2_1_3]; rfl
  | 4, _ => rfl
  | 5, _ => rw [l4_4_2_1_5]; rfl
  | 6, _ => rw [l4_4_2_1_6]; rfl
  | _ + 7, h => omega

theorem l3_4_2_3 : lvl3 4 2 3 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_4_2_3_0]; rfl
  | 1, _ => rw [l4_4_2_3_1]; rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rw [l4_4_2_3_5]; rfl
  | 6, _ => rw [l4_4_2_3_6]; rfl
  | _ + 7, h => omega

theorem l3_4_2_5 : lvl3 4 2 5 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_4_2_5_0]; rfl
  | 1, _ => rw [l4_4_2_5_1]; rfl
  | 2, _ => rfl
  | 3, _ => rw [l4_4_2_5_3]; rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | 6, _ => rw [l4_4_2_5_6]; rfl
  | _ + 7, h => omega

theorem l3_4_2_6 : lvl3 4 2 6 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_4_2_6_0]; rfl
  | 1, _ => rw [l4_4_2_6_1]; rfl
  | 2, _ => rfl
  | 3, _ => rw [l4_4_2_6_3]; rfl
  | 4, _ => rfl
  | 5, _ => rw [l4_4_2_6_5]; rfl
  | 6, _ => rfl
  | _ + 7, h => omega

theorem l3_4_3_0 : lvl3 4 3 0 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_4_3_0_0]; rfl
  | 1, _ => rw [l4_4_3_0_1]; rfl
  | 2, _ => rw [l4_4_3_0_2]; rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rw [l4_4_3_0_5]; rfl
  | 6, _ => rw [l4_4_3_0_6]; rfl
  | _ + 7, h => omega

theorem l3_4_3_1 : lvl3 4 3 1 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_4_3_1_0]; rfl
  | 1, _ => rfl
  | 2, _ => rw [l4_4_3_1_2]; rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rw [l4_4_3_1_5]; rfl
  | 6, _ => rw [l4_4_3_1_6]; rfl
  | _ + 7, h => omega

theorem l3_4_3_2 : lvl3 4 3 2 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_4_3_2_0]; rfl
  | 1, _ => rw [l4_4_3_2_1]; rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rw [l4_4_3_2_5]; rfl
  | 6, _ => rw [l4_4_3_2_6]; rfl
  | _ + 7, h => omega

theorem l3_4_3_5 : lvl3 4 3 5 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_4_3_5_0]; rfl
  | 1, _ => rw [l4_4_3_5_1]; rfl
  | 2, _ => rw [l4_4_3_5_2]; rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | 6, _ => rw [l4_4_3_5_6]; rfl
  | _ + 7, h => omega

theorem l3_4_3_6 : lvl3 4 3 6 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_4_3_6_0]; rfl
  | 1, _ => rw [l4_4_3_6_1]; rfl
  | 2, _ => rw [l4_4_3_6_2]; rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rw [l4_4_3_6_5]; rfl
  | 6, _ => rfl
  | _ + 7, h => omega

theorem l3_4_5_0 : lvl3 4 5 0 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_4_5_0_0]; rfl
  | 1, _ => rw [l4_4_5_0_1]; rfl
  | 2, _ => rw [l4_4_5_0_2]; rfl
  | 3, _ => rw [l4_4_5_0_3]; rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | 6, _ => rw [l4_4_5_0_6]; rfl
  | _ + 7, h => omega

theorem l3_4_5_1 : lvl3 4 5 1 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_4_5_1_0]; rfl
  | 1, _ => rfl
  | 2, _ => rw [l4_4_5_1_2]; rfl
  | 3, _ => rw [l4_4_5_1_3]; rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | 6, _ => rw [l4_4_5_1_6]; rfl
  | _ + 7, h => omega

theorem l3_4_5_2 : lvl3 4 5 2 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_4_5_2_0]; rfl
  | 1, _ => rw [l4_4_5_2_1]; rfl
  | 2, _ => rfl
  | 3, _ => rw [l4_4_5_2_3]; rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | 6, _ => rw [l4_4_5_2_6]; rfl
  | _ + 7, h => omega

theorem l3_4_5_3 : lvl3 4 5 3 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_4_5_3_0]; rfl
  | 1, _ => rw [l4_4_5_3_1]; rfl
  | 2, _ => rw [l4_4_5_3_2]; rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | 6, _ => rw [l4_4_5_3_6]; rfl
  | _ + 7, h => omega

theorem l3_4_5_6 : lvl3 4 5 6 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_4_5_6_0]; rfl
  | 1, _ => rw [l4_4_5_6_1]; rfl
  | 2, _ => rw [l4_4_5_6_2]; rfl
  | 3, _ => rw [l4_4_5_6_3]; rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | 6, _ => rfl
  | _ + 7, h => omega

theorem l3_4_6_0 : lvl3 4 6 0 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_4_6_0_0]; rfl
  | 1, _ => rw [l4_4_6_0_1]; rfl
  | 2, _ => rw [l4_4_6_0_2]; rfl
  | 3, _ => rw [l4_4_6_0_3]; rfl
  | 4, _ => rfl
  | 5, _ => rw [l4_4_6_0_5]; rfl
  | 6, _ => rfl
  | _ + 7, h => omega

theorem l3_4_6_1 : lvl3 4 6 1 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_4_6_1_0]; rfl
  | 1, _ => rfl
  | 2, _ => rw [l4_4_6_1_2]; rfl
  | 3, _ => rw [l4_4_6_1_3]; rfl
  | 4, _ => rfl
  | 5, _ => rw [l4_4_6_1_5]; rfl
  | 6, _ => rfl
  | _ + 7, h => omega

theorem l3_4_6_2 : lvl3 4 6 2 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_4_6_2_0]; rfl
  | 1, _ => rw [l4_4_6_2_1]; rfl
  | 2, _ => rfl
  | 3, _ => rw [l4_4_6_2_3]; rfl
  | 4, _ => rfl
  | 5, _ => rw [l4_4_6_2_5]; rfl
  | 6, _ => rfl
  | _ + 7, h => omega

theorem l3_4_6_3 : lvl3 4 6 3 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_4_6_3_0]; rfl
  | 1, _ => rw [l4_4_6_3_1]; rfl
  | 2, _ => rw [l4_4_6_3_2]; rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rw [l4_4_6_3_5]; rfl
  | 6, _ => rfl
  | _ + 7, h => omega

theorem l3_4_6_5 : lvl3 4 6 5 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_4_6_5_0]; rfl
  | 1, _ => rw [l4_4_6_5_1]; rfl
  | 2, _ => rw [l4_4_6_5_2]; rfl
  | 3, _ => rw [l4_4_6_5_3]; rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | 6, _ => rfl
  | _ + 7, h => omega

theorem l3_5_0_0 : lvl3 5 0 0 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_5_0_0_0]; rfl
  | 1, _ => rw [l4_5_0_0_1]; rfl
  | 2, _ => rw [l4_5_0_0_2]; rfl
  | 3, _ => rw [l4_5_0_0_3]; rfl
  | 4, _ => rw [l4_5_0_0_4]; rfl
  | 5, _ => rfl
  | 6, _ => rw [l4_5_0_0_6]; rfl
  | _ + 7, h => omega

theorem l3_5_0_1 : lvl3 5 0 1 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_5_0_1_0]; rfl
  | 1, _ => rfl
  | 2, _ => rw [l4_5_0_1_2]; rfl
  | 3, _ => rw [l4_5_0_1_3]; rfl
  | 4, _ => rw [l4_5_0_1_4]; rfl
  | 5, _ => rfl
  | 6, _ => rw [l4_5_0_1_6]; rfl
  | _ + 7, h => omega

theorem l3_5_0_2 : lvl3 5 0 2 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_5_0_2_0]; rfl
  | 1, _ => rw [l4_5_0_2_1]; rfl
  | 2, _ => rfl
  | 3, _ => rw [l4_5_0_2_3]; rfl
  | 4, _ => rw [l4_5_0_2_4]; rfl
  | 5, _ => rfl
  | 6, _ => rw [l4_5_0_2_6]; rfl
  | _ + 7, h => omega

theorem l3_5_0_3 : lvl3 5 0 3 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_5_0_3_0]; rfl
  | 1, _ => rw [l4_5_0_3_1]; rfl
  | 2, _ => rw [l4_5_0_3_2]; rfl
  | 3, _ => rfl
  | 4, _ => rw [l4_5_0_3_4]; rfl
  | 5, _ => rfl
  | 6, _ => rw [l4_5_0_3_6]; rfl
  | _ + 7, h => omega

theorem l3_5_0_4 : lvl3 5 0 4 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_5_0_4_0]; rfl
  | 1, _ => rw [l4_5_0_4_1]; rfl
  | 2, _ => rw [l4_5_0_4_2]; rfl
  | 3, _ => rw [l4_5_0_4_3]; rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | 6, _ => rw [l4_5_0_4_6]; rfl
  | _ + 7, h => omega

theorem l3_5_0_6 : lvl3 5 0 6 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_5_0_6_0]; rfl
  | 1, _ => rw [l4_5_0_6_1]; rfl
  | 2, _ => rw [l4_5_0_6_2]; rfl
  | 3, _ => rw [l4_5_0_6_3]; rfl
  | 4, _ => rw [l4_5_0_6_4]; rfl
  | 5, _ => rfl
  | 6, _ => rfl
  | _ + 7, h => omega

theorem l3_5_1_0 : lvl3 5 1 0 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_5_1_0_0]; rfl
  | 1, _ => rfl
  | 2, _ => rw [l4_5_1_0_2]; rfl
  | 3, _ => rw [l4_5_1_0_3]; rfl
  | 4, _ => rw [l4_5_1_0_4]; rfl
  | 5, _ => rfl
  | 6, _ => rw [l4_5_1_0_6]; rfl
  | _ + 7, h => omega

theorem l3_5_1_2 : lvl3 5 1 2 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_5_1_2_0]; rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rw [l4_5_1_2_3]; rfl
  | 4, _ => rw [l4_5_1_2_4]; rfl
  | 5, _ => rfl
  | 6, _ => rw [l4_5_1_2_6]; rfl
  | _ + 7, h => omega

theorem l3_5_1_3 : lvl3 5 1 3 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_5_1_3_0]; rfl
  | 1, _ => rfl
  | 2, _ => rw [l4_5_1_3_2]; rfl
  | 3, _ => rfl
  | 4, _ => rw [l4_5_1_3_4]; rfl
  | 5, _ => rfl
  | 6, _ => rw [l4_5_1_3_6]; rfl
  | _ + 7, h => omega

theorem l3_5_1_4 : lvl3 5 1 4 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_5_1_4_0]; rfl
  | 1, _ => rfl
  | 2, _ => rw [l4_5_1_4_2]; rfl
  | 3, _ => rw [l4_5_1_4_3]; rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | 6, _ => rw [l4_5_1_4_6]; rfl
  | _ + 7, h => omega

theorem l3_5_1_6 : lvl3 5 1 6 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_5_1_6_0]; rfl
  | 1, _ => rfl
  | 2, _ => rw [l4_5_1_6_2]; rfl
  | 3, _ => rw [l4_5_1_6_3]; rfl
  | 4, _ => rw [l4_5_1_6_4]; rfl
  | 5, _ => rfl
  | 6, _ => rfl
  | _ + 7, h => omega

theorem l3_5_2_0 : lvl3 5 2 0 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_5_2_0_0]; rfl
  | 1, _ => rw [l4_5_2_0_1]; rfl
  | 2, _ => rfl
  | 3, _ => rw [l4_5_2_0_3]; rfl
  | 4, _ => rw [l4_5_2_0_4]; rfl
  | 5, _ => rfl
  | 6, _ => rw [l4_5_2_0_6]; rfl
  | _ + 7, h => omega

theorem l3_5_2_1 : lvl3 5 2 1 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_5_2_1_0]; rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rw [l4_5_2_1_3]; rfl
  | 4, _ => rw [l4_5_2_1_4]; rfl
  | 5, _ => rfl
  | 6, _ => rw [l4_5_2_1_6]; rfl
  | _ + 7, h => omega

theorem l3_5_2_3 : lvl3 5 2 3 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_5_2_3_0]; rfl
  | 1, _ => rw [l4_5_2_3_1]; rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rw [l4_5_2_3_4]; rfl
  | 5, _ => rfl
  | 6, _ => rw [l4_5_2_3_6]; rfl
  | _ + 7, h => omega

theorem l3_5_2_4 : lvl3 5 2 4 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_5_2_4_0]; rfl
  | 1, _ => rw [l4_5_2_4_1]; rfl
  | 2, _ => rfl
  | 3, _ => rw [l4_5_2_4_3]; rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | 6, _ => rw [l4_5_2_4_6]; rfl
  | _ + 7, h => omega

theorem l3_5_2_6 : lvl3 5 2 6 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_5_2_6_0]; rfl
  | 1, _ => rw [l4_5_2_6_1]; rfl
  | 2, _ => rfl
  | 3, _ => rw [l4_5_2_6_3]; rfl
  | 4, _ => rw [l4_5_2_6_4]; rfl
  | 5, _ => rfl
  | 6, _ => rfl
  | _ + 7, h => omega

theorem l3_5_3_0 : lvl3 5 3 0 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_5_3_0_0]; rfl
  | 1, _ => rw [l4_5_3_0_1]; rfl
  | 2, _ => rw [l4_5_3_0_2]; rfl
  | 3, _ => rfl
  | 4, _ => rw [l4_5_3_0_4]; rfl
  | 5, _ => rfl
  | 6, _ => rw [l4_5_3_0_6]; rfl
  | _ + 7, h => omega

theorem l3_5_3_1 : lvl3 5 3 1 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_5_3_1_0]; rfl
  | 1, _ => rfl
  | 2, _ => rw [l4_5_3_1_2]; rfl
  | 3, _ => rfl
  | 4, _ => rw [l4_5_3_1_4]; rfl
  | 5, _ => rfl
  | 6, _ => rw [l4_5_3_1_6]; rfl
  | _ + 7, h => omega

theorem l3_5_3_2 : lvl3 5 3 2 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_5_3_2_0]; rfl
  | 1, _ => rw [l4_5_3_2_1]; rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rw [l4_5_3_2_4]; rfl
  | 5, _ => rfl
  | 6, _ => rw [l4_5_3_2_6]; rfl
  | _ + 7, h => omega

theorem l3_5_3_4 : lvl3 5 3 4 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_5_3_4_0]; rfl
  | 1, _ => rw [l4_5_3_4_1]; rfl
  | 2, _ => rw [l4_5_3_4_2]; rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | 6, _ => rw [l4_5_3_4_6]; rfl
  | _ + 7, h => omega

theorem l3_5_3_6 : lvl3 5 3 6 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_5_3_6_0]; rfl
  | 1, _ => rw [l4_5_3_6_1]; rfl
  | 2, _ => rw [l4_5_3_6_2]; rfl
  | 3, _ => rfl
  | 4, _ => rw [l4_5_3_6_4]; rfl
  | 5, _ => rfl
  | 6, _ => rfl
  | _ + 7, h => omega

theorem l3_5_4_0 : lvl3 5 4 0 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_5_4_0_0]; rfl
  | 1, _ => rw [l4_5_4_0_1]; rfl
  | 2, _ => rw [l4_5_4_0_2]; rfl
  | 3, _ => rw [l4_5_4_0_3]; rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | 6, _ => rw [l4_5_4_0_6]; rfl
  | _ + 7, h => omega

theorem l3_5_4_1 : lvl3 5 4 1 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_5_4_1_0]; rfl
  | 1, _ => rfl
  | 2, _ => rw [l4_5_4_1_2]; rfl
  | 3, _ => rw [l4_5_4_1_3]; rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | 6, _ => rw [l4_5_4_1_6]; rfl
  | _ + 7, h => omega

theorem l3_5_4_2 : lvl3 5 4 2 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_5_4_2_0]; rfl
  | 1, _ => rw [l4_5_4_2_1]; rfl
  | 2, _ => rfl
  | 3, _ => rw [l4_5_4_2_3]; rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | 6, _ => rw [l4_5_4_2_6]; rfl
  | _ + 7, h => omega

theorem l3_5_4_3 : lvl3 5 4 3 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_5_4_3_0]; rfl
  | 1, _ => rw [l4_5_4_3_1]; rfl
  | 2, _ => rw [l4_5_4_3_2]; rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | 6, _ => rw [l4_5_4_3_6]; rfl
  | _ + 7, h => omega

theorem l3_5_4_6 : lvl3 5 4 6 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_5_4_6_0]; rfl
  | 1, _ => rw [l4_5_4_6_1]; rfl
  | 2, _ => rw [l4_5_4_6_2]; rfl
  | 3, _ => rw [l4_5_4_6_3]; rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | 6, _ => rfl
  | _ + 7, h => omega

theorem l3_5_6_0 : lvl3 5 6 0 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_5_6_0_0]; rfl
  | 1, _ => rw [l4_5_6_0_1]; rfl
  | 2, _ => rw [l4_5_6_0_2]; rfl
  | 3, _ => rw [l4_5_6_0_3]; rfl
  | 4, _ => rw [l4_5_6_0_4]; rfl
  | 5, _ => rfl
  | 6, _ => rfl
  | _ + 7, h => omega

theorem l3_5_6_1 : lvl3 5 6 1 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_5_6_1_0]; rfl
  | 1, _ => rfl
  | 2, _ => rw [l4_5_6_1_2]; rfl
  | 3, _ => rw [l4_5_6_1_3]; rfl
  | 4, _ => rw [l4_5_6_1_4]; rfl
  | 5, _ => rfl
  | 6, _ => rfl
  | _ + 7, h => omega

theorem l3_5_6_2 : lvl3 5 6 2 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_5_6_2_0]; rfl
  | 1, _ => rw [l4_5_6_2_1]; rfl
  | 2, _ => rfl
  | 3, _ => rw [l4_5_6_2_3]; rfl
  | 4, _ => rw [l4_5_6_2_4]; rfl
  | 5, _ => rfl
  | 6, _ => rfl
  | _ + 7, h => omega

theorem l3_5_6_3 : lvl3 5 6 3 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_5_6_3_0]; rfl
  | 1, _ => rw [l4_5_6_3_1]; rfl
  | 2, _ => rw [l4_5_6_3_2]; rfl
  | 3, _ => rfl
  | 4, _ => rw [l4_5_6_3_4]; rfl
  | 5, _ => rfl
  | 6, _ => rfl
  | _ + 7, h => omega

theorem l3_5_6_4 : lvl3 5 6 4 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_5_6_4_0]; rfl
  | 1, _ => rw [l4_5_6_4_1]; rfl
  | 2, _ => rw [l4_5_6_4_2]; rfl
  | 3, _ => rw [l4_5_6_4_3]; rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | 6, _ => rfl
  | _ + 7, h => omega

theorem l3_6_0_0 : lvl3 6 0 0 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_6_0_0_0]; rfl
  | 1, _ => rw [l4_6_0_0_1]; rfl
  | 2, _ => rw [l4_6_0_0_2]; rfl
  | 3, _ => rw [l4_6_0_0_3]; rfl
  | 4, _ => rw [l4_6_0_0_4]; rfl
  | 5, _ => rw [l4_6_0_0_5]; rfl
  | 6, _ => rfl
  | _ + 7, h => omega

theorem l3_6_0_1 : lvl3 6 0 1 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_6_0_1_0]; rfl
  | 1, _ => rfl
  | 2, _ => rw [l4_6_0_1_2]; rfl
  | 3, _ => rw [l4_6_0_1_3]; rfl
  | 4, _ => rw [l4_6_0_1_4]; rfl
  | 5, _ => rw [l4_6_0_1_5]; rfl
  | 6, _ => rfl
  | _ + 7, h => omega

theorem l3_6_0_2 : lvl3 6 0 2 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_6_0_2_0]; rfl
  | 1, _ => rw [l4_6_0_2_1]; rfl
  | 2, _ => rfl
  | 3, _ => rw [l4_6_0_2_3]; rfl
  | 4, _ => rw [l4_6_0_2_4]; rfl
  | 5, _ => rw [l4_6_0_2_5]; rfl
  | 6, _ => rfl
  | _ + 7, h => omega

theorem l3_6_0_3 : lvl3 6 0 3 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_6_0_3_0]; rfl
  | 1, _ => rw [l4_6_0_3_1]; rfl
  | 2, _ => rw [l4_6_0_3_2]; rfl
  | 3, _ => rfl
  | 4, _ => rw [l4_6_0_3_4]; rfl
  | 5, _ => rw [l4_6_0_3_5]; rfl
  | 6, _ => rfl
  | _ + 7, h => omega

theorem l3_6_0_4 : lvl3 6 0 4 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_6_0_4_0]; rfl
  | 1, _ => rw [l4_6_0_4_1]; rfl
  | 2, _ => rw [l4_6_0_4_2]; rfl
  | 3, _ => rw [l4_6_0_4_3]; rfl
  | 4, _ => rfl
  | 5, _ => rw [l4_6_0_4_5]; rfl
  | 6, _ => rfl
  | _ + 7, h => omega

theorem l3_6_0_5 : lvl3 6 0 5 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_6_0_5_0]; rfl
  | 1, _ => rw [l4_6_0_5_1]; rfl
  | 2, _ => rw [l4_6_0_5_2]; rfl
  | 3, _ => rw [l4_6_0_5_3]; rfl
  | 4, _ => rw [l4_6_0_5_4]; rfl
  | 5, _ => rfl
  | 6, _ => rfl
  | _ + 7, h => omega

theorem l3_6_1_0 : lvl3 6 1 0 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_6_1_0_0]; rfl
  | 1, _ => rfl
  | 2, _ => rw [l4_6_1_0_2]; rfl
  | 3, _ => rw [l4_6_1_0_3]; rfl
  | 4, _ => rw [l4_6_1_0_4]; rfl
  | 5, _ => rw [l4_6_1_0_5]; rfl
  | 6, _ => rfl
  | _ + 7, h => omega

theorem l3_6_1_2 : lvl3 6 1 2 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_6_1_2_0]; rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rw [l4_6_1_2_3]; rfl
  | 4, _ => rw [l4_6_1_2_4]; rfl
  | 5, _ => rw [l4_6_1_2_5]; rfl
  | 6, _ => rfl
  | _ + 7, h => omega

theorem l3_6_1_3 : lvl3 6 1 3 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_6_1_3_0]; rfl
  | 1, _ => rfl
  | 2, _ => rw [l4_6_1_3_2]; rfl
  | 3, _ => rfl
  | 4, _ => rw [l4_6_1_3_4]; rfl
  | 5, _ => rw [l4_6_1_3_5]; rfl
  | 6, _ => rfl
  | _ + 7, h => omega

theorem l3_6_1_4 : lvl3 6 1 4 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_6_1_4_0]; rfl
  | 1, _ => rfl
  | 2, _ => rw [l4_6_1_4_2]; rfl
  | 3, _ => rw [l4_6_1_4_3]; rfl
  | 4, _ => rfl
  | 5, _ => rw [l4_6_1_4_5]; rfl
  | 6, _ => rfl
  | _ + 7, h => omega

theorem l3_6_1_5 : lvl3 6 1 5 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_6_1_5_0]; rfl
  | 1, _ => rfl
  | 2, _ => rw [l4_6_1_5_2]; rfl
  | 3, _ => rw [l4_6_1_5_3]; rfl
  | 4, _ => rw [l4_6_1_5_4]; rfl
  | 5, _ => rfl
  | 6, _ => rfl
  | _ + 7, h => omega

theorem l3_6_2_0 : lvl3 6 2 0 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_6_2_0_0]; rfl
  | 1, _ => rw [l4_6_2_0_1]; rfl
  | 2, _ => rfl
  | 3, _ => rw [l4_6_2_0_3]; rfl
  | 4, _ => rw [l4_6_2_0_4]; rfl
  | 5, _ => rw [l4_6_2_0_5]; rfl
  | 6, _ => rfl
  | _ + 7, h => omega

theorem l3_6_2_1 : lvl3 6 2 1 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_6_2_1_0]; rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rw [l4_6_2_1_3]; rfl
  | 4, _ => rw [l4_6_2_1_4]; rfl
  | 5, _ => rw [l4_6_2_1_5]; rfl
  | 6, _ => rfl
  | _ + 7, h => omega

theorem l3_6_2_3 : lvl3 6 2 3 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_6_2_3_0]; rfl
  | 1, _ => rw [l4_6_2_3_1]; rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rw [l4_6_2_3_4]; rfl
  | 5, _ => rw [l4_6_2_3_5]; rfl
  | 6, _ => rfl
  | _ + 7, h => omega

theorem l3_6_2_4 : lvl3 6 2 4 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_6_2_4_0]; rfl
  | 1, _ => rw [l4_6_2_4_1]; rfl
  | 2, _ => rfl
  | 3, _ => rw [l4_6_2_4_3]; rfl
  | 4, _ => rfl
  | 5, _ => rw [l4_6_2_4_5]; rfl
  | 6, _ => rfl
  | _ + 7, h => omega

theorem l3_6_2_5 : lvl3 6 2 5 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_6_2_5_0]; rfl
  | 1, _ => rw [l4_6_2_5_1]; rfl
  | 2, _ => rfl
  | 3, _ => rw [l4_6_2_5_3]; rfl
  | 4, _ => rw [l4_6_2_5_4]; rfl
  | 5, _ => rfl
  | 6, _ => rfl
  | _ + 7, h => omega

theorem l3_6_3_0 : lvl3 6 3 0 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_6_3_0_0]; rfl
  | 1, _ => rw [l4_6_3_0_1]; rfl
  | 2, _ => rw [l4_6_3_0_2]; rfl
  | 3, _ => rfl
  | 4, _ => rw [l4_6_3_0_4]; rfl
  | 5, _ => rw [l4_6_3_0_5]; rfl
  | 6, _ => rfl
  | _ + 7, h => omega

theorem l3_6_3_1 : lvl3 6 3 1 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_6_3_1_0]; rfl
  | 1, _ => rfl
  | 2, _ => rw [l4_6_3_1_2]; rfl
  | 3, _ => rfl
  | 4, _ => rw [l4_6_3_1_4]; rfl
  | 5, _ => rw [l4_6_3_1_5]; rfl
  | 6, _ => rfl
  | _ + 7, h => omega

theorem l3_6_3_2 : lvl3 6 3 2 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_6_3_2_0]; rfl
  | 1, _ => rw [l4_6_3_2_1]; rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rw [l4_6_3_2_4]; rfl
  | 5, _ => rw [l4_6_3_2_5]; rfl
  | 6, _ => rfl
  | _ + 7, h => omega

theorem l3_6_3_4 : lvl3 6 3 4 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_6_3_4_0]; rfl
  | 1, _ => rw [l4_6_3_4_1]; rfl
  | 2, _ => rw [l4_6_3_4_2]; rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rw [l4_6_3_4_5]; rfl
  | 6, _ => rfl
  | _ + 7, h => omega

theorem l3_6_3_5 : lvl3 6 3 5 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_6_3_5_0]; rfl
  | 1, _ => rw [l4_6_3_5_1]; rfl
  | 2, _ => rw [l4_6_3_5_2]; rfl
  | 3, _ => rfl
  | 4, _ => rw [l4_6_3_5_4]; rfl
  | 5, _ => rfl
  | 6, _ => rfl
  | _ + 7, h => omega

theorem l3_6_4_0 : lvl3 6 4 0 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_6_4_0_0]; rfl
  | 1, _ => rw [l4_6_4_0_1]; rfl
  | 2, _ => rw [l4_6_4_0_2]; rfl
  | 3, _ => rw [l4_6_4_0_3]; rfl
  | 4, _ => rfl
  | 5, _ => rw [l4_6_4_0_5]; rfl
  | 6, _ => rfl
  | _ + 7, h => omega

theorem l3_6_4_1 : lvl3 6 4 1 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_6_4_1_0]; rfl
  | 1, _ => rfl
  | 2, _ => rw [l4_6_4_1_2]; rfl
  | 3, _ => rw [l4_6_4_1_3]; rfl
  | 4, _ => rfl
  | 5, _ => rw [l4_6_4_1_5]; rfl
  | 6, _ => rfl
  | _ + 7, h => omega

theorem l3_6_4_2 : lvl3 6 4 2 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_6_4_2_0]; rfl
  | 1, _ => rw [l4_6_4_2_1]; rfl
  | 2, _ => rfl
  | 3, _ => rw [l4_6_4_2_3]; rfl
  | 4, _ => rfl
  | 5, _ => rw [l4_6_4_2_5]; rfl
  | 6, _ => rfl
  | _ + 7, h => omega

theorem l3_6_4_3 : lvl3 6 4 3 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_6_4_3_0]; rfl
  | 1, _ => rw [l4_6_4_3_1]; rfl
  | 2, _ => rw [l4_6_4_3_2]; rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rw [l4_6_4_3_5]; rfl
  | 6, _ => rfl
  | _ + 7, h => omega

theorem l3_6_4_5 : lvl3 6 4 5 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_6_4_5_0]; rfl
  | 1, _ => rw [l4_6_4_5_1]; rfl
  | 2, _ => rw [l4_6_4_5_2]; rfl
  | 3, _ => rw [l4_6_4_5_3]; rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | 6, _ => rfl
  | _ + 7, h => omega

theorem l3_6_5_0 : lvl3 6 5 0 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_6_5_0_0]; rfl
  | 1, _ => rw [l4_6_5_0_1]; rfl
  | 2, _ => rw [l4_6_5_0_2]; rfl
  | 3, _ => rw [l4_6_5_0_3]; rfl
  | 4, _ => rw [l4_6_5_0_4]; rfl
  | 5, _ => rfl
  | 6, _ => rfl
  | _ + 7, h => omega

theorem l3_6_5_1 : lvl3 6 5 1 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_6_5_1_0]; rfl
  | 1, _ => rfl
  | 2, _ => rw [l4_6_5_1_2]; rfl
  | 3, _ => rw [l4_6_5_1_3]; rfl
  | 4, _ => rw [l4_6_5_1_4]; rfl
  | 5, _ => rfl
  | 6, _ => rfl
  | _ + 7, h => omega

theorem l3_6_5_2 : lvl3 6 5 2 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_6_5_2_0]; rfl
  | 1, _ => rw [l4_6_5_2_1]; rfl
  | 2, _ => rfl
  | 3, _ => rw [l4_6_5_2_3]; rfl
  | 4, _ => rw [l4_6_5_2_4]; rfl
  | 5, _ => rfl
  | 6, _ => rfl
  | _ + 7, h => omega

theorem l3_6_5_3 : lvl3 6 5 3 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_6_5_3_0]; rfl
  | 1, _ => rw [l4_6_5_3_1]; rfl
  | 2, _ => rw [l4_6_5_3_2]; rfl
  | 3, _ => rfl
  | 4, _ => rw [l4_6_5_3_4]; rfl
  | 5, _ => rfl
  | 6, _ => rfl
  | _ + 7, h => omega

theorem l3_6_5_4 : lvl3 6 5 4 cov = true := by
  unfold lvl3
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l4_6_5_4_0]; rfl
  | 1, _ => rw [l4_6_5_4_1]; rfl
  | 2, _ => rw [l4_6_5_4_2]; rfl
  | 3, _ => rw [l4_6_5_4_3]; rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | 6, _ => rfl
  | _ + 7, h => omega

theorem l2_0_0 : lvl2 0 0 cov = true := by
  unfold lvl2
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l3_0_0_0]; rfl
  | 1, _ => rw [l3_0_0_1]; rfl
  | 2, _ => rw [l3_0_0_2]; rfl
  | 3, _ => rw [l3_0_0_3]; rfl
  | 4, _ => rw [l3_0_0_4]; rfl
  | 5, _ => rw [l3_0_0_5]; rfl
  | 6, _ => rw [l3_0_0_6]; rfl
  | _ + 7, h => omega

theorem l2_0_1 : lvl2 0 1 cov = true := by
  unfold lvl2
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l3_0_1_0]; rfl
  | 1, _ => rfl
  | 2, _ => rw [l3_0_1_2]; rfl
  | 3, _ => rw [l3_0_1_3]; rfl
  | 4, _ => rw [l3_0_1_4]; rfl
  | 5, _ => rw [l3_0_1_5]; rfl
  | 6, _ => rw [l3_0_1_6]; rfl
  | _ + 7, h => omega

theorem l2_0_2 : lvl2 0 2 cov = true := by
  unfold lvl2
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l3_0_2_0]; rfl
  | 1, _ => rw [l3_0_2_1]; rfl
  | 2, _ => rfl
  | 3, _ => rw [l3_0_2_3]; rfl
  | 4, _ => rw [l3_0_2_4]; rfl
  | 5, _ => rw [l3_0_2_5]; rfl
  | 6, _ => rw [l3_0_2_6]; rfl
  | _ + 7, h => omega

theorem l2_0_3 : lvl2 0 3 cov = true := by
  unfold lvl2
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l3_0_3_0]; rfl
  | 1, _ => rw [l3_0_3_1]; rfl
  | 2, _ => rw [l3_0_3_2]; rfl
  | 3, _ => rfl
  | 4, _ => rw [l3_0_3_4]; rfl
  | 5, _ => rw [l3_0_3_5]; rfl
  | 6, _ => rw [l3_0_3_6]; rfl
  | _ + 7, h => omega

theorem l2_0_4 : lvl2 0 4 cov = true := by
  unfold lvl2
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l3_0_4_0]; rfl
  | 1, _ => rw [l3_0_4_1]; rfl
  | 2, _ => rw [l3_0_4_2]; rfl
  | 3, _ => rw [l3_0_4_3]; rfl
  | 4, _ => rfl
  | 5, _ => rw [l3_0_4_5]; rfl
  | 6, _ => rw [l3_0_4_6]; rfl
  | _ + 7, h => omega

theorem l2_0_5 : lvl2 0 5 cov = true := by
  unfold lvl2
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l3_0_5_0]; rfl
  | 1, _ => rw [l3_0_5_1]; rfl
  | 2, _ => rw [l3_0_5_2]; rfl
  | 3, _ => rw [l3_0_5_3]; rfl
  | 4, _ => rw [l3_0_5_4]; rfl
  | 5, _ => rfl
  | 6, _ => rw [l3_0_5_6]; rfl
  | _ + 7, h => omega

theorem l2_0_6 : lvl2 0 6 cov = true := by
  unfold lvl2
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l3_0_6_0]; rfl
  | 1, _ => rw [l3_0_6_1]; rfl
  | 2, _ => rw [l3_0_6_2]; rfl
  | 3, _ => rw [l3_0_6_3]; rfl
  | 4, _ => rw [l3_0_6_4]; rfl
  | 5, _ => rw [l3_0_6_5]; rfl
  | 6, _ => rfl
  | _ + 7, h => omega

theorem l2_1_0 : lvl2 1 0 cov = true := by
  unfold lvl2
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l3_1_0_0]; rfl
  | 1, _ => rfl
  | 2, _ => rw [l3_1_0_2]; rfl
  | 3, _ => rw [l3_1_0_3]; rfl
  | 4, _ => rw [l3_1_0_4]; rfl
  | 5, _ => rw [l3_1_0_5]; rfl
  | 6, _ => rw [l3_1_0_6]; rfl
  | _ + 7, h => omega

theorem l2_1_2 : lvl2 1 2 cov = true := by
  unfold lvl2
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l3_1_2_0]; rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rw [l3_1_2_3]; rfl
  | 4, _ => rw [l3_1_2_4]; rfl
  | 5, _ => rw [l3_1_2_5]; rfl
  | 6, _ => rw [l3_1_2_6]; rfl
  | _ + 7, h => omega

theorem l2_1_3 : lvl2 1 3 cov = true := by
  unfold lvl2
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l3_1_3_0]; rfl
  | 1, _ => rfl
  | 2, _ => rw [l3_1_3_2]; rfl
  | 3, _ => rfl
  | 4, _ => rw [l3_1_3_4]; rfl
  | 5, _ => rw [l3_1_3_5]; rfl
  | 6, _ => rw [l3_1_3_6]; rfl
  | _ + 7, h => omega

theorem l2_1_4 : lvl2 1 4 cov = true := by
  unfold lvl2
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l3_1_4_0]; rfl
  | 1, _ => rfl
  | 2, _ => rw [l3_1_4_2]; rfl
  | 3, _ => rw [l3_1_4_3]; rfl
  | 4, _ => rfl
  | 5, _ => rw [l3_1_4_5]; rfl
  | 6, _ => rw [l3_1_4_6]; rfl
  | _ + 7, h => omega

theorem l2_1_5 : lvl2 1 5 cov = true := by
  unfold lvl2
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l3_1_5_0]; rfl
  | 1, _ => rfl
  | 2, _ => rw [l3_1_5_2]; rfl
  | 3, _ => rw [l3_1_5_3]; rfl
  | 4, _ => rw [l3_1_5_4]; rfl
  | 5, _ => rfl
  | 6, _ => rw [l3_1_5_6]; rfl
  | _ + 7, h => omega

theorem l2_1_6 : lvl2 1 6 cov = true := by
  unfold lvl2
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l3_1_6_0]; rfl
  | 1, _ => rfl
  | 2, _ => rw [l3_1_6_2]; rfl
  | 3, _ => rw [l3_1_6_3]; rfl
  | 4, _ => rw [l3_1_6_4]; rfl
  | 5, _ => rw [l3_1_6_5]; rfl
  | 6, _ => rfl
  | _ + 7, h => omega

theorem l2_2_0 : lvl2 2 0 cov = true := by
  unfold lvl2
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l3_2_0_0]; rfl
  | 1, _ => rw [l3_2_0_1]; rfl
  | 2, _ => rfl
  | 3, _ => rw [l3_2_0_3]; rfl
  | 4, _ => rw [l3_2_0_4]; rfl
  | 5, _ => rw [l3_2_0_5]; rfl
  | 6, _ => rw [l3_2_0_6]; rfl
  | _ + 7, h => omega

theorem l2_2_1 : lvl2 2 1 cov = true := by
  unfold lvl2
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l3_2_1_0]; rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rw [l3_2_1_3]; rfl
  | 4, _ => rw [l3_2_1_4]; rfl
  | 5, _ => rw [l3_2_1_5]; rfl
  | 6, _ => rw [l3_2_1_6]; rfl
  | _ + 7, h => omega

theorem l2_2_3 : lvl2 2 3 cov = true := by
  unfold lvl2
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l3_2_3_0]; rfl
  | 1, _ => rw [l3_2_3_1]; rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rw [l3_2_3_4]; rfl
  | 5, _ => rw [l3_2_3_5]; rfl
  | 6, _ => rw [l3_2_3_6]; rfl
  | _ + 7, h => omega

theorem l2_2_4 : lvl2 2 4 cov = true := by
  unfold lvl2
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l3_2_4_0]; rfl
  | 1, _ => rw [l3_2_4_1]; rfl
  | 2, _ => rfl
  | 3, _ => rw [l3_2_4_3]; rfl
  | 4, _ => rfl
  | 5, _ => rw [l3_2_4_5]; rfl
  | 6, _ => rw [l3_2_4_6]; rfl
  | _ + 7, h => omega

theorem l2_2_5 : lvl2 2 5 cov = true := by
  unfold lvl2
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l3_2_5_0]; rfl
  | 1, _ => rw [l3_2_5_1]; rfl
  | 2, _ => rfl
  | 3, _ => rw [l3_2_5_3]; rfl
  | 4, _ => rw [l3_2_5_4]; rfl
  | 5, _ => rfl
  | 6, _ => rw [l3_2_5_6]; rfl
  | _ + 7, h => omega

theorem l2_2_6 : lvl2 2 6 cov = true := by
  unfold lvl2
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l3_2_6_0]; rfl
  | 1, _ => rw [l3_2_6_1]; rfl
  | 2, _ => rfl
  | 3, _ => rw [l3_2_6_3]; rfl
  | 4, _ => rw [l3_2_6_4]; rfl
  | 5, _ => rw [l3_2_6_5]; rfl
  | 6, _ => rfl
  | _ + 7, h => omega

theorem l2_3_0 : lvl2 3 0 cov = true := by
  unfold lvl2
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l3_3_0_0]; rfl
  | 1, _ => rw [l3_3_0_1]; rfl
  | 2, _ => rw [l3_3_0_2]; rfl
  | 3, _ => rfl
  | 4, _ => rw [l3_3_0_4]; rfl
  | 5, _ => rw [l3_3_0_5]; rfl
  | 6, _ => rw [l3_3_0_6]; rfl
  | _ + 7, h => omega

theorem l2_3_1 : lvl2 3 1 cov = true := by
  unfold lvl2
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l3_3_1_0]; rfl
  | 1, _ => rfl
  | 2, _ => rw [l3_3_1_2]; rfl
  | 3, _ => rfl
  | 4, _ => rw [l3_3_1_4]; rfl
  | 5, _ => rw [l3_3_1_5]; rfl
  | 6, _ => rw [l3_3_1_6]; rfl
  | _ + 7, h => omega

theorem l2_3_2 : lvl2 3 2 cov = true := by
  unfold lvl2
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l3_3_2_0]; rfl
  | 1, _ => rw [l3_3_2_1]; rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rw [l3_3_2_4]; rfl
  | 5, _ => rw [l3_3_2_5]; rfl
  | 6, _ => rw [l3_3_2_6]; rfl
  | _ + 7, h => omega

theorem l2_3_4 : lvl2 3 4 cov = true := by
  unfold lvl2
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l3_3_4_0]; rfl
  | 1, _ => rw [l3_3_4_1]; rfl
  | 2, _ => rw [l3_3_4_2]; rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rw [l3_3_4_5]; rfl
  | 6, _ => rw [l3_3_4_6]; rfl
  | _ + 7, h => omega

theorem l2_3_5 : lvl2 3 5 cov = true := by
  unfold lvl2
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l3_3_5_0]; rfl
  | 1, _ => rw [l3_3_5_1]; rfl
  | 2, _ => rw [l3_3_5_2]; rfl
  | 3, _ => rfl
  | 4, _ => rw [l3_3_5_4]; rfl
  | 5, _ => rfl
  | 6, _ => rw [l3_3_5_6]; rfl
  | _ + 7, h => omega

theorem l2_3_6 : lvl2 3 6 cov = true := by
  unfold lvl2
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l3_3_6_0]; rfl
  | 1, _ => rw [l3_3_6_1]; rfl
  | 2, _ => rw [l3_3_6_2]; rfl
  | 3, _ => rfl
  | 4, _ => rw [l3_3_6_4]; rfl
  | 5, _ => rw [l3_3_6_5]; rfl
  | 6, _ => rfl
  | _ + 7, h => omega

theorem l2_4_0 : lvl2 4 0 cov = true := by
  unfold lvl2
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l3_4_0_0]; rfl
  | 1, _ => rw [l3_4_0_1]; rfl
  | 2, _ => rw [l3_4_0_2]; rfl
  | 3, _ => rw [l3_4_0_3]; rfl
  | 4, _ => rfl
  | 5, _ => rw [l3_4_0_5]; rfl
  | 6, _ => rw [l3_4_0_6]; rfl
  | _ + 7, h => omega

theorem l2_4_1 : lvl2 4 1 cov = true := by
  unfold lvl2
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l3_4_1_0]; rfl
  | 1, _ => rfl
  | 2, _ => rw [l3_4_1_2]; rfl
  | 3, _ => rw [l3_4_1_3]; rfl
  | 4, _ => rfl
  | 5, _ => rw [l3_4_1_5]; rfl
  | 6, _ => rw [l3_4_1_6]; rfl
  | _ + 7, h => omega

theorem l2_4_2 : lvl2 4 2 cov = true := by
  unfold lvl2
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l3_4_2_0]; rfl
  | 1, _ => rw [l3_4_2_1]; rfl
  | 2, _ => rfl
  | 3, _ => rw [l3_4_2_3]; rfl
  | 4, _ => rfl
  | 5, _ => rw [l3_4_2_5]; rfl
  | 6, _ => rw [l3_4_2_6]; rfl
  | _ + 7, h => omega

theorem l2_4_3 : lvl2 4 3 cov = true := by
  unfold lvl2
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l3_4_3_0]; rfl
  | 1, _ => rw [l3_4_3_1]; rfl
  | 2, _ => rw [l3_4_3_2]; rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rw [l3_4_3_5]; rfl
  | 6, _ => rw [l3_4_3_6]; rfl
  | _ + 7, h => omega

theorem l2_4_5 : lvl2 4 5 cov = true := by
  unfold lvl2
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l3_4_5_0]; rfl
  | 1, _ => rw [l3_4_5_1]; rfl
  | 2, _ => rw [l3_4_5_2]; rfl
  | 3, _ => rw [l3_4_5_3]; rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | 6, _ => rw [l3_4_5_6]; rfl
  | _ + 7, h => omega

theorem l2_4_6 : lvl2 4 6 cov = true := by
  unfold lvl2
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l3_4_6_0]; rfl
  | 1, _ => rw [l3_4_6_1]; rfl
  | 2, _ => rw [l3_4_6_2]; rfl
  | 3, _ => rw [l3_4_6_3]; rfl
  | 4, _ => rfl
  | 5, _ => rw [l3_4_6_5]; rfl
  | 6, _ => rfl
  | _ + 7, h => omega

theorem l2_5_0 : lvl2 5 0 cov = true := by
  unfold lvl2
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l3_5_0_0]; rfl
  | 1, _ => rw [l3_5_0_1]; rfl
  | 2, _ => rw [l3_5_0_2]; rfl
  | 3, _ => rw [l3_5_0_3]; rfl
  | 4, _ => rw [l3_5_0_4]; rfl
  | 5, _ => rfl
  | 6, _ => rw [l3_5_0_6]; rfl
  | _ + 7, h => omega

theorem l2_5_1 : lvl2 5 1 cov = true := by
  unfold lvl2
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l3_5_1_0]; rfl
  | 1, _ => rfl
  | 2, _ => rw [l3_5_1_2]; rfl
  | 3, _ => rw [l3_5_1_3]; rfl
  | 4, _ => rw [l3_5_1_4]; rfl
  | 5, _ => rfl
  | 6, _ => rw [l3_5_1_6]; rfl
  | _ + 7, h => omega

theorem l2_5_2 : lvl2 5 2 cov = true := by
  unfold lvl2
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l3_5_2_0]; rfl
  | 1, _ => rw [l3_5_2_1]; rfl
  | 2, _ => rfl
  | 3, _ => rw [l3_5_2_3]; rfl
  | 4, _ => rw [l3_5_2_4]; rfl
  | 5, _ => rfl
  | 6, _ => rw [l3_5_2_6]; rfl
  | _ + 7, h => omega

theorem l2_5_3 : lvl2 5 3 cov = true := by
  unfold lvl2
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l3_5_3_0]; rfl
  | 1, _ => rw [l3_5_3_1]; rfl
  | 2, _ => rw [l3_5_3_2]; rfl
  | 3, _ => rfl
  | 4, _ => rw [l3_5_3_4]; rfl
  | 5, _ => rfl
  | 6, _ => rw [l3_5_3_6]; rfl
  | _ + 7, h => omega

theorem l2_5_4 : lvl2 5 4 cov = true := by
  unfold lvl2
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l3_5_4_0]; rfl
  | 1, _ => rw [l3_5_4_1]; rfl
  | 2, _ => rw [l3_5_4_2]; rfl
  | 3, _ => rw [l3_5_4_3]; rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | 6, _ => rw [l3_5_4_6]; rfl
  | _ + 7, h => omega

theorem l2_5_6 : lvl2 5 6 cov = true := by
  unfold lvl2
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l3_5_6_0]; rfl
  | 1, _ => rw [l3_5_6_1]; rfl
  | 2, _ => rw [l3_5_6_2]; rfl
  | 3, _ => rw [l3_5_6_3]; rfl
  | 4, _ => rw [l3_5_6_4]; rfl
  | 5, _ => rfl
  | 6, _ => rfl
  | _ + 7, h => omega

theorem l2_6_0 : lvl2 6 0 cov = true := by
  unfold lvl2
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l3_6_0_0]; rfl
  | 1, _ => rw [l3_6_0_1]; rfl
  | 2, _ => rw [l3_6_0_2]; rfl
  | 3, _ => rw [l3_6_0_3]; rfl
  | 4, _ => rw [l3_6_0_4]; rfl
  | 5, _ => rw [l3_6_0_5]; rfl
  | 6, _ => rfl
  | _ + 7, h => omega

theorem l2_6_1 : lvl2 6 1 cov = true := by
  unfold lvl2
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l3_6_1_0]; rfl
  | 1, _ => rfl
  | 2, _ => rw [l3_6_1_2]; rfl
  | 3, _ => rw [l3_6_1_3]; rfl
  | 4, _ => rw [l3_6_1_4]; rfl
  | 5, _ => rw [l3_6_1_5]; rfl
  | 6, _ => rfl
  | _ + 7, h => omega

theorem l2_6_2 : lvl2 6 2 cov = true := by
  unfold lvl2
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l3_6_2_0]; rfl
  | 1, _ => rw [l3_6_2_1]; rfl
  | 2, _ => rfl
  | 3, _ => rw [l3_6_2_3]; rfl
  | 4, _ => rw [l3_6_2_4]; rfl
  | 5, _ => rw [l3_6_2_5]; rfl
  | 6, _ => rfl
  | _ + 7, h => omega

theorem l2_6_3 : lvl2 6 3 cov = true := by
  unfold lvl2
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l3_6_3_0]; rfl
  | 1, _ => rw [l3_6_3_1]; rfl
  | 2, _ => rw [l3_6_3_2]; rfl
  | 3, _ => rfl
  | 4, _ => rw [l3_6_3_4]; rfl
  | 5, _ => rw [l3_6_3_5]; rfl
  | 6, _ => rfl
  | _ + 7, h => omega

theorem l2_6_4 : lvl2 6 4 cov = true := by
  unfold lvl2
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l3_6_4_0]; rfl
  | 1, _ => rw [l3_6_4_1]; rfl
  | 2, _ => rw [l3_6_4_2]; rfl
  | 3, _ => rw [l3_6_4_3]; rfl
  | 4, _ => rfl
  | 5, _ => rw [l3_6_4_5]; rfl
  | 6, _ => rfl
  | _ + 7, h => omega

theorem l2_6_5 : lvl2 6 5 cov = true := by
  unfold lvl2
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l3_6_5_0]; rfl
  | 1, _ => rw [l3_6_5_1]; rfl
  | 2, _ => rw [l3_6_5_2]; rfl
  | 3, _ => rw [l3_6_5_3]; rfl
  | 4, _ => rw [l3_6_5_4]; rfl
  | 5, _ => rfl
  | 6, _ => rfl
  | _ + 7, h => omega

theorem l1_0 : lvl1 0 cov = true := by
  unfold lvl1
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l2_0_0]; rfl
  | 1, _ => rw [l2_0_1]; rfl
  | 2, _ => rw [l2_0_2]; rfl
  | 3, _ => rw [l2_0_3]; rfl
  | 4, _ => rw [l2_0_4]; rfl
  | 5, _ => rw [l2_0_5]; rfl
  | 6, _ => rw [l2_0_6]; rfl
  | _ + 7, h => omega

theorem l1_1 : lvl1 1 cov = true := by
  unfold lvl1
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l2_1_0]; rfl
  | 1, _ => rfl
  | 2, _ => rw [l2_1_2]; rfl
  | 3, _ => rw [l2_1_3]; rfl
  | 4, _ => rw [l2_1_4]; rfl
  | 5, _ => rw [l2_1_5]; rfl
  | 6, _ => rw [l2_1_6]; rfl
  | _ + 7, h => omega

theorem l1_2 : lvl1 2 cov = true := by
  unfold lvl1
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l2_2_0]; rfl
  | 1, _ => rw [l2_2_1]; rfl
  | 2, _ => rfl
  | 3, _ => rw [l2_2_3]; rfl
  | 4, _ => rw [l2_2_4]; rfl
  | 5, _ => rw [l2_2_5]; rfl
  | 6, _ => rw [l2_2_6]; rfl
  | _ + 7, h => omega

theorem l1_3 : lvl1 3 cov = true := by
  unfold lvl1
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l2_3_0]; rfl
  | 1, _ => rw [l2_3_1]; rfl
  | 2, _ => rw [l2_3_2]; rfl
  | 3, _ => rfl
  | 4, _ => rw [l2_3_4]; rfl
  | 5, _ => rw [l2_3_5]; rfl
  | 6, _ => rw [l2_3_6]; rfl
  | _ + 7, h => omega

theorem l1_4 : lvl1 4 cov = true := by
  unfold lvl1
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l2_4_0]; rfl
  | 1, _ => rw [l2_4_1]; rfl
  | 2, _ => rw [l2_4_2]; rfl
  | 3, _ => rw [l2_4_3]; rfl
  | 4, _ => rfl
  | 5, _ => rw [l2_4_5]; rfl
  | 6, _ => rw [l2_4_6]; rfl
  | _ + 7, h => omega

theorem l1_5 : lvl1 5 cov = true := by
  unfold lvl1
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l2_5_0]; rfl
  | 1, _ => rw [l2_5_1]; rfl
  | 2, _ => rw [l2_5_2]; rfl
  | 3, _ => rw [l2_5_3]; rfl
  | 4, _ => rw [l2_5_4]; rfl
  | 5, _ => rfl
  | 6, _ => rw [l2_5_6]; rfl
  | _ + 7, h => omega

theorem l1_6 : lvl1 6 cov = true := by
  unfold lvl1
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => rw [l2_6_0]; rfl
  | 1, _ => rw [l2_6_1]; rfl
  | 2, _ => rw [l2_6_2]; rfl
  | 3, _ => rw [l2_6_3]; rfl
  | 4, _ => rw [l2_6_4]; rfl
  | 5, _ => rw [l2_6_5]; rfl
  | 6, _ => rfl
  | _ + 7, h => omega

theorem lvl0_cov : lvl0 cov = true := by
  unfold lvl0
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  match c, hc with
  | 0, _ => exact l1_0
  | 1, _ => exact l1_1
  | 2, _ => exact l1_2
  | 3, _ => exact l1_3
  | 4, _ => exact l1_4
  | 5, _ => exact l1_5
  | 6, _ => exact l1_6
  | _ + 7, h => omega

end URTM.Three
