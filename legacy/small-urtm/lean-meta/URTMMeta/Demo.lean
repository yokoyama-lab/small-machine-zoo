/-
  空虚でないことの確認。

  主定理 `no_two_state_URTM` は「`TwoStateRTM` かつ `IsUTM`」を否定する。定義のどちらかが
  **どんな表でも成り立たない**なら主張は空虚になるので、具体例で次を示す:
    * `TwoStateRTM` は実際の可逆 2 状態表（本体の `haltTbl`・`escTbl`）で成り立つ。
    * `Simulates`（Def. 5.8）は 2 状態表で**実際に成り立つ**。止まる系（常に 0 を返す）を
      `haltTbl` が、止まらない系（どこでも未定義）を `escTbl` が模倣する。
  つまり 2 状態 RTM は「決定可能な系」なら模倣でき、万能になれないのは停止の決定可能性のため。
-/
import URTMMeta.NoURTM
import URTM.TSDDemo

namespace URTM.Meta
open URTM URTM.TwoState

theorem haltTbl_two : TwoStateRTM haltTbl 0 1 2 :=
  ⟨by decide, by decide, by decide, by decide, by decide,
    by intro r hr; simp [haltTbl] at hr; rcases hr with rfl | rfl <;> simp,
    by intro r hr; simp [haltTbl] at hr; rcases hr with rfl | rfl <;> simp⟩

theorem escTbl_two : TwoStateRTM escTbl 0 1 2 :=
  ⟨by decide, by decide, by decide, by decide, by decide,
    by intro r hr; simp [escTbl] at hr; rcases hr with rfl | rfl <;> simp,
    by intro r hr; simp [escTbl] at hr; rcases hr with rfl | rfl <;> simp⟩

/-- 止まる系（入力によらず 0 を返す）は 2 状態 RTM `haltTbl` で模倣できる。 -/
theorem sim_const : Simulates haltTbl (fun _ : ℕ => Part.some 0) := by
  refine ⟨fun _ => (0, [], []), fun _ => 0, Computable.const _, Computable.const _, ?_, ?_⟩
  · intro a v hv
    rw [Part.mem_some_iff] at hv
    exact ⟨(0, [], [1, 0]), ⟨2, rfl, rfl⟩, hv.symm⟩
  · intro a h; exact absurd trivial h

/-- 止まらない系（どこでも未定義）は 2 状態 RTM `escTbl` で模倣できる。 -/
theorem sim_none : Simulates escTbl (fun _ : ℕ => (Part.none : Part ℕ)) := by
  refine ⟨fun _ => (1, [], []), fun _ => 0, Computable.const _, Computable.const _, ?_, ?_⟩
  · intro a v hv; exact absurd hv (Part.notMem_none v)
  · intro a _ hH
    rw [ZHalts_iff] at hH
    obtain ⟨n, hn⟩ := hH
    exact escTbl_never n 0 _ (fun x _ => by
      show tapeOf 0 [] [] x = 0
      unfold tapeOf; split <;> rfl) hn

end URTM.Meta
