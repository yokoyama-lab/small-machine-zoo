/-
  2 状態 RTM の停止問題の決定可能性 その 8: 主定理。**手書き**。

    * `central_bound` : 停止する実行では、両側の半直線への入場回数は NB 以下
    * `halt_time_bound` : 停止するなら、停止までの歩数は `haltBound nsym a b` 未満
      （入場回数 → 深さ（`depth_bound`）→ 窓の大きさ → 配置は繰り返さない → 鳩の巣）
    * `decideHalt` / `decideHalt_correct` : **停止問題は決定可能**。`decideHalt` は
      `haltBound` 歩だけ素朴に回して停止したかを返す、全域の計算可能な関数。

  仮定: 方向状態機械 π（状態 ＝ 直前の移動方向）で 0 シフトなし（`NoZ`）、記号は nsym 未満で
  規則が閉じている（`Closed`）、初期配置は窓 [a,b] の外が空白でヘッドは窓の中。
  **可逆性は使わない**（2 状態の可逆 TM は構造定理によりこの形になる。`TwoState.lean`）。
-/
import URTM.TSDCentral

namespace URTM.TwoState

/-- 窓の配置の数と、入場回数の上界。 -/
def winW (a b : Int) : Nat := (b - a + 1).toNat

def entBound (nsym : Nat) (a b : Int) : Nat := csize nsym (winW a b) * (2 * nsym + 3) + 1

/-- 停止までの歩数の上界（天文学的だが計算可能）。 -/
def haltBound (nsym : Nat) (a b : Int) : Nat :=
  csize nsym (winW a b + 2 * entBound nsym a b + 2)

section Main
variable {π : Rule} {c : Conf2} {T : Nat}

theorem zorb_inwin (hcl : Closed π nsym) (hinit : ∀ x, c.tape x < nsym) (a b : Int)
    (hab : a ≤ b) (ha : a ≤ c.pos) (hb : c.pos ≤ b)
    (hsupp : ∀ x, (x < a ∨ b < x) → c.tape x = 0) :
    ∀ m z, zorb π a b c m = some z → InWin nsym a (winW a b) z := by
  have hW : (winW a b : Int) = b - a + 1 := by unfold winW; omega
  intro m
  induction m with
  | zero =>
    intro z h
    have : c = z := Option.some.inj h
    subst this
    exact ⟨ha, by omega, fun x hx => hsupp x (by omega), hinit⟩
  | succ m ih =>
    intro z h
    change (zorb π a b c m).bind (stepZ π a b) = some z at h
    cases hm : zorb π a b c m with
    | none => rw [hm] at h; exact absurd h (by simp)
    | some y =>
      rw [hm] at h
      obtain ⟨y1, y2, y3, y4⟩ := ih y hm
      change stepZ π a b y = some z at h
      unfold stepZ at h
      cases hr : π y.dir (y.tape y.pos) with
      | none => rw [hr] at h; exact absurd h (by simp)
      | some vd =>
        obtain ⟨v, d'⟩ := vd
        rw [hr] at h
        have hv : v < nsym := hcl _ _ _ _ (y4 _) hr
        have htape : ∀ x, (x < a ∨ a + (winW a b : Int) ≤ x) → write y.tape y.pos v x = 0 := by
          intro x hx
          have hne : x ≠ y.pos := by omega
          rw [write_off _ _ _ hne]; exact y3 x hx
        have hsym : ∀ x, write y.tape y.pos v x < nsym := by
          intro x; unfold write; split
          · exact hv
          · exact y4 x
        simp only at h
        split at h
        · rename_i hw
          have e := (Option.some.inj h).symm
          subst e
          exact ⟨hw.1, by show move d' y.pos < _; omega, htape, hsym⟩
        · have e := (Option.some.inj h).symm
          subst e
          exact ⟨y1, y2, htape, hsym⟩

/-- **中央の上界**: 両側の半直線への入場は `entBound` 以下。 -/
theorem HaltRun.central_bound (hZ : NoZ π) (hR : HaltRun π c T) {nsym : Nat}
    (hcl : Closed π nsym) (hinit : ∀ x, c.tape x < nsym) (a b : Int) (hab : a ≤ b)
    (ha : a ≤ c.pos) (hb : c.pos ≤ b) (hsupp : ∀ x, (x < a ∨ b < x) → c.tape x = 0) :
    Ent π c (b + 1) T ≤ entBound nsym a b ∧ EntL π c a T ≤ entBound nsym a b := by
  have hc0 : a ≤ P π c 0 ∧ P π c 0 ≤ b := ⟨ha, hb⟩
  obtain ⟨tl, _, htlT, htlc, htld⟩ :=
    exists_last (fun u => a ≤ P π c u ∧ P π c u ≤ b) T 0 hc0
  rw [Nat.zero_add] at htlT htld
  obtain ⟨zl, hzl, ⟨hzp, hzd, hzt⟩, hE, hL⟩ :=
    hR.sim hZ a b hab ha hb (tl + 1) tl (by omega) htlT htlc
  -- 最後の窓の時刻のあとは、窓の外（入場の 1 歩は窓の端で起きるので、高々 1 回増える）
  have hEle : Ent π c (b + 1) T ≤ Ent π c (b + 1) tl + 1 := by
    rcases Nat.eq_or_lt_of_le htlT with h | h
    · rw [h]; omega
    · have e : T = (tl + 1) + (T - (tl + 1)) := by omega
      rw [e, Ent_const π c (b + 1) (tl + 1) _ (fun u h1 h2 hs => by
        have := htld u (by omega) (by omega); have := hs.1; omega)]
      exact Ent_succ_le π c (b + 1) tl
  have hLle : EntL π c a T ≤ EntL π c a tl + 1 := by
    rcases Nat.eq_or_lt_of_le htlT with h | h
    · rw [h]; omega
    · have e : T = (tl + 1) + (T - (tl + 1)) := by omega
      rw [e, EntL_const π c a (tl + 1) _ (fun u h1 h2 hs => by
        have := htld u (by omega) (by omega); have := hs.1; omega)]
      show EntL π c a tl + (if LStep π c a tl then 1 else 0) ≤ _
      split <;> omega
  -- 鍵: 窓の軌道の長さ n は Zs·(2nsym+3) 未満
  have hkey : Cnt π c a b tl < csize nsym (winW a b) * (2 * nsym + 3) := by
    refine Classical.byContradiction fun hbig => ?_
    have hn : csize nsym (winW a b) * (2 * nsym + 3) ≤ Cnt π c a b tl := by omega
    generalize hZs : csize nsym (winW a b) = Zs at hn
    generalize hnn : Cnt π c a b tl = n at hn hzl hE hL
    have hZn : Zs ≤ n := by
      have : Zs * 1 ≤ Zs * (2 * nsym + 3) := Nat.mul_le_mul_left Zs (by omega)
      omega
    have hdef : ∀ m, m ≤ n → zorb π a b c m ≠ none := by
      intro m hm hnone
      have := oorb_none_mono (stepZ π a b) c m (n - m) hnone
      rw [show m + (n - m) = n by omega] at this
      change zorb π a b c n = none at this
      rw [hzl] at this; exact absurd this (by simp)
    have hinw := zorb_inwin (π := π) hcl hinit a b hab ha hb hsupp
    have hcodes : ∀ m, m ≤ Zs → ccode nsym a (winW a b) ((zorb π a b c m).getD c) < Zs := by
      intro m hm
      cases hq : zorb π a b c m with
      | none => exact absurd hq (hdef m (by omega))
      | some q => rw [← hZs]; exact ccode_lt (hinw m q hq)
    obtain ⟨i, j, hij, hjZ, hq⟩ := pigeon Zs _ hcodes
    have heq : zorb π a b c i = zorb π a b c j := by
      cases hqi : zorb π a b c i with
      | none => exact absurd hqi (hdef i (by omega))
      | some qi =>
        cases hqj : zorb π a b c j with
        | none => exact absurd hqj (hdef j (by omega))
        | some qj =>
          simp only [hqi, hqj, Option.getD] at hq
          rw [ccode_inj (hinw i qi hqi) (hinw j qj hqj) hq]
    have hper : ∀ m, j ≤ m → zorb π a b c (m - (j - i)) = zorb π a b c m := by
      intro m hm
      have := oorb_shift_eq (stepZ π a b) c i j heq (m - j)
      rw [show i + (m - j) = m - (j - i) by omega, show j + (m - j) = m by omega] at this
      exact this
    have hlam : 1 ≤ j - i := by omega
    have hiter : ∀ q, q * (j - i) + i ≤ n → zorb π a b c (n - q * (j - i)) = some zl := by
      intro q
      induction q with
      | zero => intro _; rw [Nat.zero_mul, Nat.sub_zero]; exact hzl
      | succ q ih =>
        intro hq
        rw [Nat.succ_mul] at hq ⊢
        rw [show n - (q * (j - i) + (j - i)) = (n - q * (j - i)) - (j - i) by omega,
          hper (n - q * (j - i)) (by omega)]
        exact ih (by omega)
    have hQ : (2 * nsym + 2) * (j - i) ≤ (2 * nsym + 2) * Zs :=
      Nat.mul_le_mul_left _ (by omega)
    have hn' : (2 * nsym + 2) * Zs + Zs ≤ n := by
      have : Zs * (2 * nsym + 3) = (2 * nsym + 2) * Zs + Zs := by
        rw [Nat.mul_comm, Nat.succ_mul]
      omega
    rcases Nat.eq_or_lt_of_le htlT with htT | htT
    · -- 窓の中で停止: 周期の前のコピーでは停止していないので矛盾
      have hh := hR.halt
      rw [← htT] at hh
      have hsz : stepZ π a b zl = none := by
        unfold stepZ
        have hread : zl.tape zl.pos = (tr π c tl).tape (tr π c tl).pos := by
          rw [hzp]; exact hzt _ htlc.1 htlc.2
        rw [hread, hzd]
        unfold step2 at hh
        cases hr : π (tr π c tl).dir ((tr π c tl).tape (tr π c tl).pos) with
        | none => rfl
        | some r => rw [hr] at hh; exact absurd hh (by simp)
      have h1 : zorb π a b c (n + 1) = none := by
        show (zorb π a b c n).bind (stepZ π a b) = none; rw [hzl]; exact hsz
      have h2 := hper (n + 1) (by omega)
      rw [h1] at h2
      exact hdef (n + 1 - (j - i)) (by omega) h2
    · -- 半直線の中で停止
      have hout : ¬ (a ≤ P π c (tl + 1) ∧ P π c (tl + 1) ≤ b) := htld (tl + 1) (by omega) htT
      have hst := hR.step tl htT
      obtain ⟨v, d', hr, _, hps, _⟩ := step2_some π hst
      have hread : zl.tape zl.pos = (tr π c tl).tape (tr π c tl).pos := by
        rw [hzp]; exact hzt _ htlc.1 htlc.2
      have hrz : π zl.dir (zl.tape zl.pos) = some (v, d') := by rw [hread, hzd]; exact hr
      have hmv : move d' zl.pos = P π c (tl + 1) := by
        rw [hzp]; show _ = (tr π c (tl + 1)).pos; rw [hps]
      have hm1 := hR.move1 hZ tl htT
      by_cases hright : b < P π c (tl + 1)
      · have hgt : b < P π c T := by
          have := hR.outside_right hZ a b hab (tl + 1) (T - (tl + 1)) (by omega) hright
            (fun u h1 h2 => htld u (by omega) (by omega))
          rwa [show tl + 1 + (T - (tl + 1)) = T by omega] at this
        have hin := hR.inside_halt_bound hZ hcl hinit (b + 1)
          (fun x hx => hsupp x (by omega)) (by omega) (by omega)
        have hrefl : reflR π b zl = 1 := by
          unfold reflR; rw [hrz]; simp only; rw [if_pos (by rw [hmv]; exact hright)]
        have hge := RefR_ge π a b c (j - i) hlam (2 * nsym + 2) n (by omega)
          (fun q h1 h2 => ⟨zl, hiter q (by
            have : q * (j - i) ≤ (2 * nsym + 2) * (j - i) := Nat.mul_le_mul_right _ h2
            omega), hrefl⟩)
        have hstep : EntStep π c (b + 1) tl := ⟨by omega, by omega⟩
        have h3 := Ent_mono' π c (b + 1) (show tl + 1 ≤ T by omega)
        rw [Ent_succ_of π c (b + 1) tl hstep, hE] at h3
        omega
      · have hleft : P π c (tl + 1) < a := by omega
        have hlt : P π c T < a := by
          have := hR.outside_left hZ a b hab (tl + 1) (T - (tl + 1)) (by omega) hleft
            (fun u h1 h2 => htld u (by omega) (by omega))
          rwa [show tl + 1 + (T - (tl + 1)) = T by omega] at this
        have hin := hR.inside_halt_bound_left hZ hcl hinit a
          (fun x hx => hsupp x (by omega)) ha (by omega)
        have hrefl : reflL π a zl = 1 := by
          unfold reflL; rw [hrz]; simp only; rw [if_pos (by rw [hmv]; exact hleft)]
        have hge := RefL_ge π a b c (j - i) hlam (2 * nsym + 2) n (by omega)
          (fun q h1 h2 => ⟨zl, hiter q (by
            have : q * (j - i) ≤ (2 * nsym + 2) * (j - i) := Nat.mul_le_mul_right _ h2
            omega), hrefl⟩)
        have hstep : LStep π c a tl := ⟨by omega, by omega⟩
        have h3 : EntL π c a (tl + 1) ≤ EntL π c a T := by
          have e : T = (tl + 1) + (T - (tl + 1)) := by omega
          rw [e, EntL_const π c a (tl + 1) _ (fun u h1 h2 hs => by
            have := htld u (by omega) (by omega); have := hs.1; omega)]
          exact Nat.le_refl _
        have h4 : EntL π c a (tl + 1) = EntL π c a tl + 1 := by
          show EntL π c a tl + (if LStep π c a tl then 1 else 0) = _
          rw [if_pos hstep]
        rw [h4, hL] at h3
        omega
  have hr1 := RefR_le π a b c (Cnt π c a b tl)
  have hl1 := RefL_le π a b c (Cnt π c a b tl)
  unfold entBound
  constructor <;> omega

/-- 配置が繰り返したら停止しない。 -/
theorem HaltRun.no_repeat (hR : HaltRun π c T) (i j : Nat) (hij : i < j) (hj : j ≤ T)
    (he : tr π c i = tr π c j) : False := by
  have hrun : run2 π (j - i) (tr π c i) = some (tr π c i) := by
    have := hR.run_mid i (j - i) (by omega)
    rw [show i + (j - i) = j by omega, ← he] at this; exact this
  have hall : ∀ q, run2 π (q * (j - i)) (tr π c i) = some (tr π c i) := by
    intro q
    induction q with
    | zero => rw [Nat.zero_mul]; rfl
    | succ q ih => rw [Nat.succ_mul, run2_add, ih]; exact hrun
  have hdead := hR.run_from i (by omega)
  have hle : T + 1 - i ≤ (T + 1 - i) * (j - i) := by
    have := Nat.mul_le_mul_left (T + 1 - i) (show 1 ≤ j - i by omega); simpa using this
  have := run2_none_mono π _ _ _ hdead hle
  rw [hall] at this; exact absurd this (by simp)

/-- **停止までの歩数の上界**。 -/
theorem HaltRun.halt_time_bound (hZ : NoZ π) (hR : HaltRun π c T) {nsym : Nat}
    (hcl : Closed π nsym) (hinit : ∀ x, c.tape x < nsym) (a b : Int) (hab : a ≤ b)
    (ha : a ≤ c.pos) (hb : c.pos ≤ b) (hsupp : ∀ x, (x < a ∨ b < x) → c.tape x = 0) :
    T < haltBound nsym a b := by
  obtain ⟨hER, hEL⟩ := hR.central_bound hZ hcl hinit a b hab ha hb hsupp
  generalize hNB : entBound nsym a b = NB at hER hEL
  have hW : (winW a b : Int) = b - a + 1 := by unfold winW; omega
  -- ヘッドは [a - NB, b + NB] の中
  have hposR := hR.depth_bound hZ (b + 1) (fun x hx => hsupp x (by omega)) (by omega)
  have hposL := hR.depth_bound_left hZ a (fun x hx => hsupp x (by omega)) ha
  have hposR' : ∀ t, t ≤ T → P π c t ≤ b + NB := by
    intro t ht; have := hposR t ht; omega
  have hposL' : ∀ t, t ≤ T → a - NB ≤ P π c t := by
    intro t ht; have := hposL t ht; omega
  obtain ⟨lo, hlo⟩ : ∃ lo : Int, lo = a - NB - 1 := ⟨_, rfl⟩
  obtain ⟨W', hW'⟩ : ∃ W' : Nat, W' = winW a b + 2 * NB + 2 := ⟨_, rfl⟩
  have hW'i : (W' : Int) = b - a + 1 + 2 * NB + 2 := by rw [hW']; push_cast; omega
  have hinw : ∀ t, t ≤ T → InWin nsym lo W' (tr π c t) := by
    intro t ht
    refine ⟨by have := hposL' t ht; show lo ≤ P π c t; omega,
      by have := hposR' t ht; show P π c t < lo + (W' : Int); omega, ?_,
      hR.tape_lt hcl hinit t ht⟩
    intro x hx
    have hfz := hR.cell_frozen x 0 t (by omega) (fun u _ h2 he => by
      have h1 := hposL' u (by omega); have h2' := hposR' u (by omega)
      rw [he] at h1 h2'
      rcases hx with hx | hx <;> omega)
    rw [Nat.zero_add] at hfz
    rw [hfz]
    show c.tape x = 0
    rcases hx with hx | hx
    · exact hsupp x (Or.inl (by omega))
    · exact hsupp x (Or.inr (by omega))
  unfold haltBound
  rw [hNB]
  refine Classical.byContradiction fun hbig => ?_
  have hK : csize nsym W' ≤ T := by rw [hW']; omega
  obtain ⟨i, j, hij, hjK, hq⟩ := pigeon (csize nsym W') (fun t => ccode nsym lo W' (tr π c t))
    (fun t ht => ccode_lt (hinw t (by omega)))
  exact hR.no_repeat i j hij (by omega) (ccode_inj (hinw i (by omega)) (hinw j (by omega)) hq)

end Main

/-- **決定手続き**: `haltBound` 歩だけ回して停止したかを返す。 -/
def decideHalt (π : Rule) (nsym : Nat) (a b : Int) (c : Conf2) : Bool :=
  (run2 π (haltBound nsym a b) c).isNone

/-- **主定理（2 状態 RTM の停止問題は有限配置上で決定可能）**。 -/
theorem decideHalt_correct (π : Rule) (hZ : NoZ π) (nsym : Nat) (hcl : Closed π nsym)
    (a b : Int) (c : Conf2) (hinit : ∀ x, c.tape x < nsym) (hab : a ≤ b)
    (ha : a ≤ c.pos) (hb : c.pos ≤ b) (hsupp : ∀ x, (x < a ∨ b < x) → c.tape x = 0) :
    decideHalt π nsym a b c = true ↔ Halts π c := by
  constructor
  · intro h
    unfold decideHalt at h
    cases hr : run2 π (haltBound nsym a b) c with
    | none => exact ⟨_, hr⟩
    | some x => rw [hr] at h; exact absurd h (by simp)
  · intro h
    obtain ⟨T, hR⟩ := halts_haltRun h
    have hT := hR.halt_time_bound hZ hcl hinit a b hab ha hb hsupp
    have := run2_none_mono π c (T + 1) (haltBound nsym a b) hR.dead (by omega)
    unfold decideHalt; rw [this]; rfl

end URTM.TwoState
