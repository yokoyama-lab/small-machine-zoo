/-
  2 状態 RTM の停止問題の決定可能性 その 3: 空白半直線への潜り込みの深さ。**手書き**。

  停止する実行で、はじめ空白の半直線 [k,∞)（ヘッドは k 未満から出発）について:
    * `entry_chain` : **補題 4.1（実行版）**。i 回目の入場時の [k,∞) の中身は、
      空白から i-1 回の滞在を終えた中身 `Chain π k (i-1) blankT` に等しい
    * `depth_step`  : [k+1,∞) への入場回数は [k,∞) への入場回数より真に少ない（0 でなければ）。
      証明は「最初に追いついた添字」で自己相似の逃走補題に帰着する
    * `depth_bound` : ヘッドは k + (入場回数) より右へは行かない
-/
import URTM.TSDSoj

namespace URTM.TwoState

section Depth
variable {π : Rule} {c : Conf2} {T : Nat}

theorem HaltRun.conf_eq (hR : HaltRun π c T) (t : Nat) :
    tr π c t = ⟨(tr π c t).tape, (tr π c t).pos, (tr π c t).dir⟩ := rfl

/-- 滞在を実行から切り出す。 -/
theorem HaltRun.soj_of (hR : HaltRun π c T) (k : Int) (e x : Nat) (hex : e ≤ x) (hx : x ≤ T)
    (hin : ∀ u, e ≤ u → u < x → k ≤ P π c u) (hout : P π c x < k) :
    Soj π k (tr π c e) (x - e) (tr π c x) := by
  refine ⟨?_, hout, ?_⟩
  · have := hR.run_mid e (x - e) (by omega)
    rw [show e + (x - e) = x by omega] at this; exact this
  · intro j hj cj hcj
    rw [hR.run_mid e j (by omega)] at hcj
    have : cj = tr π c (e + j) := (Option.some.inj hcj).symm
    rw [this]; exact hin (e + j) (by omega) (by omega)

/-- **補題 4.1（実行版）**。 -/
theorem HaltRun.entry_chain (hZ : NoZ π) (hR : HaltRun π c T) (k : Int)
    (hblank : ∀ x, k ≤ x → c.tape x = 0) (h0 : c.pos < k) :
    ∀ (N s : Nat), s < N → s < T → EntStep π c k s →
      Chain π k (Ent π c k (s + 1) - 1) blankT (tr π c (s + 1)).tape := by
  intro N
  induction N with
  | zero => intro s hs; omega
  | succ N ih =>
    intro s hsN hsT hE
    have hEs : Ent π c k (s + 1) = Ent π c k s + 1 := Ent_succ_of π c k s hE
    rw [hEs, Nat.add_sub_cancel]
    have hPs : P π c s = k - 1 := hE.1
    by_cases hz : Ent π c k s = 0
    · -- 最初の入場: それまでずっと k 未満なので [k,∞) は空白のまま
      rw [hz]
      have hbelow := hR.stay_below hZ k 0 s (Nat.zero_le _) (by omega) h0
        (by rw [hz]; rfl)
      intro x hx
      have := hR.frozen_right k 0 (s + 1) (by omega) (by omega)
        (fun u _ hu => hbelow u (Nat.zero_le _) (by omega)) x hx
      rw [this]; exact hblank x hx
    · -- 直前の入場 s' を取り、そこからの滞在と退場後の凍結をつなぐ
      obtain ⟨s₁, hs₁a, hs₁b, hs₁c⟩ :=
        Ent_grow π c k 0 s (Nat.zero_le _) (by show 0 < Ent π c k s; omega)
      obtain ⟨s', hs'a, hs'b, hs'E, hs'L⟩ :=
        exists_last (fun u => EntStep π c k u) (s - 1 - s₁) s₁ hs₁c
      have hs's : s' < s := by omega
      have hnoE : ∀ u, s' < u → u < s → ¬ EntStep π c k u :=
        fun u h1 h2 => hs'L u h1 (by omega)
      have hEs' : Ent π c k s = Ent π c k (s' + 1) := by
        have e : s = (s' + 1) + (s - (s' + 1)) := by omega
        rw [e, Ent_const π c k (s' + 1) (s - (s' + 1))
          (fun u h1 h2 => hnoE u (by omega) (by omega))]
      have IH := ih s' (by omega) (by omega) hs'E
      have hk1 : P π c (s' + 1) = k := hs'E.2
      have hd1 : (tr π c (s' + 1)).dir = Dir.R := hR.entry_dir hZ k s' (by omega) hs'E
      -- 退場
      have hne : s ≠ s' + 1 := by intro h; rw [h] at hPs; omega
      obtain ⟨x₀, hx₀a, hx₀b, hx₀c, hx₀d, hx₀e⟩ :=
        hR.cross_down hZ k (s' + 1) s (by omega) (by omega) (by omega) (by omega)
      have hbelow : ∀ u, x₀ + 1 ≤ u → u ≤ s → P π c u < k := by
        apply hR.stay_below hZ k (x₀ + 1) s (by omega) (by omega) (by omega)
        have e : s = (x₀ + 1) + (s - (x₀ + 1)) := by omega
        rw [e, Ent_const π c k (x₀ + 1) (s - (x₀ + 1))
          (fun u h1 h2 => hnoE u (by omega) (by omega))]
      have hsoj := hR.soj_of k (s' + 1) (x₀ + 1) (by omega) (by omega)
        (fun u h1 h2 => hx₀e u h1 (by omega)) (by omega)
      have hk1' : (tr π c (s' + 1)).pos = k := hk1
      have heq : tr π c (s' + 1) = ⟨(tr π c (s' + 1)).tape, k, Dir.R⟩ := by
        rw [← hk1', ← hd1]
      rw [heq] at hsoj
      have hE1 : Ent π c k (s' + 1) = Ent π c k s' + 1 := Ent_succ_of π c k s' hs'E
      have hj : Ent π c k s = (Ent π c k (s' + 1) - 1) + 1 := by omega
      rw [hj]
      refine ⟨(tr π c (s' + 1)).tape, x₀ + 1 - (s' + 1), tr π c (x₀ + 1), ?_, hsoj, ?_⟩
      · exact IH
      · intro x hx
        exact hR.frozen_right k (x₀ + 1) (s + 1) (by omega) (by omega)
          (fun u h1 h2 => hbelow u h1 (by omega)) x hx

/-- **深さの 1 段**: [k+1,∞) への入場は [k,∞) への入場より真に少ない。 -/
theorem HaltRun.depth_step (hZ : NoZ π) (hR : HaltRun π c T) (k : Int)
    (hblank : ∀ x, k ≤ x → c.tape x = 0) (h0 : c.pos < k) :
    Ent π c (k + 1) T < Ent π c k T ∨ Ent π c (k + 1) T = 0 := by
  by_cases hc : Ent π c (k + 1) T = 0
  · exact Or.inr hc
  left
  apply Nat.lt_of_not_le
  intro hge
  -- [k,∞) に一度は入っている
  have hEk : 0 < Ent π c k T := by
    obtain ⟨s, hs1', hs2, hs3⟩ := Ent_grow π c (k + 1) 0 T (Nat.zero_le _)
      (by show 0 < Ent π c (k + 1) T; omega)
    have hPs : P π c s = k := by have := hs3.1; omega
    obtain ⟨s₂, _, _, h3, h4, _⟩ :=
      hR.cross_up hZ k 0 s (by
        rcases Nat.eq_zero_or_pos s with h | h
        · rw [h] at hPs; exact absurd hPs (by show c.pos ≠ k; omega)
        · exact h) (by omega) h0 (by omega)
    have := Ent_mono' π c k (show s₂ + 1 ≤ T by omega)
    rw [Ent_succ_of π c k s₂ ⟨h3, h4⟩] at this; omega
  -- 最初の [k,∞) 入場
  obtain ⟨s₁, hs₁a, hs₁b, hs₁⟩ := Ent_grow π c k 0 T (Nat.zero_le _) hEk
  obtain ⟨e₁, he₁a, he₁b, he₁c, he₁d⟩ :=
    exists_first (fun u => EntStep π c k u) s₁ 0 (by simpa using hs₁)
  have hbel : ∀ u, u ≤ e₁ → P π c u < k := by
    have := hR.stay_below hZ k 0 e₁ (Nat.zero_le _) (by omega) h0 (by
      have e : e₁ = 0 + e₁ := by omega
      rw [e, Ent_const π c k 0 e₁ (fun u h1 h2 => he₁d u h1 (by omega))])
    exact fun u hu => this u (Nat.zero_le _) hu
  have hQ1 : Ent π c (k + 1) (e₁ + 1) < Ent π c k (e₁ + 1) := by
    rw [Ent_succ_of π c k e₁ he₁c]
    have : Ent π c (k + 1) (e₁ + 1) = 0 := by
      have e : e₁ + 1 = 0 + (e₁ + 1) := by omega
      rw [e, Ent_const π c (k + 1) 0 (e₁ + 1) (fun u h1 h2 hs => by
        have := hbel u (by omega); have := hs.1; omega)]
      rfl
    omega
  -- 最初に追いつく時刻
  have hle : e₁ + 1 ≤ T := by omega
  obtain ⟨t, ht1, ht2, ht3, ht4⟩ :=
    exists_first (fun u => Ent π c k u ≤ Ent π c (k + 1) u) (T - (e₁ + 1)) (e₁ + 1)
      (by rw [show e₁ + 1 + (T - (e₁ + 1)) = T by omega]; exact hge)
  have ht0 : t ≠ e₁ + 1 := by intro h; rw [h] at ht3; omega
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  have hprev : ¬ (Ent π c k s ≤ Ent π c (k + 1) s) := ht4 s (by omega) (by omega)
  have hsT : s < T := by omega
  have hA := Ent_succ_le π c k s
  have hB := Ent_succ_le π c (k + 1) s
  have hmk := Ent_mono π c k s 1
  have hmk1 := Ent_mono π c (k + 1) s 1
  have hstep : EntStep π c (k + 1) s := by
    refine Classical.byContradiction fun hn => ?_
    rw [Ent_succ_not π c (k + 1) s hn] at ht3; omega
  have hnotk : ¬ EntStep π c k s := by
    intro h; have := h.1; have := hstep.1; omega
  rw [Ent_succ_not π c k s hnotk, Ent_succ_of π c (k + 1) s hstep] at ht3
  have hi : Ent π c k s = Ent π c (k + 1) s + 1 := by omega
  -- s で位置 k。直近の [k,∞) 入場 s₀
  have hPs : P π c s = k := by have := hstep.1; omega
  obtain ⟨s₀, hs₀a, hs₀b, hs₀c, hs₀d⟩ := hR.last_entry hZ k s (by omega) h0 (by omega)
  have C1 := hR.entry_chain hZ k hblank h0 (s₀ + 1) s₀ (by omega) (by omega) hs₀b
  have C2 := hR.entry_chain hZ (k + 1) (fun x hx => hblank x (by omega)) (by omega)
    (s + 1) s (by omega) hsT hstep
  rw [hs₀c] at C1
  rw [Ent_succ_of π c (k + 1) s hstep, ← hi] at C2
  have C1' := Chain_shift π k 1 _ _ _ C1
  have hag := Chain_func π (k + 1) _ _ _ _ C1' C2
  -- 自己相似の逃走補題
  have hd0 : (tr π c (s₀ + 1)).dir = Dir.R := hR.entry_dir hZ k s₀ (by omega) hs₀b
  have hd1 : (tr π c (s + 1)).dir = Dir.R := hR.entry_dir hZ (k + 1) s hsT hstep
  have hp0 : P π c (s₀ + 1) = k := hs₀b.2
  have hp1 : P π c (s + 1) = k + 1 := hstep.2
  have hnever := selfsim_never_halts π (tr π c (s₀ + 1)) (tr π c (s + 1)) (s - s₀)
    (by omega)
    (by have := hR.run_mid (s₀ + 1) (s - s₀) (by omega)
        rw [show s₀ + 1 + (s - s₀) = s + 1 by omega] at this; exact this)
    (by intro j hj cj hcj
        rw [hR.run_mid (s₀ + 1) j (by omega)] at hcj
        have : cj = tr π c (s₀ + 1 + j) := (Option.some.inj hcj).symm
        rw [this]
        show P π c (s₀ + 1) ≤ P π c (s₀ + 1 + j)
        rw [hp0]; exact hs₀d (s₀ + 1 + j) (by omega) (by omega))
    (by show P π c (s + 1) = P π c (s₀ + 1) + 1; rw [hp0, hp1])
    (by rw [hd0, hd1])
    (by intro x hx
        have hx' : k + 1 ≤ x := by
          have : P π c (s₀ + 1) + 1 ≤ x := hx
          rw [hp0] at this; exact this
        rw [← hag x hx']
        rfl)
  exact hnever _ (hR.run_from (s₀ + 1) (by omega))

/-- **深さの上界**: ヘッドは k + (入場回数) より右へは行かない。 -/
theorem HaltRun.depth_bound (hZ : NoZ π) (hR : HaltRun π c T) (k : Int)
    (hblank : ∀ x, k ≤ x → c.tape x = 0) (h0 : c.pos < k) :
    ∀ t, t ≤ T → P π c t < k + Ent π c k T := by
  have key : ∀ j : Nat, Ent π c (k + j) T + j ≤ Ent π c k T ∨ Ent π c (k + j) T = 0 := by
    intro j
    induction j with
    | zero => left; simp
    | succ j ih =>
      have hs := hR.depth_step hZ (k + j) (fun x hx => hblank x (by omega)) (by omega)
      have e : k + ((j + 1 : Nat) : Int) = k + j + 1 := by push_cast; omega
      rw [e]
      rcases hs with h | h
      · rcases ih with h' | h'
        · left; omega
        · right; omega
      · right; exact h
  intro t ht
  refine Classical.byContradiction fun hc => ?_
  have hc' : k + Ent π c k T ≤ P π c t := by omega
  have hzero : Ent π c (k + (Ent π c k T : Nat)) T = 0 := by
    rcases key (Ent π c k T) with h | h
    · omega
    · exact h
  have hz0 : P π c 0 < k + (Ent π c k T : Nat) := by
    show c.pos < _; omega
  have := hR.stay_below hZ (k + (Ent π c k T : Nat)) 0 t (Nat.zero_le _) ht hz0 (by
    have h1 := Ent_mono' π c (k + (Ent π c k T : Nat)) ht
    rw [hzero] at h1
    have h2 : Ent π c (k + (Ent π c k T : Nat)) 0 = 0 := rfl
    omega) t (Nat.zero_le _) (Nat.le_refl _)
  omega

end Depth

end URTM.TwoState
