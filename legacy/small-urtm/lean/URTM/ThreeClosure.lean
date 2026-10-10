/-
  3 状態 2 記号 RTM の停止問題の決定可能性 その 5: **閉包の検査の健全性**。**手書き**。

  `closedR tbl C M = true` なら、ヘッドが b 以下から始まり (b, ∞) が空白の配置から**止まる**実行では、
  ヘッドはずっと b + M 以下に居る（`right_bound`）。

  証明: ヘッドが b 以下に居て (b, ∞) の中身が C の模様 P であるような時刻 t₀ から、次に b より右へ
  出る時刻 t₁ を取る。t₁ の配置はちょうど「状態 e で模様 P に入った訪問」なので、`visit_sound` から
  訪問の結果が分かる。`div` なら止まらないので矛盾、`halt` なら止まるまで b + M 以下、`ret` なら
  戻った時刻で再び「b 以下・模様は C」になるので、残り時間についての帰納法で続ける。
-/
import URTM.ThreeVisit

namespace URTM.Three
open URTM URTM.TwoState

section
variable {tbl : List Quint} {c : QConf} {T : Nat}

/-- 時刻 t の (b, ∞) の中身が模様 P。 -/
def PatAt (tbl : List Quint) (c : QConf) (b : Int) (t : Nat) (P : List Nat) : Prop :=
  ∀ x, b < x → (qtr tbl c t).tape x = P.getD (x - b - 1).toNat 0

theorem mem_entR {r : Quint} (hr : r ∈ tbl) (hd : r.d = Dir.R) : r.q ∈ entR tbl := by
  unfold entR
  exact List.mem_map.mpr ⟨r, List.mem_filter.mpr ⟨hr, by simp [hd]⟩, rfl⟩

theorem closedR_spec {C : List (List Nat)} {M : Nat} (h : closedR tbl C M = true) :
    [] ∈ C ∧ ∀ P ∈ C, ∀ e ∈ entR tbl, entOK tbl e P = true → outOK C M (visit tbl e P) = true := by
  unfold closedR at h
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨by simpa using h1, fun P hP e he hok => ?_⟩
  have := (h2 P hP).2 e he
  rw [hok] at this; simpa using this

/-- 実行の途中の配置から先の実行。 -/
theorem _root_.URTM.TwoState.QHaltRun.run_at (hR : QHaltRun tbl c T) {t n : Nat} (h : t + n ≤ T) :
    qrun tbl n (qtr tbl c t) = some (qtr tbl c (t + n)) := hR.run_mid t n h

/-- ヘッドが b 以下のあいだ、(b, ∞) の中身は変わらない。 -/
theorem _root_.URTM.TwoState.QHaltRun.pat_frozen (hR : QHaltRun tbl c T) {b : Int} {t₀ t₁ : Nat} (h01 : t₀ ≤ t₁)
    (h1T : t₁ ≤ T) (hle : ∀ u, t₀ ≤ u → u < t₁ → (qtr tbl c u).pos ≤ b) {P : List Nat}
    (hP : PatAt tbl c b t₀ P) : PatAt tbl c b t₁ P := by
  intro x hx
  have := hR.cell_frozen x t₀ (t₁ - t₀) (by omega) (fun u h1 h2 he => by
    have := hle u h1 (by omega); show False; unfold QP at he; omega)
  rw [show t₀ + (t₁ - t₀) = t₁ by omega] at this
  rw [this]; exact hP x hx

/-- 訪問の始まり: b 以下から b より右へ出た時刻の配置は、模様 P への訪問の始めの配置。 -/
theorem _root_.URTM.TwoState.QHaltRun.visit_start (hR : QHaltRun tbl c T) {b : Int} {t : Nat} (htT : t + 1 ≤ T)
    (hle : (qtr tbl c t).pos ≤ b) (hgt : b < (qtr tbl c (t + 1)).pos) {P : List Nat}
    (hP : PatAt tbl c b t P) :
    ∃ e ∈ entR tbl, qtr tbl c (t + 1) = vreal b (qtr tbl c (t + 1)).tape ⟨e, 1, P⟩ ∧
      PatAt tbl c b (t + 1) P := by
  obtain ⟨r, hr, _, he⟩ := qstep_some (hR.step t (by omega))
  have hd : r.d = Dir.R := by
    cases hrd : r.d with
    | L => rw [he, hrd] at hgt; simp [move] at hgt; omega
    | Z => rw [he, hrd] at hgt; simp [move] at hgt; omega
    | R => rfl
  have hpos : (qtr tbl c (t + 1)).pos = b + 1 := by
    rw [he, hd]; show (qtr tbl c t).pos + 1 = b + 1
    rw [he, hd] at hgt; simp [move] at hgt; omega
  have hP1 : PatAt tbl c b (t + 1) P := by
    intro x hx
    rw [he]; show write (qtr tbl c t).tape (qtr tbl c t).pos r.t x = _
    rw [write_off _ _ _ (by omega)]; exact hP x hx
  refine ⟨r.q, mem_entR hr hd, ?_, hP1⟩
  have hst : (qtr tbl c (t + 1)).st = r.q := by rw [he]
  have htape : glue b (qtr tbl c (t + 1)).tape P = (qtr tbl c (t + 1)).tape := by
    funext x; unfold glue; split
    · rename_i hx; exact (hP1 x hx).symm
    · rfl
  calc qtr tbl c (t + 1)
      = ⟨(qtr tbl c (t + 1)).st, (qtr tbl c (t + 1)).pos, (qtr tbl c (t + 1)).tape⟩ := rfl
    _ = vreal b (qtr tbl c (t + 1)).tape ⟨r.q, 1, P⟩ := by
      unfold vreal; simp only; rw [htape, hst, hpos]; simp

/-- 同じ状態へ入る規則は同じ向きに動く（可逆性の帰結。正規形の表では作り方から成り立つ）。 -/
def DirConsistent (tbl : List Quint) : Prop := ∀ r ∈ tbl, ∀ r' ∈ tbl, r.q = r'.q → r.d = r'.d

/-- **初めにしか居られない状態の訪問は空の模様から**: 状態 e へ入る規則がどれも e から出るなら、
    e で b+1 へ入った時刻までずっと e で右へ動いてきたので、(b, ∞) はまだ空白。 -/
theorem _root_.URTM.TwoState.QHaltRun.selfonly_blank (hR : QHaltRun tbl c T) (hdir : DirConsistent tbl)
    {b : Int} (hz : ∀ x, b < x → c.tape x = 0) {s : Nat} (hsT : s + 1 ≤ T)
    (hle : (qtr tbl c s).pos ≤ b) (hgt : b < (qtr tbl c (s + 1)).pos)
    (hso : selfOnly tbl (qtr tbl c (s + 1)).st = true) : PatAt tbl c b s [] := by
  have hso' : ∀ r ∈ tbl, r.q = (qtr tbl c (s + 1)).st → r.p = (qtr tbl c (s + 1)).st := by
    intro r hr hq
    unfold selfOnly at hso
    have := List.all_eq_true.mp hso r hr
    simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at this
    rcases this with h | h
    · exact absurd hq h
    · exact h
  -- 時刻 s の規則は右へ動いて e に入る
  obtain ⟨rs, hrs, _, hes⟩ := qstep_some (hR.step s (by omega))
  have hrsq : rs.q = (qtr tbl c (s + 1)).st := by rw [hes]
  have hrsd : rs.d = Dir.R := by
    cases hrd : rs.d with
    | L => rw [hes, hrd] at hgt; simp [move] at hgt; omega
    | Z => rw [hes, hrd] at hgt; simp [move] at hgt; omega
    | R => rfl
  -- 0..s+1 の状態はずっと e、各歩は右へ 1
  have hst : ∀ k, k ≤ s + 1 → (qtr tbl c (s + 1 - k)).st = (qtr tbl c (s + 1)).st := by
    intro k
    induction k with
    | zero => intro _; rfl
    | succ k ih =>
      intro hk
      have ih' := ih (by omega)
      obtain ⟨r, hr, hf, he⟩ := qstep_some (hR.step (s - k) (by omega))
      rw [show s - k + 1 = s + 1 - k by omega] at he
      have hq : r.q = (qtr tbl c (s + 1)).st := by rw [← ih', he]
      obtain ⟨_, hp, _⟩ := find?_spec hf
      rw [show s + 1 - (k + 1) = s - k by omega, ← hp]
      exact hso' r hr hq
  have hmove : ∀ u, u ≤ s → (qtr tbl c (u + 1)).pos = (qtr tbl c u).pos + 1 := by
    intro u hu
    obtain ⟨r, hr, _, he⟩ := qstep_some (hR.step u (by omega))
    have hq : r.q = (qtr tbl c (s + 1)).st := by
      have := hst (s - u) (by omega)
      rw [show s + 1 - (s - u) = u + 1 by omega, he] at this; exact this
    have hd : r.d = Dir.R := by rw [hdir r hr rs hrs (by rw [hq, hrsq]), hrsd]
    rw [he, hd]; rfl
  have hpos : ∀ k, k ≤ s → (qtr tbl c (s - k)).pos ≤ b := by
    intro k
    induction k with
    | zero => intro _; simpa using hle
    | succ k ih =>
      intro hk
      have := hmove (s - (k + 1)) (by omega)
      rw [show s - (k + 1) + 1 = s - k by omega] at this
      have := ih (by omega); omega
  intro x hx
  have := hR.cell_frozen x 0 s (by omega) (fun u _ h2 he => by
    have := hpos (s - u) (by omega)
    rw [show s - (s - u) = u by omega] at this
    unfold QP at he; omega)
  rw [Nat.zero_add] at this
  rw [this]
  show c.tape x = _
  rw [hz x hx]; simp

/-- 閉包の検査の健全性（残り時間についての帰納法）。 -/
theorem right_bound_aux (hR : QHaltRun tbl c T) (hdir : DirConsistent tbl) {C : List (List Nat)} {M : Nat}
    (hC : closedR tbl C M = true) (b : Int) (hb : c.pos ≤ b) (hz : ∀ x, b < x → c.tape x = 0) :
    ∀ m t₀, T - t₀ = m → t₀ ≤ T → (qtr tbl c t₀).pos ≤ b → (∃ P ∈ C, PatAt tbl c b t₀ P) →
      ∀ t, t₀ ≤ t → t ≤ T → (qtr tbl c t).pos ≤ b + M := by
  obtain ⟨hnil, hvis⟩ := closedR_spec hC
  intro m
  induction m using Nat.strongRecOn with
  | _ m ih =>
  intro t₀ hm ht₀ hle₀ ⟨P, hPC, hP⟩ t ht0 htT
  by_cases hex : ∃ u, t₀ < u ∧ u ≤ t ∧ b < (qtr tbl c u).pos
  · obtain ⟨u, hu1, hu2, hu3⟩ := hex
    obtain ⟨t₁, h1a, h1b, h1c, h1d⟩ := exists_first (fun u => b < (qtr tbl c u).pos) (u - (t₀ + 1))
      (t₀ + 1) (by rw [show t₀ + 1 + (u - (t₀ + 1)) = u by omega]; exact hu3)
    -- t₀ .. t₁ - 1 は b 以下
    have hbelow : ∀ v, t₀ ≤ v → v < t₁ → (qtr tbl c v).pos ≤ b := by
      intro v hv1 hv2
      rcases Nat.eq_or_lt_of_le hv1 with rfl | hv1
      · exact hle₀
      · have := h1d v (by omega) hv2; omega
    obtain ⟨s, rfl⟩ : ∃ s, t₁ = s + 1 := ⟨t₁ - 1, by omega⟩
    have hPs := hR.pat_frozen (t₀ := t₀) (t₁ := s) (by omega) (by omega)
      (fun v h1 h2 => hbelow v h1 (by omega)) hP
    -- 訪問に使う模様: 初めにしか居られない状態なら空の模様
    obtain ⟨P₀, hP₀C, hP₀, hok⟩ : ∃ P₀ ∈ C, PatAt tbl c b s P₀ ∧
        entOK tbl (qtr tbl c (s + 1)).st P₀ = true := by
      by_cases hso : selfOnly tbl (qtr tbl c (s + 1)).st = true
      · exact ⟨[], hnil, hR.selfonly_blank hdir hz (by omega) (hbelow s (by omega) (by omega)) h1c hso,
          by simp [entOK]⟩
      · exact ⟨P, hPC, hPs, by simp [entOK, hso]⟩
    obtain ⟨e, heR, hcfg, hPs1⟩ := hR.visit_start (t := s) (by omega) (hbelow s (by omega) (by omega)) h1c hP₀
    have he0 : (qtr tbl c (s + 1)).st = e := by rw [hcfg]; rfl
    have hout := hvis P₀ hP₀C e heR (he0 ▸ hok)
    have hspec := visit_sound tbl b (qtr tbl c (s + 1)).tape e P₀
    rw [← hcfg] at hspec
    -- 実際の実行と訪問の実行の対応
    have hrun : ∀ n, s + 1 + n ≤ T → qrun tbl n (qtr tbl c (s + 1)) = some (qtr tbl c (s + 1 + n)) :=
      fun n hn => hR.run_at hn
    cases hv : visit tbl e P₀ with
    | unk => rw [hv] at hout; simp [outOK] at hout
    | div =>
      rw [hv] at hspec
      obtain ⟨d, hd, _⟩ := hspec (T + 1 - (s + 1))
      rw [hR.run_from (s + 1) (by omega)] at hd; cases hd
    | halt k mp =>
      rw [hv] at hspec hout
      simp only [outOK, decide_eq_true_eq] at hout
      obtain ⟨hdead, hpos⟩ := hspec
      have hk : t - (s + 1) ≤ k := by
        rcases Nat.lt_or_ge k (t - (s + 1)) with hk | hk
        · have := qrun_none_mono tbl _ (k + 1) (t - (s + 1)) hdead (by omega)
          rw [hrun (t - (s + 1)) (by omega)] at this; cases this
        · exact hk
      have := hpos (t - (s + 1)) hk _ (hrun (t - (s + 1)) (by omega))
      rw [show s + 1 + (t - (s + 1)) = t by omega] at this
      omega
    | ret q P' k mp =>
      rw [hv] at hspec hout
      simp only [outOK, Bool.and_eq_true, decide_eq_true_eq] at hout
      obtain ⟨hP'C, hmp⟩ := hout
      obtain ⟨hback, hpos⟩ := hspec
      by_cases htk : t < s + 1 + k
      · have := hpos (t - (s + 1)) (by omega) _ (hrun (t - (s + 1)) (by omega))
        rw [show s + 1 + (t - (s + 1)) = t by omega] at this
        omega
      · -- 戻った時刻 s+1+k から帰納法
        have hkT : s + 1 + k ≤ T := by omega
        have hback' : qtr tbl c (s + 1 + k) = ⟨q, b, glue b (qtr tbl c (s + 1)).tape P'⟩ := by
          rw [hrun k hkT] at hback; exact Option.some.inj hback
        have hk1 : 1 ≤ k := by
          rcases Nat.eq_zero_or_pos k with h0 | h0
          · subst h0
            have := hrun 0 (by omega)
            rw [hback] at this
            have := congrArg QConf.pos (Option.some.inj this)
            simp at this
            have h' : (qtr tbl c (s + 1)).pos = b + 1 := by
              rw [hcfg]; unfold vreal; simp
            omega
          · exact h0
        refine ih (T - (s + 1 + k)) (by omega) (s + 1 + k) rfl hkT ?_ ⟨P', ?_, ?_⟩ t (by omega) htT
        · rw [hback']; exact Int.le_refl b
        · simpa using hP'C
        · intro x hx; rw [hback']; show glue b _ P' x = _; unfold glue; rw [if_pos hx]
  · -- t₀ のあと b より右へ出ない
    have : (qtr tbl c t).pos ≤ b := by
      rcases Nat.eq_or_lt_of_le ht0 with rfl | hlt
      · exact hle₀
      · exact Int.not_lt.mp fun hc => hex ⟨t, hlt, Nat.le_refl _, hc⟩
    omega

/-- **右側の有界性**: 閉包の検査が通れば、(b, ∞) が空白でヘッドが b 以下の配置から止まる実行の
    ヘッドは、止まるまでずっと b + M 以下。 -/
theorem right_bound (hR : QHaltRun tbl c T) (hdir : DirConsistent tbl) {C : List (List Nat)} {M : Nat}
    (hC : closedR tbl C M = true) (b : Int) (hb : c.pos ≤ b) (hz : ∀ x, b < x → c.tape x = 0) :
    ∀ t, t ≤ T → (qtr tbl c t).pos ≤ b + M := by
  have hnil := (closedR_spec hC).1
  intro t ht
  exact right_bound_aux hR hdir hC b hb hz (T - 0) 0 rfl (by omega) hb
    ⟨[], hnil, fun x hx => by show c.tape x = _; rw [hz x hx]; simp⟩ t (Nat.zero_le t) ht

end

end URTM.Three
