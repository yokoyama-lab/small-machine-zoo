/-
  3 状態 2 記号の URTM（段階 2e の 4）: **吸収的な戻り状態がある群 D の 4 類**（48 表）。**手書き**。

  段階 1 の閉包の検査（`closedR`）を「吸収的な状態の集合 D」つきに弱める（`closedRD`）。
  D は、D から出る規則がどれも D へ入り、D へ入る規則がどれも右へ動かない状態の集合（`doomOK`）。
  訪問が D の状態で b へ戻れば、以後の状態はずっと D にあり、ヘッドは二度と b より右へ出ない（`doom_stays`）。
  そこで、D の状態で戻った訪問の模様は閉包に入れなくてよい。それ以外は段階 1 と同じで、止まる実行の
  ヘッドは b + M 以下に居る（`right_boundD`）。左は段階 1 の証明書で有界なので、窓の配置の数で
  止まる歩数が抑えられる（`halts_iff_boundH`、上界は段階 1 と同じ `bound3`）。
  outlook の番号で class 8, 10, 35, 45 は、D = {1} または {2}、C = {[], [1]}、M = 2 で閉じる
  （空白 → 戻り状態が D の外・模様 1 → 戻り状態が D）。
  検査 `grpH es D`（Bool）: 表か鏡像の表で、左に段階 1 の証明書、右に D つきの証明書が立つ。
  主定理 `no_three_two_URTM_H`（`isExcH = isExcG && !grpH`）。例外は高々 336 表（`excHKeys_length`）。
-/
import URTMMeta.ThreeG

namespace URTM.Meta
open URTM URTM.TwoState URTM.Three

/-! ### 吸収的な状態の集合と、D つきの閉包の検査（計算） -/

/-- 状態の集合 D は吸収的: D から出る規則は D へ入り、D へ入る規則は右へ動かない。 -/
def doomOK (tbl : List Quint) (D : List Nat) : Bool :=
  tbl.all fun ρ => decide (ρ.p ∈ D → ρ.q ∈ D) && decide (ρ.q ∈ D → ρ.d ≠ Dir.R)

/-- 1 つの訪問の結果が C と M に収まる（D の状態で戻った訪問の模様は C に入らなくてよい）。 -/
def outOKD (D : List Nat) (C : List (List Nat)) (M : Nat) : VOut → Bool
  | VOut.ret q P _ mp => (D.contains q || C.contains P) && mp ≤ M
  | VOut.halt _ mp => mp ≤ M
  | VOut.div => true
  | VOut.unk => false

/-- **D つきの閉包の検査**: 空の模様が C にあり、C のどの模様・どの入り口状態の訪問も `outOKD`。 -/
def closedRD (tbl : List Quint) (D : List Nat) (C : List (List Nat)) (M : Nat) : Bool :=
  C.contains [] && C.all fun P => P.length ≤ M &&
    (entR tbl).all fun e => !(entOK tbl e P) || outOKD D C M (visit tbl e P)

/-- D つきの閉包を作る（`closureAux` の写しで、D の状態で戻った模様は足さない）。 -/
def closureAuxD (tbl : List Quint) (D : List Nat) : Nat → List (List Nat) → List (List Nat) → Nat →
    Option (List (List Nat) × Nat)
  | 0, _, _, _ => none
  | _ + 1, [], C, M => some (C, M)
  | fuel + 1, P :: work, C, M =>
    let outs := ((entR tbl).filter fun e => entOK tbl e P).map fun e => visit tbl e P
    if outs.any (· == VOut.unk) then none
    else
      let new := (outs.filterMap fun o => match o with
        | VOut.ret q P' _ _ => if D.contains q || C.contains P' then none else some P'
        | _ => none).eraseDups
      let M' := (outs.map outMp).foldl max (max M P.length)
      closureAuxD tbl D fuel (work ++ new) (C ++ new) M'

/-- D つきの右側の検査（D が吸収的で、閉包を作ってから閉じていることを確かめ直す）。 -/
def checkRD (tbl : List Quint) (D : List Nat) : Bool :=
  doomOK tbl D && match closureAuxD tbl D closureFuel [[]] [[]] 1 with
    | none => false
    | some (C, M) => closedRD tbl D C M

/-- 試す D の候補（空でない部分集合）。 -/
def doomSets : List (List Nat) := [[0], [1], [2], [0, 1], [0, 2], [1, 2], [0, 1, 2]]

/-! ### 健全性 -/

section
variable {tbl : List Quint} {c : QConf} {T : Nat}

theorem doomOK_spec {D : List Nat} (h : doomOK tbl D = true) :
    (∀ ρ ∈ tbl, ρ.p ∈ D → ρ.q ∈ D) ∧ (∀ ρ ∈ tbl, ρ.q ∈ D → ρ.d ≠ Dir.R) := by
  unfold doomOK at h
  rw [List.all_eq_true] at h
  refine ⟨fun ρ hρ => ?_, fun ρ hρ => ?_⟩
  · have := h ρ hρ
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact this.1
  · have := h ρ hρ
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact this.2

theorem closedRD_spec {D : List Nat} {C : List (List Nat)} {M : Nat} (h : closedRD tbl D C M = true) :
    [] ∈ C ∧ ∀ P ∈ C, ∀ e ∈ entR tbl, entOK tbl e P = true → outOKD D C M (visit tbl e P) = true := by
  unfold closedRD at h
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨by simpa using h1, fun P hP e he hok => ?_⟩
  have := (h2 P hP).2 e he
  rw [hok] at this; simpa using this

theorem checkRD_spec {D : List Nat} (h : checkRD tbl D = true) :
    doomOK tbl D = true ∧ ∃ C M, closedRD tbl D C M = true := by
  unfold checkRD at h
  obtain ⟨hD, h⟩ := Bool.and_eq_true_iff.mp h
  refine ⟨hD, ?_⟩
  cases hc : closureAuxD tbl D closureFuel [[]] [[]] 1 with
  | none => rw [hc] at h; simp at h
  | some CM => rw [hc] at h; exact ⟨CM.1, CM.2, h⟩

/-- **D に入ったら出ない**: 時刻 t₀ に状態が D にありヘッドが b 以下なら、以後ずっとそう。 -/
theorem doom_stays (hR : QHaltRun tbl c T) {D : List Nat} (hD1 : ∀ ρ ∈ tbl, ρ.p ∈ D → ρ.q ∈ D)
    (hD2 : ∀ ρ ∈ tbl, ρ.q ∈ D → ρ.d ≠ Dir.R) {b : Int} {t₀ : Nat}
    (hst : (qtr tbl c t₀).st ∈ D) (hpos : (qtr tbl c t₀).pos ≤ b) :
    ∀ n, t₀ + n ≤ T → (qtr tbl c (t₀ + n)).st ∈ D ∧ (qtr tbl c (t₀ + n)).pos ≤ b
  | 0, _ => ⟨hst, hpos⟩
  | n + 1, h => by
    obtain ⟨h1, h2⟩ := doom_stays hR hD1 hD2 hst hpos n (by omega)
    obtain ⟨ρ, hρ, hf, e1⟩ := qstep_some (hR.step (t₀ + n) (by omega))
    obtain ⟨_, hp, _⟩ := find?_spec hf
    have hq : ρ.q ∈ D := hD1 ρ hρ (by rw [hp]; exact h1)
    have hd := hD2 ρ hρ hq
    rw [show t₀ + (n + 1) = t₀ + n + 1 by omega, e1]
    refine ⟨hq, ?_⟩
    show move ρ.d (qtr tbl c (t₀ + n)).pos ≤ b
    cases hrd : ρ.d with
    | L => simp [move]; omega
    | Z => simp [move]; omega
    | R => exact absurd hrd hd

/-- D つきの閉包の検査の健全性（`right_bound_aux` の写しに、D で戻った場合を足したもの）。 -/
theorem right_boundD_aux (hR : QHaltRun tbl c T) (hdir : DirConsistent tbl) {D : List Nat}
    (hD : doomOK tbl D = true) {C : List (List Nat)} {M : Nat}
    (hC : closedRD tbl D C M = true) (b : Int) (hz : ∀ x, b < x → c.tape x = 0) :
    ∀ m t₀, T - t₀ = m → t₀ ≤ T → (qtr tbl c t₀).pos ≤ b → (∃ P ∈ C, PatAt tbl c b t₀ P) →
      ∀ t, t₀ ≤ t → t ≤ T → (qtr tbl c t).pos ≤ b + M := by
  obtain ⟨hnil, hvis⟩ := closedRD_spec hC
  obtain ⟨hD1, hD2⟩ := doomOK_spec hD
  intro m
  induction m using Nat.strongRecOn with
  | _ m ih =>
  intro t₀ hm ht₀ hle₀ ⟨P, hPC, hP⟩ t ht0 htT
  by_cases hex : ∃ u, t₀ < u ∧ u ≤ t ∧ b < (qtr tbl c u).pos
  · obtain ⟨u, hu1, hu2, hu3⟩ := hex
    obtain ⟨t₁, h1a, h1b, h1c, h1d⟩ := exists_first (fun u => b < (qtr tbl c u).pos) (u - (t₀ + 1))
      (t₀ + 1) (by rw [show t₀ + 1 + (u - (t₀ + 1)) = u by omega]; exact hu3)
    have hbelow : ∀ v, t₀ ≤ v → v < t₁ → (qtr tbl c v).pos ≤ b := by
      intro v hv1 hv2
      rcases Nat.eq_or_lt_of_le hv1 with rfl | hv1
      · exact hle₀
      · have := h1d v (by omega) hv2; omega
    obtain ⟨s, rfl⟩ : ∃ s, t₁ = s + 1 := ⟨t₁ - 1, by omega⟩
    have hPs := hR.pat_frozen (t₀ := t₀) (t₁ := s) (by omega) (by omega)
      (fun v h1 h2 => hbelow v h1 (by omega)) hP
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
    have hrun : ∀ n, s + 1 + n ≤ T → qrun tbl n (qtr tbl c (s + 1)) = some (qtr tbl c (s + 1 + n)) :=
      fun n hn => hR.run_at hn
    cases hv : visit tbl e P₀ with
    | unk => rw [hv] at hout; simp [outOKD] at hout
    | div =>
      rw [hv] at hspec
      obtain ⟨d, hd, _⟩ := hspec (T + 1 - (s + 1))
      rw [hR.run_from (s + 1) (by omega)] at hd; cases hd
    | halt k mp =>
      rw [hv] at hspec hout
      simp only [outOKD, decide_eq_true_eq] at hout
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
      simp only [outOKD, Bool.and_eq_true, Bool.or_eq_true, List.contains_iff_mem,
        decide_eq_true_eq] at hout
      obtain ⟨hP'C, hmp⟩ := hout
      obtain ⟨hback, hpos⟩ := hspec
      by_cases htk : t < s + 1 + k
      · have := hpos (t - (s + 1)) (by omega) _ (hrun (t - (s + 1)) (by omega))
        rw [show s + 1 + (t - (s + 1)) = t by omega] at this
        omega
      · have hkT : s + 1 + k ≤ T := by omega
        have hback' : qtr tbl c (s + 1 + k) = ⟨q, b, glue b (qtr tbl c (s + 1)).tape P'⟩ := by
          rw [hrun k hkT] at hback; exact Option.some.inj hback
        rcases hP'C with hqD | hP'C
        · -- D の状態で戻った: 以後ヘッドは b 以下
          have := doom_stays hR hD1 hD2 (b := b) (t₀ := s + 1 + k) (by rw [hback']; exact hqD)
            (by rw [hback']) (t - (s + 1 + k)) (by omega)
          rw [show s + 1 + k + (t - (s + 1 + k)) = t by omega] at this
          omega
        · have hk1 : 1 ≤ k := by
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
          refine ih (T - (s + 1 + k)) (by omega) (s + 1 + k) rfl hkT ?_ ⟨P', hP'C, ?_⟩ t (by omega) htT
          · rw [hback']
          · intro x hx; rw [hback']; show glue b _ P' x = _; unfold glue; rw [if_pos hx]
  · have : (qtr tbl c t).pos ≤ b := by
      rcases Nat.eq_or_lt_of_le ht0 with rfl | hlt
      · exact hle₀
      · exact Int.not_lt.mp fun hc => hex ⟨t, hlt, Nat.le_refl _, hc⟩
    omega

/-- **右側の有界性（D つき）**。 -/
theorem right_boundD (hR : QHaltRun tbl c T) (hdir : DirConsistent tbl) {D : List Nat}
    (hD : doomOK tbl D = true) {C : List (List Nat)} {M : Nat}
    (hC : closedRD tbl D C M = true) (b : Int) (hb : c.pos ≤ b) (hz : ∀ x, b < x → c.tape x = 0) :
    ∀ t, t ≤ T → (qtr tbl c t).pos ≤ b + M := by
  have hnil := (closedRD_spec hC).1
  intro t ht
  exact right_boundD_aux hR hdir hD hC b hz (T - 0) 0 rfl (by omega) hb
    ⟨[], hnil, fun x hx => by show c.tape x = _; rw [hz x hx]; simp⟩ t (Nat.zero_le t) ht

end

/-- **有界停止**（右が D つきの証明書、左が段階 1 の証明書。上界は `bound3`）。 -/
theorem halts_iff_boundH {tbl : List Quint} (hsrc : Src3 tbl) (hcl : QClosed tbl 2) (hdir : DirConsistent tbl)
    {D : List Nat} (hD : doomOK tbl D = true) {CR CL : List (List Nat)} {MR ML : Nat}
    (hRc : closedRD tbl D CR MR = true) (hLc : closedR (mirTbl tbl) CL ML = true)
    (c : QConf) (a b : Int) (ha : a ≤ c.pos) (hb : c.pos ≤ b)
    (hz : ∀ x, (x < a ∨ b < x) → c.tape x = 0) (h2 : ∀ x, c.tape x < 2) :
    QHalts tbl c ↔ qrun tbl (bound3 MR ML a b) c = none := by
  constructor
  · intro hH
    obtain ⟨T, hR⟩ := qhalts_haltRun hH
    have hr := right_boundD hR hdir hD hRc b hb (fun x hx => hz x (Or.inr hx))
    have hl := left_bound hR hdir hLc a ha (fun x hx => hz x (Or.inl hx))
    obtain ⟨W, hW⟩ : ∃ W : Nat, W = ((b + MR) - (a - ML) + 1).toNat := ⟨_, rfl⟩
    have hWi : (W : Int) = (b + MR) - (a - ML) + 1 := by rw [hW]; omega
    have hinw : ∀ t, t ≤ T → InWin 2 (a - ML) W (URTM.Three.toC2 (qtr tbl c t)) := by
      intro t ht
      refine ⟨hl t ht, by have := hr t ht; show (qtr tbl c t).pos < a - ML + W; omega, ?_,
        hR.tape_lt hcl h2 t ht⟩
      intro x hx
      show (qtr tbl c t).tape x = 0
      have := hR.cell_frozen x 0 t (by omega) (fun u _ h2 he => by
        have h1 := hl u (by omega); have h2' := hr u (by omega)
        unfold QP at he; rw [he] at h1 h2'; omega)
      rw [Nat.zero_add] at this
      rw [this]; exact hz x (by omega)
    have hTle : T ≤ csize 2 W := by
      rcases Nat.lt_or_ge (csize 2 W) T with hbig | hok
      · obtain ⟨i, j, hij, hjK, hq⟩ := pigeon (csize 2 W)
          (fun t => ccode 2 (a - ML) W (URTM.Three.toC2 (qtr tbl c t))) (fun t ht => ccode_lt (hinw t (by omega)))
        have he := ccode_inj (hinw i (by omega)) (hinw j (by omega)) hq
        exfalso
        apply hR.no_repeat i j hij (by omega)
        have si := hR.st_lt hsrc i (by omega)
        have sj := hR.st_lt hsrc j (by omega)
        unfold URTM.Three.toC2 at he
        injection he with h1 h2 h3
        have hst' := stDir_inj si sj h3
        cases hqi : qtr tbl c i
        cases hqj : qtr tbl c j
        rw [hqi, hqj] at h1 h2 hst'
        simp only at h1 h2 hst'
        rw [h1, h2, hst']
      · exact hok
    have := hR.dead
    exact qrun_none_mono tbl c (T + 1) _ this (by unfold bound3; rw [← hW]; omega)
  · intro h; exact ⟨_, h⟩

/-! ### Bool の検査 -/

/-- 左に段階 1 の証明書、右に D つきの証明書が立つ。 -/
def sideH (tbl : List Quint) : Bool := checkR (mirTbl tbl) && doomSets.any (checkRD tbl)

/-- **群 D の吸収的な戻り状態の 4 類の検査**: 表か、その鏡像が `sideH`。 -/
def grpH (es : List Nat) (D : List Dir) : Bool :=
  sideH (URTM.Three.realize es D) || sideH (mirTbl (URTM.Three.realize es D))

/-- 段階 2e の 4 の例外: `isExcG` の表のうち、この 4 類に当たらない表。 -/
def isExcH (es : List Nat) (D : List Dir) : Bool := isExcG es D && !grpH es D

theorem sideH_bound {tbl : List Quint} (hsrc : Src3 tbl) (hcl : QClosed tbl 2) (hdir : DirConsistent tbl)
    (h : sideH tbl = true) :
    ∃ MR ML : Nat, ∀ (c : QConf) (a b : Int), a ≤ c.pos → c.pos ≤ b →
      (∀ x, (x < a ∨ b < x) → c.tape x = 0) → (∀ x, c.tape x < 2) →
      (QHalts tbl c ↔ qrun tbl (bound3 MR ML a b) c = none) := by
  unfold sideH at h
  obtain ⟨hL, hc⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨CL, ML, hLc⟩ := checkR_spec hL
  obtain ⟨D, -, hc⟩ := List.any_eq_true.mp hc
  obtain ⟨hD, CR, MR, hRc⟩ := checkRD_spec hc
  exact ⟨MR, ML, fun c a b ha hb hz h2 => halts_iff_boundH hsrc hcl hdir hD hRc hLc c a b ha hb hz h2⟩

theorem sideH_mir_bound {tbl : List Quint} (hsrc : Src3 tbl) (hcl : QClosed tbl 2) (hdir : DirConsistent tbl)
    (h : sideH (mirTbl tbl) = true) :
    ∃ MR ML : Nat, ∀ (c : QConf) (a b : Int), a ≤ c.pos → c.pos ≤ b →
      (∀ x, (x < a ∨ b < x) → c.tape x = 0) → (∀ x, c.tape x < 2) →
      (QHalts tbl c ↔ qrun tbl (bound3 MR ML a b) c = none) := by
  rw [mirTbl_eq] at h
  obtain ⟨MR, ML, hb⟩ := sideH_bound (src3_mir hsrc) (closed_mir hcl) (dirConsistent_mir hdir) h
  refine ⟨MR, ML, fun c a b ha hb' hz h2 => ?_⟩
  have := hb (mirQ c) (-b) (-a) (by show -b ≤ -c.pos; omega) (by show -c.pos ≤ -a; omega)
    (fun x hx => by show c.tape (-x) = 0; exact hz (-x) (by omega)) (fun x => h2 (-x))
  rw [QHalts_mir, qrun_mir] at this
  have e : bound3 MR ML (-b) (-a) = bound3 MR ML a b := by
    unfold bound3; rw [show -a + (MR : Int) - (-b - ML) + 1 = b + MR - (a - ML) + 1 by omega]
  rw [e] at this
  rw [this]
  cases qrun tbl (bound3 MR ML a b) c <;> simp

theorem bnd3N_primrec (MR ML : Nat) : Primrec (bnd3N MR ML) :=
  (Primrec.nat_add.comp (csize_primrec.comp (Primrec.const 2)
    (Primrec.nat_add.comp (Primrec.nat_add.comp (Primrec.nat_add.comp Primrec.id (Primrec.const MR))
      (Primrec.const ML)) (Primrec.const 1))) (Primrec.const 1)).of_eq fun w => rfl

section
variable {tbl : List Quint} {q₀ q₁ q₂ sg : Nat}

/-- **4 類の有界停止**（任意の表の正規形）。 -/
theorem okH_bound (H : RTM32 tbl q₀ q₁ q₂ sg)
    (hok : grpH (absCodes q₀ q₁ q₂ sg tbl) (absDirs q₀ q₁ q₂ tbl) = true) :
    ∃ MR ML : Nat, ∀ (c : QConf) (m n : ℕ), -(m : ℤ) ≤ c.pos → c.pos ≤ (n : ℤ) →
      (∀ x, (x < -(m : ℤ) ∨ (n : ℤ) < x) → c.tape x = 0) → (∀ x, c.tape x < 2) →
      (QHalts (normT (tbl := tbl) (q₀ := q₀) (q₁ := q₁) (q₂ := q₂) (σ := sg)) c ↔
        qrun (normT (tbl := tbl) (q₀ := q₀) (q₁ := q₁) (q₂ := q₂) (σ := sg)) (bnd3N MR ML (m + n)) c
          = none) := by
  have hsrc := realize_src3 (absCodes q₀ q₁ q₂ sg tbl) (absDirs q₀ q₁ q₂ tbl)
  have hcl := realize_closed (absCodes q₀ q₁ q₂ sg tbl) (absDirs q₀ q₁ q₂ tbl)
  have hdir := realize_dir (absCodes q₀ q₁ q₂ sg tbl) (absDirs q₀ q₁ q₂ tbl)
  unfold grpH at hok
  obtain ⟨MR, ML, hb⟩ : ∃ MR ML : Nat, ∀ (c : QConf) (a b : Int), a ≤ c.pos → c.pos ≤ b →
      (∀ x, (x < a ∨ b < x) → c.tape x = 0) → (∀ x, c.tape x < 2) →
      (QHalts (URTM.Three.realize (absCodes q₀ q₁ q₂ sg tbl) (absDirs q₀ q₁ q₂ tbl)) c ↔
        qrun (URTM.Three.realize (absCodes q₀ q₁ q₂ sg tbl) (absDirs q₀ q₁ q₂ tbl)) (bound3 MR ML a b) c
          = none) := by
    rcases Bool.or_eq_true_iff.mp hok with h | h
    · exact sideH_bound hsrc hcl hdir h
    · exact sideH_mir_bound hsrc hcl hdir h
  refine ⟨MR, ML, fun c m n ha hb' hz h2 => ?_⟩
  rw [← bound3_eq]
  exact hb c _ _ ha hb' hz h2

/-- **3 状態 2 記号の RTM の停止問題は、U の ID の上で計算可能**（`isExcH` の表を除く）。 -/
theorem three_halting_computable_H (H : RTM32 tbl q₀ q₁ q₂ sg)
    (hne : isExcH (absCodes q₀ q₁ q₂ sg tbl) (absDirs q₀ q₁ q₂ tbl) = false) :
    ∃ f : ZID → Bool, Computable f ∧
      ∀ z, (∀ a ∈ z.2.1 ++ z.2.2, a = 0 ∨ a ∈ [sg]) → (ZHalts tbl z ↔ f z = true) := by
  cases hG : isExcG (absCodes q₀ q₁ q₂ sg tbl) (absDirs q₀ q₁ q₂ tbl) with
  | false => exact three_halting_computable_G H hG
  | true =>
    have hH : grpH (absCodes q₀ q₁ q₂ sg tbl) (absDirs q₀ q₁ q₂ tbl) = true := by
      unfold isExcH at hne; rw [hG] at hne; simpa using hne
    obtain ⟨MR, ML, hb⟩ := okH_bound H hH
    exact halting_computable_of_bound H (bnd3N_primrec MR ML) hb

/-- **定理（段階 2e の 4）: `isExcH` の表を除き、3 状態 2 記号の URTM は存在しない**（Morita Def. 7.1、
    U の記号集合 {0, sg} の上の ID への符号化）。 -/
theorem no_three_two_URTM_H (H : RTM32 tbl q₀ q₁ q₂ sg)
    (hne : isExcH (absCodes q₀ q₁ q₂ sg tbl) (absDirs q₀ q₁ q₂ tbl) = false) :
    ¬ IsUTM_MoritaOver tbl [sg] :=
  not_UTM_of_halting_computable (three_halting_computable_H H hne)

end

/-! ### 残る例外の数

段階 2e の 3 の例外の上界 384 表（`excGKeys`）のうち、`grpH` に当たる 48 表（4 類）の鍵を一覧 `h48Keys` に書き、
それらが `grpH` に当たることを kernel で確かめる。残る例外はその外の 336 表に**含まれる**（上界）。 -/

/-- `grpH` に当たる 48 表の鍵（Python で生成。下の `h48_grpH` が kernel で検査する）。 -/
def h48Keys : List Nat := [
  248294, 250646, 276324, 278676, 289512, 305976, 321458, 337922, 719060, 721460, 731584, 748384,
  776848, 779248, 791444, 808244, 1030222, 1030270, 1036940, 1036988, 1047898, 1048234, 1052240, 1052576,
  2206712, 2206760, 2213430, 2213478, 2224388, 2224724, 2228730, 2229066, 2366146, 2368546, 2378670, 2395470,
  2423934, 2426334, 2438530, 2455330, 2836572, 2838924, 2864602, 2866954, 2877790, 2894254, 2909736, 2926200
]

theorem h48_grpH : h48Keys.all (fun k => grpH (unkey k).1 (unkey k).2) = true := by decide +kernel

theorem h48_sub : h48Keys.all (fun k => excGKeys.contains k) = true := by decide +kernel

/-- 段階 2e の 4 の例外の鍵（の上界）。 -/
def excHKeys : List Nat := excGKeys.filter fun k => !h48Keys.contains k

/-- **段階 2e の 4 の例外の表（の上界）の一覧**。 -/
def excHTables : List (List Nat × List Dir) := excHKeys.map unkey

/-- **主定理の仮定が外れる表は一覧に載る**（符号 6 つ・向き 3 つの表について）。 -/
theorem mem_excHTables {es : List Nat} {D : List Dir} (h : ValidKey es D) (hx : isExcH es D = true) :
    (es, D) ∈ excHTables := by
  unfold isExcH at hx
  obtain ⟨hG, hH⟩ := Bool.and_eq_true_iff.mp hx
  obtain ⟨k, hk, he⟩ := List.mem_map.mp (mem_excGTables h hG)
  refine List.mem_map.mpr ⟨k, List.mem_filter.mpr ⟨hk, ?_⟩, he⟩
  cases hc : h48Keys.contains k
  · rfl
  · exfalso
    have := List.all_eq_true.mp h48_grpH k (List.contains_iff_mem.mp hc)
    rw [he] at this
    simp only [this, Bool.not_true] at hH
    exact Bool.false_ne_true hH

/-- **段階 2e の 4 の例外は高々 336 表**（384 − 48。kernel の評価）。 -/
theorem excHKeys_length : excHKeys.length = 336 := by decide +kernel

theorem excHTables_length : excHTables.length = 336 := by
  unfold excHTables; rw [List.length_map, excHKeys_length]

end URTM.Meta
