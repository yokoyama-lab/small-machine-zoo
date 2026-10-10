/-
  2 状態 RTM の停止問題の決定可能性 その 11: 単調な場合の上界と、**Morita の表についての主定理**。**手書き**。

    * `mono_time_bound` : 右単調な 2 状態の表で停止するなら、歩数は `monoBound` 未満
    * `decide2` / `decide2_correct` : **可逆（Def. 5.4）で状態が 2 つの任意の五つ組 TM** について、
      有限の初期配置から停止するかを決める全域の手続き。場合 (iii)（左右両方の移動がある）は
      方向状態機械 `ruleOf` へ移して `decideHalt`、そうでなければ単調（右単調か、鏡像で右単調）。
-/
import URTM.TSDMono

namespace URTM.TwoState

section MonoRun
variable {tbl : List Quint} {c : QConf} {T : Nat}

abbrev QP (tbl : List Quint) (c : QConf) (t : Nat) : Int := (qtr tbl c t).pos

theorem QHaltRun.tape_off (hR : QHaltRun tbl c T) (t : Nat) (ht : t < T) (x : Int)
    (hx : x ≠ QP tbl c t) : (qtr tbl c (t + 1)).tape x = (qtr tbl c t).tape x := by
  obtain ⟨r, _, _, e⟩ := qstep_some (hR.step t ht)
  rw [e]; exact write_off _ _ _ hx

theorem QHaltRun.cell_frozen (hR : QHaltRun tbl c T) (x : Int) :
    ∀ (t₁ n : Nat), t₁ + n ≤ T → (∀ u, t₁ ≤ u → u < t₁ + n → QP tbl c u ≠ x) →
      (qtr tbl c (t₁ + n)).tape x = (qtr tbl c t₁).tape x := by
  intro t₁ n
  induction n with
  | zero => intro _ _; rfl
  | succ n ih =>
    intro h hne
    rw [show t₁ + (n + 1) = (t₁ + n) + 1 by omega,
      hR.tape_off (t₁ + n) (by omega) x (fun he => hne (t₁ + n) (by omega) (by omega) he.symm)]
    exact ih (by omega) (fun u h1 h2 => hne u h1 (by omega))

theorem QHaltRun.mono_move (hm : RightMono tbl) (hR : QHaltRun tbl c T) (t : Nat) (ht : t < T) :
    QP tbl c (t + 1) = QP tbl c t ∨ QP tbl c (t + 1) = QP tbl c t + 1 :=
  mono_pos hm (hR.step t ht)

theorem QHaltRun.mono_ge (hm : RightMono tbl) (hR : QHaltRun tbl c T) :
    ∀ t, t ≤ T → c.pos ≤ QP tbl c t := by
  intro t
  induction t with
  | zero => intro _; exact Int.le_refl _
  | succ t ih => intro ht; have := hR.mono_move hm t (by omega); have := ih (by omega); omega

theorem QHaltRun.st_mem (hR : QHaltRun tbl c T) {q₀ q₁ : Nat}
    (hstates : ∀ r ∈ tbl, r.q = q₀ ∨ r.q = q₁) (hst : c.st = q₀ ∨ c.st = q₁) :
    ∀ t, t ≤ T → (qtr tbl c t).st = q₀ ∨ (qtr tbl c t).st = q₁ := by
  intro t
  induction t with
  | zero => intro _; exact hst
  | succ t _ =>
    intro ht
    obtain ⟨r, hr, _, e⟩ := qstep_some (hR.step t (by omega))
    rw [e]; exact hstates r hr

theorem QHaltRun.tape_lt (hR : QHaltRun tbl c T) {nsym : Nat} (hcl : QClosed tbl nsym)
    (hinit : ∀ x, c.tape x < nsym) : ∀ t, t ≤ T → ∀ x, (qtr tbl c t).tape x < nsym := by
  intro t
  induction t with
  | zero => intro _ x; exact hinit x
  | succ t ih =>
    intro ht x
    obtain ⟨r, hr, hf, e⟩ := qstep_some (hR.step t (by omega))
    rw [e]
    show write _ _ r.t x < nsym
    unfold write; split
    · obtain ⟨_, _, hrs⟩ := find?_spec hf
      exact hcl r hr (by rw [hrs]; exact ih (by omega) _)
    · exact ih (by omega) x

/-- 初めて p 以上に着く時刻。 -/
theorem QHaltRun.first_arrival (hm : RightMono tbl) (hR : QHaltRun tbl c T) (p : Int)
    (hp : c.pos < p) (t : Nat) (ht : t ≤ T) (hge : p ≤ QP tbl c t) :
    ∃ f, 1 ≤ f ∧ f ≤ t ∧ QP tbl c f = p ∧ ∀ u, u < f → QP tbl c u < p := by
  obtain ⟨f, _, hf2, hf3, hf4⟩ := exists_first (fun u => p ≤ QP tbl c u) t 0 (by simpa using hge)
  have hf0 : f ≠ 0 := by intro h; rw [h] at hf3; have : QP tbl c 0 = c.pos := rfl; omega
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  have hg := hf4 g (by omega) (by omega)
  have hm1 := hR.mono_move hm g (by omega)
  refine ⟨g + 1, by omega, by omega, by omega, fun u hu => ?_⟩
  have := hf4 u (by omega) hu; omega

/-- **右単調な実行はヘッドが b+2 を越えない**（停止するなら）。 -/
theorem QHaltRun.mono_pos_bound (hm : RightMono tbl) (hR : QHaltRun tbl c T) {q₀ q₁ : Nat}
    (hstates : ∀ r ∈ tbl, r.q = q₀ ∨ r.q = q₁) (hst : c.st = q₀ ∨ c.st = q₁) (b : Int)
    (hb : c.pos ≤ b) (hsupp : ∀ x, b < x → c.tape x = 0) :
    ∀ t, t ≤ T → QP tbl c t ≤ b + 2 := by
  intro t ht
  refine Classical.byContradiction fun hc => ?_
  have hge : b + 3 ≤ QP tbl c t := by omega
  -- p に初めて着いた時、p 以上はまだ空白
  have arrive : ∀ p : Int, b < p → p ≤ b + 3 →
      ∃ f, 1 ≤ f ∧ f ≤ t ∧ QP tbl c f = p ∧ ∀ x, p ≤ x → (qtr tbl c f).tape x = 0 := by
    intro p hp1 hp2
    obtain ⟨f, hf1, hf2, hf3, hf4⟩ := hR.first_arrival hm p (by omega) t ht (by omega)
    refine ⟨f, hf1, hf2, hf3, fun x hx => ?_⟩
    have := hR.cell_frozen x 0 f (by omega) (fun u _ h2 he => by have := hf4 u (by omega); omega)
    rw [Nat.zero_add] at this
    rw [this]; exact hsupp x (by omega)
  obtain ⟨f₁, _, _, hp₁, hb₁⟩ := arrive (b + 1) (by omega) (by omega)
  obtain ⟨f₂, _, _, hp₂, hb₂⟩ := arrive (b + 2) (by omega) (by omega)
  obtain ⟨f₃, _, _, hp₃, hb₃⟩ := arrive (b + 3) (by omega) (by omega)
  -- 着く時刻は増える（位置は減らないので）
  have mono_time : ∀ f f' : Nat, f ≤ T → f' ≤ T → QP tbl c f < QP tbl c f' → f < f' := by
    intro f f' hf hf' hlt
    refine Classical.byContradiction fun hn => ?_
    have : QP tbl c f' ≤ QP tbl c f := by
      have key : ∀ n, f' + n ≤ T → QP tbl c f' ≤ QP tbl c (f' + n) := by
        intro n
        induction n with
        | zero => intro _; exact Int.le_refl _
        | succ n ih => intro h; have := hR.mono_move hm (f' + n) (by omega); have := ih (by omega); rw [show f' + (n + 1) = f' + n + 1 by omega]; omega
      have := key (f - f') (by omega)
      rwa [show f' + (f - f') = f by omega] at this
    omega
  have h12 := mono_time f₁ f₂ (by omega) (by omega) (by omega)
  have h23 := mono_time f₂ f₃ (by omega) (by omega) (by omega)
  -- 同じ状態の 2 つの到着で逃走補題
  have esc : ∀ f f' : Nat, ∀ p p' : Int, f < f' → f' ≤ T → QP tbl c f = p → QP tbl c f' = p' →
      p < p' → (∀ x, p ≤ x → (qtr tbl c f).tape x = 0) →
      (∀ x, p' ≤ x → (qtr tbl c f').tape x = 0) →
      (qtr tbl c f).st = (qtr tbl c f').st → False := by
    intro f f' p p' hff hf' hp hp' hpp hbf hbf' hs
    have := qescape hm (qtr tbl c f) (qtr tbl c f') (f' - f) (p' - p) (by omega)
      (by have := hR.run_mid f (f' - f) (by omega); rwa [show f + (f' - f) = f' by omega] at this)
      hs.symm (by show QP tbl c f' = QP tbl c f + (p' - p); omega)
      (fun x hx => by
        have hx' : p' ≤ x := by have : QP tbl c f' ≤ x := hx; omega
        rw [hbf' x hx', hbf (x - (p' - p)) (by omega)])
    exact this _ (hR.run_from f (by omega))
  have s₁ := hR.st_mem hstates hst f₁ (by omega)
  have s₂ := hR.st_mem hstates hst f₂ (by omega)
  have s₃ := hR.st_mem hstates hst f₃ (by omega)
  by_cases e12 : (qtr tbl c f₁).st = (qtr tbl c f₂).st
  · exact esc f₁ f₂ (b + 1) (b + 2) h12 (by omega) hp₁ hp₂ (by omega) hb₁ hb₂ e12
  · by_cases e23 : (qtr tbl c f₂).st = (qtr tbl c f₃).st
    · exact esc f₂ f₃ (b + 2) (b + 3) h23 (by omega) hp₂ hp₃ (by omega) hb₂ hb₃ e23
    · have e13 : (qtr tbl c f₁).st = (qtr tbl c f₃).st := by
        rcases s₁ with h1 | h1 <;> rcases s₂ with h2 | h2 <;> rcases s₃ with h3 | h3 <;>
          simp_all
      exact esc f₁ f₃ (b + 1) (b + 3) (by omega) (by omega) hp₁ hp₃ (by omega) hb₁ hb₃ e13

end MonoRun

/-- 五つ組の配置を窓の番号へ（状態 q₀ を L、それ以外を R として符号化）。 -/
def qConf2 (q₀ : Nat) (d : QConf) : Conf2 := ⟨d.tape, d.pos, if d.st = q₀ then Dir.L else Dir.R⟩

def monoBound (nsym : Nat) (a b : Int) : Nat := csize nsym (b - a + 3).toNat

theorem QHaltRun.mono_time_bound {tbl : List Quint} {c : QConf} {T : Nat} (hm : RightMono tbl)
    (hR : QHaltRun tbl c T) {q₀ q₁ : Nat} (hne : q₀ ≠ q₁)
    (hstates : ∀ r ∈ tbl, r.q = q₀ ∨ r.q = q₁) (hst : c.st = q₀ ∨ c.st = q₁)
    {nsym : Nat} (hcl : QClosed tbl nsym) (hinit : ∀ x, c.tape x < nsym) (a b : Int)
    (ha : a ≤ c.pos) (hb : c.pos ≤ b) (hsupp : ∀ x, (x < a ∨ b < x) → c.tape x = 0) :
    T < monoBound nsym a b := by
  have hpb := hR.mono_pos_bound hm hstates hst b hb (fun x hx => hsupp x (Or.inr hx))
  have hge := hR.mono_ge hm
  obtain ⟨W, hW⟩ : ∃ W : Nat, W = (b - a + 3).toNat := ⟨_, rfl⟩
  have hWi : (W : Int) = b - a + 3 := by rw [hW]; omega
  have hinw : ∀ t, t ≤ T → InWin nsym a W (qConf2 q₀ (qtr tbl c t)) := by
    intro t ht
    refine ⟨by have := hge t ht; show a ≤ QP tbl c t; omega,
      by have := hpb t ht; show QP tbl c t < a + W; omega, ?_, hR.tape_lt hcl hinit t ht⟩
    intro x hx
    show (qtr tbl c t).tape x = 0
    have := hR.cell_frozen x 0 t (by omega) (fun u _ h2 he => by
      have h1 := hge u (by omega); have h2' := hpb u (by omega)
      rw [he] at h1 h2'; omega)
    rw [Nat.zero_add] at this
    rw [this]; exact hsupp x (by omega)
  unfold monoBound
  rw [← hW]
  refine Classical.byContradiction fun hbig => ?_
  obtain ⟨i, j, hij, hjK, hq⟩ := pigeon (csize nsym W)
    (fun t => ccode nsym a W (qConf2 q₀ (qtr tbl c t))) (fun t ht => ccode_lt (hinw t (by omega)))
  have he := ccode_inj (hinw i (by omega)) (hinw j (by omega)) hq
  apply hR.no_repeat i j hij (by omega)
  have si := hR.st_mem hstates hst i (by omega)
  have sj := hR.st_mem hstates hst j (by omega)
  unfold qConf2 at he
  injection he with h1 h2 h3
  have hst' : (qtr tbl c i).st = (qtr tbl c j).st := by
    rcases si with hi | hi <;> rcases sj with hj | hj <;> simp_all
  cases hqi : qtr tbl c i
  cases hqj : qtr tbl c j
  rw [hqi, hqj] at h1 h2 hst'
  simp only at h1 h2 hst'
  rw [h1, h2, hst']

/-! ## 鏡像（左単調 → 右単調） -/

def mirQuint (r : Quint) : Quint := { r with d := flipD r.d }
def mirT (tbl : List Quint) : List Quint := tbl.map mirQuint
def mirQ (c : QConf) : QConf := ⟨c.st, -c.pos, fun x => c.tape (-x)⟩

theorem find?_mirT (tbl : List Quint) (p s : Nat) :
    find? (mirT tbl) p s = (find? tbl p s).map mirQuint := by
  unfold find? mirT
  rw [List.find?_map]
  rfl

theorem qstep_mir (tbl : List Quint) (c : QConf) :
    qstep (mirT tbl) (mirQ c) = (qstep tbl c).map mirQ := by
  have hread : (mirQ c).tape (mirQ c).pos = c.tape c.pos := by
    show c.tape (-(-c.pos)) = _; rw [Int.neg_neg]
  unfold qstep
  rw [hread, show (mirQ c).st = c.st from rfl, find?_mirT]
  cases find? tbl c.st (c.tape c.pos) with
  | none => rfl
  | some r =>
    show some _ = some (mirQ _)
    congr 1
    show (⟨r.q, move (flipD r.d) (-c.pos), write (fun x => c.tape (-x)) (-c.pos) r.t⟩ : QConf)
      = ⟨r.q, -(move r.d c.pos), fun x => write c.tape c.pos r.t (-x)⟩
    rw [move_mir]
    congr 1
    funext x; unfold write
    by_cases h : x = -c.pos
    · have h' : -x = c.pos := by omega
      simp [h, h']
    · have h' : ¬ -x = c.pos := by omega
      simp [h, h']

theorem qrun_mir (tbl : List Quint) :
    ∀ (n : Nat) (c : QConf), qrun (mirT tbl) n (mirQ c) = (qrun tbl n c).map mirQ := by
  intro n
  induction n with
  | zero => intro c; rfl
  | succ n ih =>
    intro c
    cases hs : qstep tbl c with
    | none =>
      have hs' : qstep (mirT tbl) (mirQ c) = none := by rw [qstep_mir, hs]; rfl
      rw [qrun_succ_none _ n hs', qrun_succ_none _ n hs]; rfl
    | some c' =>
      have hs' : qstep (mirT tbl) (mirQ c) = some (mirQ c') := by rw [qstep_mir, hs]; rfl
      rw [qrun_succ_some _ n hs', qrun_succ_some _ n hs, ih]

theorem QHalts_mir (tbl : List Quint) (c : QConf) :
    QHalts (mirT tbl) (mirQ c) ↔ QHalts tbl c := by
  constructor
  · rintro ⟨n, hn⟩
    rw [qrun_mir] at hn
    exact ⟨n, by cases h : qrun tbl n c <;> simp_all⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, by rw [qrun_mir, hn]; rfl⟩

theorem mem_mirT {tbl : List Quint} {r : Quint} (h : r ∈ mirT tbl) :
    ∃ r₀ ∈ tbl, r = mirQuint r₀ := by
  unfold mirT at h
  obtain ⟨r₀, h1, h2⟩ := List.mem_map.mp h
  exact ⟨r₀, h1, h2.symm⟩

/-! ## 主定理 -/

/-- 単調な表の判定（ちょうど `bound` 歩回す）。 -/
def decideMono (tbl : List Quint) (nsym : Nat) (a b : Int) (c : QConf) : Bool :=
  (qrun tbl (monoBound nsym a b) c).isNone

theorem decideMono_correct {tbl : List Quint} (hm : RightMono tbl) {q₀ q₁ : Nat} (hne : q₀ ≠ q₁)
    (hstates : ∀ r ∈ tbl, r.q = q₀ ∨ r.q = q₁) {nsym : Nat} (hcl : QClosed tbl nsym)
    (a b : Int) (c : QConf) (hst : c.st = q₀ ∨ c.st = q₁) (hinit : ∀ x, c.tape x < nsym)
    (ha : a ≤ c.pos) (hb : c.pos ≤ b) (hsupp : ∀ x, (x < a ∨ b < x) → c.tape x = 0) :
    decideMono tbl nsym a b c = true ↔ QHalts tbl c := by
  constructor
  · intro h
    unfold decideMono at h
    cases hr : qrun tbl (monoBound nsym a b) c with
    | none => exact ⟨_, hr⟩
    | some x => rw [hr] at h; exact absurd h (by simp)
  · intro h
    obtain ⟨T, hR⟩ := qhalts_haltRun h
    have hT := hR.mono_time_bound hm hne hstates hst hcl hinit a b ha hb hsupp
    have := qrun_none_mono tbl c (T + 1) (monoBound nsym a b) hR.dead (by omega)
    unfold decideMono; rw [this]; rfl

/-- **決定手続き（Morita の表そのもの）**。 -/
def decide2 (tbl : List Quint) (q₀ q₁ nsym : Nat) (a b : Int) (c : QConf) : Bool :=
  match tbl.find? (fun r => r.d == Dir.L) with
  | some rl =>
    if tbl.any (fun r => r.d == Dir.R) then
      decideHalt (ruleOf tbl rl.q (if rl.q = q₀ then q₁ else q₀)) nsym a b (toC2 rl.q c)
    else decideMono (mirT tbl) nsym (-b) (-a) (mirQ c)
  | none => decideMono tbl nsym a b c

/-- **主定理**: 可逆（Morita Def. 5.4）で状態が q₀, q₁ の 2 つだけの五つ組 TM について、
    有限の初期配置（窓 [a,b] の外は空白）から停止するかを `decide2` が正しく判定する。
    停止は「適用できる規則が無い」。記号は nsym 未満。 -/
theorem decide2_correct (tbl : List Quint) (hrev : reversible tbl = true) (q₀ q₁ : Nat)
    (hne : q₀ ≠ q₁) (hstates : ∀ r ∈ tbl, r.q = q₀ ∨ r.q = q₁) (nsym : Nat)
    (hcl : QClosed tbl nsym) (a b : Int) (c : QConf) (hst : c.st = q₀ ∨ c.st = q₁)
    (hinit : ∀ x, c.tape x < nsym) (hab : a ≤ b) (ha : a ≤ c.pos) (hb : c.pos ≤ b)
    (hsupp : ∀ x, (x < a ∨ b < x) → c.tape x = 0) :
    decide2 tbl q₀ q₁ nsym a b c = true ↔ QHalts tbl c := by
  unfold decide2
  cases hL : tbl.find? (fun r => r.d == Dir.L) with
  | none =>
    -- 左へ動く規則が無い: 右単調
    have hm : RightMono tbl := by
      intro r hr hd
      have := List.find?_eq_none.mp hL r hr
      simp [hd] at this
    exact decideMono_correct hm hne hstates hcl a b c hst hinit ha hb hsupp
  | some rl =>
    have hrl := List.mem_of_find?_eq_some hL
    have hrld : rl.d = Dir.L := by have := List.find?_some hL; simpa using this
    simp only
    by_cases hR : tbl.any (fun r => r.d == Dir.R) = true
    · rw [if_pos hR]
      -- 場合 (iii)
      obtain ⟨rr, hrr, hrrd⟩ := List.any_eq_true.mp hR
      have hrrd' : rr.d = Dir.R := by simpa using hrrd
      let qL := rl.q
      let qR := if rl.q = q₀ then q₁ else q₀
      have hqLmem := hstates rl hrl
      have hneLR : qL ≠ qR := by
        show rl.q ≠ (if rl.q = q₀ then q₁ else q₀)
        by_cases h : rl.q = q₀
        · rw [if_pos h, h]; exact hne
        · rw [if_neg h]; exact h
      have hmemLR : ∀ q, (q = q₀ ∨ q = q₁) → (q = qL ∨ q = qR) := by
        intro q hq
        show q = rl.q ∨ q = (if rl.q = q₀ then q₁ else q₀)
        by_cases h : rl.q = q₀
        · rw [if_pos h]; rcases hq with hq | hq
          · left; rw [hq, h]
          · right; exact hq
        · rw [if_neg h]; rcases hq with hq | hq
          · right; exact hq
          · left; rcases hqLmem with h' | h'
            · exact absurd h' h
            · rw [hq, h']
      have hrrq : rr.q = qR := by
        rcases hmemLR rr.q (hstates rr hrr) with h | h
        · exfalso
          have := same_next_state_same_dir hrev hrr hrl h
          rw [hrrd', hrld] at this; exact Dir.noConfusion this
        · exact h
      have h3 : Case3 tbl qL qR :=
        ⟨hrev, hneLR, fun r hr => hmemLR r.q (hstates r hr), ⟨rl, hrl, rfl, hrld⟩,
          ⟨rr, hrr, hrrq, hrrd'⟩⟩
      exact case3_decidable h3 hcl a b c (hmemLR c.st hst) hinit hab ha hb hsupp
    · rw [if_neg hR]
      -- 右へ動く規則が無い: 鏡像で右単調
      have hm : RightMono (mirT tbl) := by
        intro r hr hd
        obtain ⟨r₀, hr₀, rfl⟩ := mem_mirT hr
        have hd0 : r₀.d = Dir.R := by
          unfold mirQuint at hd; simp only at hd
          cases h : r₀.d <;> rw [h] at hd <;> simp [flipD] at hd ⊢
        exact hR (List.any_eq_true.mpr ⟨r₀, hr₀, by simp [hd0]⟩)
      rw [← QHalts_mir]
      exact decideMono_correct hm hne
        (fun r hr => by obtain ⟨r₀, hr₀, rfl⟩ := mem_mirT hr; exact hstates r₀ hr₀)
        (fun r hr hs => by
          obtain ⟨r₀, hr₀, rfl⟩ := mem_mirT hr
          exact hcl r₀ hr₀ hs)
        (-b) (-a) (mirQ c) hst (fun x => hinit _) (by show -b ≤ -c.pos; omega)
        (by show -c.pos ≤ -a; omega)
        (fun x hx => by show c.tape (-x) = 0; exact hsupp (-x) (by omega))

end URTM.TwoState
