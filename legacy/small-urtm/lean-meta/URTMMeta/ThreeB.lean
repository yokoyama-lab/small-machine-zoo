/-
  3 状態 2 記号の URTM（段階 2b）その 3: **群 B（初めにしか居られない状態がある表）**。**手書き**。

  状態 e へ入る規則がどれも e 自身から出る（`SelfOnly`）とする。e に居続けるあいだ、ヘッドは同じ向きに
  動き続ける（同じ状態へ入る規則は同じ向き `DirConsistent`）。
    * 右へ動く場合: 窓の右端を出ると空白しか読まないので、そこでも e に留まるなら永久に右へ進み、止まらない
      （`run_right_forever`）。よって止まる実行は 幅 歩以内に e を離れる（`stay_right`）。左は鏡像（`stay_left`）。
    * 動かない場合: 同じマスの記号は 0 か 1 なので、3 つの時刻のどれか 2 つで配置が一致し、止まらない
      （`stay_zero`）。
  e を離れた後は戻らず、残りの 2 状態の RTM として動く（`halts_tail`）。

  主定理 `no_three_two_URTM_B`: 段階 2a の例外（`isExc`）のうち、初めにしか居られない状態がある表（`grpB`。
  入る規則の無い状態を含むので群 A を含む）を例外から外す（`isExcB es D = isExc es D && !grpB es D`）。
-/
import URTMMeta.ThreeA

namespace URTM.Meta
open URTM URTM.TwoState URTM.Three

/-! ### e に居続ける実行 -/

/-- 状態 e で空白を読むと右へ動いて e に留まる規則があるなら、ヘッドから右がすべて空白の配置からは
    永久に右へ進み、止まらない。 -/
theorem run_right_forever {tbl : List Quint} {e : Nat} {r : Quint} (hf : find? tbl e 0 = some r)
    (hq : r.q = e) (hd : r.d = Dir.R) :
    ∀ n (x : QConf), x.st = e → (∀ y, x.pos ≤ y → x.tape y = 0) → qrun tbl n x ≠ none := by
  intro n
  induction n with
  | zero => intro x _ _; simp [qrun]
  | succ n ih =>
    intro x hx hz
    have hs : qstep tbl x = some ⟨r.q, move r.d x.pos, write x.tape x.pos r.t⟩ := by
      unfold qstep; rw [hx, hz x.pos (Int.le_refl _), hf]
    rw [qrun_succ_some tbl n hs]
    refine ih _ hq (fun y hy => ?_)
    have hy' : x.pos + 1 ≤ y := by rw [hd] at hy; exact hy
    show write x.tape x.pos r.t y = 0
    rw [write_off _ _ _ (by omega)]; exact hz y (by omega)

/-- 右へ動いて e に入る規則があり、時刻 0..N のあいだずっと e に居る止まる実行では、N は窓の右端までの
    距離以下（右端を出た後も e に留まるなら止まらない）。 -/
theorem stay_right {tbl : List Quint} {e : Nat} (hdir : DirConsistent tbl) {c : QConf} {T : Nat}
    (hR : QHaltRun tbl c T) {b : Int} (hb : c.pos ≤ b) (hz : ∀ x, b < x → c.tape x = 0)
    {N : Nat} (hNT : N ≤ T) (hst : ∀ k, k ≤ N → (qtr tbl c k).st = e)
    {r₀ : Quint} (hr₀ : r₀ ∈ tbl) (hq₀ : r₀.q = e) (hd₀ : r₀.d = Dir.R) :
    N ≤ (b + 1 - c.pos).toNat := by
  rcases Nat.lt_or_ge (b + 1 - c.pos).toNat N with hlt | hge
  swap
  · exact hge
  exfalso
  obtain ⟨j, hj⟩ : ∃ j : Nat, j = (b + 1 - c.pos).toNat := ⟨_, rfl⟩
  rw [← hj] at hlt
  -- 時刻 N までの各歩は右へ 1
  have hmove : ∀ t, t < N → (qtr tbl c (t + 1)).pos = (qtr tbl c t).pos + 1 := by
    intro t ht
    obtain ⟨r, hr, _, he⟩ := qstep_some (hR.step t (by omega))
    have hq : r.q = e := by have := hst (t + 1) (by omega); rw [he] at this; exact this
    have hd : r.d = Dir.R := by rw [hdir r hr r₀ hr₀ (hq.trans hq₀.symm), hd₀]
    rw [he, hd]; rfl
  have hpos : ∀ t, t ≤ N → (qtr tbl c t).pos = c.pos + t := by
    intro t
    induction t with
    | zero => intro _; show c.pos = c.pos + ((0 : Nat) : Int); omega
    | succ t ih => intro ht; rw [hmove t (by omega), ih (by omega)]; omega
  -- 時刻 j の配置: 状態 e、位置 b + 1、b より右は空白
  have hxpos : (qtr tbl c j).pos = b + 1 := by rw [hpos j (by omega)]; omega
  have hxz : ∀ y, b < y → (qtr tbl c j).tape y = 0 := by
    intro y hy
    have := hR.cell_frozen y 0 j (by omega) (fun u _ hu he => by
      have := hpos u (by omega); unfold QP at he; omega)
    rw [Nat.zero_add] at this
    rw [this]; exact hz y hy
  -- 時刻 j の歩は、e で空白を読み、右へ動いて e に留まる
  obtain ⟨r, hr, hf, he⟩ := qstep_some (hR.step j (by omega))
  have hq : r.q = e := by have := hst (j + 1) (by omega); rw [he] at this; exact this
  have hd : r.d = Dir.R := by rw [hdir r hr r₀ hr₀ (hq.trans hq₀.symm), hd₀]
  rw [hst j (by omega), hxpos, hxz (b + 1) (by omega)] at hf
  exact run_right_forever hf hq hd (T + 1 - j) (qtr tbl c j) (hst j (by omega))
    (fun y hy => hxz y (by omega)) (hR.run_from j (by omega))

/-- `stay_right` の鏡像。 -/
theorem stay_left {tbl : List Quint} {e : Nat} (hdir : DirConsistent tbl) {c : QConf} {T : Nat}
    (hR : QHaltRun tbl c T) {a : Int} (ha : a ≤ c.pos) (hz : ∀ x, x < a → c.tape x = 0)
    {N : Nat} (hNT : N ≤ T) (hst : ∀ k, k ≤ N → (qtr tbl c k).st = e)
    {r₀ : Quint} (hr₀ : r₀ ∈ tbl) (hq₀ : r₀.q = e) (hd₀ : r₀.d = Dir.L) :
    N ≤ (c.pos - a + 1).toNat := by
  have h := stay_right (e := e) (dirConsistent_mir hdir) hR.mir (b := -a) (by show -c.pos ≤ -a; omega)
    (fun x hx => by show c.tape (-x) = 0; exact hz (-x) (by omega)) hNT
    (fun k hk => by rw [qtr_mir]; exact hst k hk) (r₀ := mirQuint r₀)
    (List.mem_map.mpr ⟨r₀, hr₀, rfl⟩) hq₀ (by show flipD r₀.d = Dir.R; rw [hd₀]; rfl)
  have e1 : -a + 1 - (mirQ c).pos = c.pos - a + 1 := by show -a + 1 - (-c.pos) = _; omega
  rw [e1] at h; exact h

/-- 動かずに e に入る規則があるとき、時刻 0, 1, 2 のすべてで e に居る実行は止まらない
    （同じマスの記号は 0 か 1 なので、どれか 2 つの時刻で配置が一致する）。 -/
theorem stay_zero {tbl : List Quint} {e : Nat} (hdir : DirConsistent tbl) (hcl : QClosed tbl 2)
    {c : QConf} {T : Nat} (hR : QHaltRun tbl c T) (h2 : ∀ x, c.tape x < 2) (hT : 2 ≤ T)
    (hst : ∀ k, k ≤ 2 → (qtr tbl c k).st = e)
    {r₀ : Quint} (hr₀ : r₀ ∈ tbl) (hq₀ : r₀.q = e) (hd₀ : r₀.d = Dir.Z) : False := by
  obtain ⟨ra, hra, hfa, hea⟩ := qstep_some (hR.step 0 (by omega))
  obtain ⟨rb, hrb, hfb, heb⟩ := qstep_some (hR.step 1 (by omega))
  have hqa : ra.q = e := by have := hst 1 (by omega); rw [hea] at this; exact this
  have hqb : rb.q = e := by have := hst 2 (by omega); rw [heb] at this; exact this
  have hda : ra.d = Dir.Z := by rw [hdir ra hra r₀ hr₀ (hqa.trans hq₀.symm), hd₀]
  have hdb : rb.d = Dir.Z := by rw [hdir rb hrb r₀ hr₀ (hqb.trans hq₀.symm), hd₀]
  have h0 : qtr tbl c 0 = c := rfl
  have hc0 : c = ⟨e, c.pos, c.tape⟩ := by
    have := hst 0 (by omega); rw [h0] at this
    cases c; simp only at this; subst this; rfl
  have e1 : qtr tbl c 1 = ⟨e, c.pos, write c.tape c.pos ra.t⟩ := by
    rw [hea, hqa, hda, h0]; rfl
  have e2 : qtr tbl c 2 = ⟨e, c.pos, write (write c.tape c.pos ra.t) c.pos rb.t⟩ := by
    rw [heb, hqb, hdb, e1]; rfl
  have u0 := h2 c.pos
  have u1 : ra.t < 2 := hcl ra hra (by rw [(find?_spec hfa).2.2]; exact h2 _)
  have u2 : rb.t < 2 :=
    hcl rb hrb (by rw [(find?_spec hfb).2.2]; exact hR.tape_lt hcl h2 1 (by omega) _)
  have wsame : ∀ (t : Int → Nat) (p : Int), write t p (t p) = t := by
    intro t p; funext x; unfold write; split
    · rename_i h; rw [h]
    · rfl
  have wwrite : ∀ (t : Int → Nat) (p : Int) (v w : Nat), write (write t p v) p w = write t p w := by
    intro t p v w; funext x; unfold write; split <;> rfl
  rcases (show ra.t = c.tape c.pos ∨ rb.t = ra.t ∨ rb.t = c.tape c.pos by omega) with h | h | h
  · -- 時刻 1 の配置は時刻 0 と同じ
    refine hR.no_repeat 0 1 (by omega) (by omega) ?_
    rw [e1, h0, h, wsame]; exact hc0
  · -- 時刻 2 の配置は時刻 1 と同じ
    refine hR.no_repeat 1 2 (by omega) (by omega) ?_
    rw [e1, e2, wwrite, h]
  · -- 時刻 2 の配置は時刻 0 と同じ
    refine hR.no_repeat 0 2 (by omega) (by omega) ?_
    rw [e2, h0, wwrite, h, wsame]; exact hc0

/-- e に居続けられる歩数の上界（窓の幅 + 1）。 -/
def stayK (a b : Int) : Nat := (b - a + 1).toNat + 1

/-- **止まる実行は 幅 + 1 歩以内に e を離れる**（窓 [a, b] の外は空白、記号は 0, 1）。 -/
theorem leave_within {tbl : List Quint} {e : Nat} (hdir : DirConsistent tbl) (hcl : QClosed tbl 2)
    {c : QConf} {T : Nat} (hR : QHaltRun tbl c T) {a b : Int} (ha : a ≤ c.pos) (hb : c.pos ≤ b)
    (hsupp : ∀ x, (x < a ∨ b < x) → c.tape x = 0) (h2 : ∀ x, c.tape x < 2)
    (hT : stayK a b ≤ T) : ∃ k, k ≤ stayK a b ∧ (qtr tbl c k).st ≠ e := by
  apply Classical.byContradiction
  intro hno
  have hst : ∀ k, k ≤ stayK a b → (qtr tbl c k).st = e :=
    fun k hk => Classical.byContradiction fun h => hno ⟨k, hk, h⟩
  unfold stayK at hT hst
  obtain ⟨r₀, hr₀, _, he₀⟩ := qstep_some (hR.step 0 (by omega))
  have hq₀ : r₀.q = e := by have := hst 1 (by omega); rw [he₀] at this; exact this
  cases hd : r₀.d with
  | R =>
    have := stay_right hdir hR hb (fun x hx => hsupp x (Or.inr hx)) hT hst hr₀ hq₀ hd
    omega
  | L =>
    have := stay_left hdir hR ha (fun x hx => hsupp x (Or.inl hx)) hT hst hr₀ hq₀ hd
    omega
  | Z => exact stay_zero hdir hcl hR h2 (by omega) (fun k hk => hst k (by omega)) hr₀ hq₀ hd

/-- **群 B の有界停止**（`QConf` の上）: 状態 e が初めにしか居られず（`SelfOnly`）、e から出る規則を除いた表が
    2 状態の RTM なら、窓 [a, b] の外が空白で記号が 0, 1 の配置から止まる実行は
    `K + (bnd 2 (a − K) (b + K) + 1)` 歩以内に止まる（K = 幅 + 1。始状態は任意）。 -/
theorem halts_selfOnly {tbl : List Quint} {e qa qb : Nat} (hT : TwoStateRTM (dropFrom e tbl) qa qb e)
    (hso : SelfOnly tbl e) (hdir : DirConsistent tbl) (hcl : QClosed tbl 2) (a b : Int) (c : QConf)
    (hinit : ∀ x, c.tape x < 2) (ha : a ≤ c.pos) (hb : c.pos ≤ b)
    (hsupp : ∀ x, (x < a ∨ b < x) → c.tape x = 0) :
    QHalts tbl c ↔
      qrun tbl (stayK a b + (bnd 2 (a - stayK a b) (b + stayK a b) + 1)) c = none := by
  constructor
  · intro hH
    obtain ⟨T, hR⟩ := qhalts_haltRun hH
    rcases Nat.lt_or_ge T (stayK a b) with hlt | hge
    · exact qrun_none_mono tbl c (T + 1) _ hR.dead (by omega)
    · obtain ⟨k, hk, hne⟩ := leave_within hdir hcl hR ha hb hsupp hinit hge
      exact halts_tail hT hso hcl (hR.run k (by omega)) hne hk hinit ha hb hsupp hH
  · intro h; exact ⟨_, h⟩

section
variable {tbl : List Quint} {q₀ q₁ q₂ sg : Nat}

/-- 窓の幅だけで書いた群 B の上界。 -/
def bndB (w : Nat) : Nat := (w + 2) + (bndN 2 (3 * w + 4) + 1)

theorem bndB_primrec : Primrec bndB := by
  have h := Primrec.nat_add.comp (Primrec.nat_add.comp Primrec.id (Primrec.const 2))
    (Primrec.nat_add.comp
      (bndN_primrec.comp (Primrec.const 2)
        (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 3) Primrec.id) (Primrec.const 4)))
      (Primrec.const 1))
  exact h.of_eq fun w => rfl

/-- **群 B の有界停止**（正規形の表）。 -/
theorem selfOnly_bound (H : RTM32 tbl q₀ q₁ q₂ sg) {e : Nat} (he : e < 3)
    (hso : selfOnly (normT (tbl := tbl) (q₀ := q₀) (q₁ := q₁) (q₂ := q₂) (σ := sg)) e = true)
    (c : QConf) (m n : ℕ) (ha : -(m : ℤ) ≤ c.pos) (hb : c.pos ≤ (n : ℤ))
    (hz : ∀ x, (x < -(m : ℤ) ∨ (n : ℤ) < x) → c.tape x = 0) (h2 : ∀ x, c.tape x < 2) :
    QHalts (normT (tbl := tbl) (q₀ := q₀) (q₁ := q₁) (q₂ := q₂) (σ := sg)) c ↔
      qrun (normT (tbl := tbl) (q₀ := q₀) (q₁ := q₁) (q₂ := q₂) (σ := sg)) (bndB (m + n)) c = none := by
  obtain ⟨qa, qb, hT⟩ := normT_twoState H he
  have h := halts_selfOnly hT (selfOnly_spec hso) (realize_dir _ _) (realize_closed _ _)
    (-(m : ℤ)) (n : ℤ) c h2 ha hb hz
  have ek : stayK (-(m : ℤ)) (n : ℤ) = m + n + 2 := by unfold stayK; omega
  have e1 : -(m : ℤ) - ((m + n + 2 : ℕ) : ℤ) = -((m + (m + n + 2) : ℕ) : ℤ) := by omega
  have e2 : (n : ℤ) + ((m + n + 2 : ℕ) : ℤ) = ((n + (m + n + 2) : ℕ) : ℤ) := by omega
  have e3 : m + (m + n + 2) + (n + (m + n + 2)) = 3 * (m + n) + 4 := by omega
  rw [ek, e1, e2, bnd_eq, e3] at h
  exact h

/-- 正規形の表 (es, D) に、初めにしか居られない状態がある（群 B。入る規則の無い状態＝群 A を含む）。 -/
def grpB (es : List Nat) (D : List Dir) : Bool := (List.range 3).any fun e => selfOnly (URTM.Three.realize es D) e

/-- 段階 2b（群 B まで）の例外: 段階 2a の例外のうち、初めにしか居られない状態を持たない表。 -/
def isExcB (es : List Nat) (D : List Dir) : Bool := isExc es D && !grpB es D

/-- 群 A は群 B に含まれる（入る規則が無ければ、入る規則はどれも自分から出る）。 -/
theorem grpA_le_grpB (es : List Nat) (D : List Dir) (h : grpA es D = true) : grpB es D = true := by
  unfold grpA at h
  unfold grpB
  obtain ⟨e, he, hno⟩ := List.any_eq_true.mp h
  refine List.any_eq_true.mpr ⟨e, he, ?_⟩
  unfold selfOnly
  refine List.all_eq_true.mpr fun r hr => ?_
  have := noEntry_spec hno r hr
  simp [this]

/-- **3 状態 2 記号の RTM の停止問題は、U の ID の上で計算可能**（`isExcB` の表を除く）。 -/
theorem three_halting_computable_B (H : RTM32 tbl q₀ q₁ q₂ sg)
    (hne : isExcB (absCodes q₀ q₁ q₂ sg tbl) (absDirs q₀ q₁ q₂ tbl) = false) :
    ∃ f : ZID → Bool, Computable f ∧
      ∀ z, (∀ a ∈ z.2.1 ++ z.2.2, a = 0 ∨ a ∈ [sg]) → (ZHalts tbl z ↔ f z = true) := by
  cases hexc : isExc (absCodes q₀ q₁ q₂ sg tbl) (absDirs q₀ q₁ q₂ tbl) with
  | false => exact three_halting_computable H hexc
  | true =>
    have hB : grpB (absCodes q₀ q₁ q₂ sg tbl) (absDirs q₀ q₁ q₂ tbl) = true := by
      unfold isExcB at hne
      rw [hexc] at hne
      simpa using hne
    obtain ⟨e, he, hso⟩ := List.any_eq_true.mp hB
    exact halting_computable_of_bound H bndB_primrec (selfOnly_bound H (List.mem_range.mp he) hso)

/-- **定理（段階 2b、群 A・B）: `isExcB` の表を除き、3 状態 2 記号の URTM は存在しない**（Morita Def. 7.1、
    U の記号集合 {0, sg} の上の ID への符号化）。 -/
theorem no_three_two_URTM_B (H : RTM32 tbl q₀ q₁ q₂ sg)
    (hne : isExcB (absCodes q₀ q₁ q₂ sg tbl) (absDirs q₀ q₁ q₂ tbl) = false) :
    ¬ IsUTM_MoritaOver tbl [sg] :=
  not_UTM_of_halting_computable (three_halting_computable_B H hne)

end

end URTM.Meta
