/-
  2 状態 RTM の停止問題の決定可能性 その 6: 窓の中の配置の番号づけ。**手書き**。

  窓 [lo, lo+W) の外が空白で、ヘッドが窓の中に居る配置に、nsym^W · (3W) 未満の番号を
  単射に振る。鳩の巣（`pigeon`）に渡すために使う。
-/
import URTM.TSDMirror

namespace URTM.TwoState

/-- 窓 [lo, lo+m) の中身を nsym 進数で読む。 -/
def encW (nsym : Nat) (u : Int → Nat) : Int → Nat → Nat
  | _, 0 => 0
  | lo, m + 1 => u lo + nsym * encW nsym u (lo + 1) m

theorem lt_mul_of_digit {n d r M : Nat} (hd : d < n) (hr : r < M) : d + n * r < n * M := by
  have h1 : n * (r + 1) ≤ n * M := Nat.mul_le_mul_left n hr
  rw [Nat.mul_succ] at h1
  omega

theorem encW_lt (nsym : Nat) (u : Int → Nat) :
    ∀ (m : Nat) (lo : Int), (∀ i : Nat, i < m → u (lo + i) < nsym) →
      encW nsym u lo m < nsym ^ m := by
  intro m
  induction m with
  | zero => intro lo _; simp [encW]
  | succ m ih =>
    intro lo h
    show u lo + nsym * encW nsym u (lo + 1) m < nsym ^ (m + 1)
    have hd : u lo < nsym := by have := h 0 (by omega); simpa using this
    have hr : encW nsym u (lo + 1) m < nsym ^ m :=
      ih (lo + 1) (fun i hi => by have := h (i + 1) (by omega); rw [show lo + ((i + 1 : Nat) : Int) = lo + 1 + i by push_cast; omega] at this; exact this)
    rw [Nat.pow_succ, Nat.mul_comm (nsym ^ m) nsym]
    exact lt_mul_of_digit hd hr

theorem digit_eq {n d d' r r' : Nat} (hn : 0 < n) (hd : d < n) (hd' : d' < n)
    (h : d + n * r = d' + n * r') : d = d' ∧ r = r' := by
  have h1 : (d + n * r) % n = d := by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hd]
  have h2 : (d' + n * r') % n = d' := by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hd']
  have h3 : (d + n * r) / n = r := by rw [Nat.add_mul_div_left _ _ hn, Nat.div_eq_of_lt hd]; omega
  have h4 : (d' + n * r') / n = r' := by rw [Nat.add_mul_div_left _ _ hn, Nat.div_eq_of_lt hd']; omega
  rw [h] at h1 h3
  exact ⟨by rw [← h1, h2], by rw [← h3, h4]⟩

theorem encW_inj (nsym : Nat) (u u' : Int → Nat) :
    ∀ (m : Nat) (lo : Int), (∀ i : Nat, i < m → u (lo + i) < nsym) →
      (∀ i : Nat, i < m → u' (lo + i) < nsym) →
      encW nsym u lo m = encW nsym u' lo m → ∀ i : Nat, i < m → u (lo + i) = u' (lo + i) := by
  intro m
  induction m with
  | zero => intro lo _ _ _ i hi; omega
  | succ m ih =>
    intro lo h h' he i hi
    have hd : u lo < nsym := by have := h 0 (by omega); simpa using this
    have hd' : u' lo < nsym := by have := h' 0 (by omega); simpa using this
    have hn : 0 < nsym := by omega
    obtain ⟨e1, e2⟩ := digit_eq hn hd hd' he
    cases i with
    | zero => simpa using e1
    | succ i =>
      have := ih (lo + 1)
        (fun j hj => by have := h (j + 1) (by omega); rw [show lo + ((j + 1 : Nat) : Int) = lo + 1 + j by push_cast; omega] at this; exact this)
        (fun j hj => by have := h' (j + 1) (by omega); rw [show lo + ((j + 1 : Nat) : Int) = lo + 1 + j by push_cast; omega] at this; exact this)
        e2 i (by omega)
      rw [show lo + ((i + 1 : Nat) : Int) = lo + 1 + i by push_cast; omega]
      exact this

def dcode : Dir → Nat
  | Dir.L => 0
  | Dir.Z => 1
  | Dir.R => 2

theorem dcode_lt (d : Dir) : dcode d < 3 := by cases d <;> simp [dcode]

theorem dcode_inj {d₁ d₂ : Dir} (h : dcode d₁ = dcode d₂) : d₁ = d₂ := by
  cases d₁ <;> cases d₂ <;> simp [dcode] at h ⊢

/-- 窓 [lo, lo+W) の配置の番号。 -/
def ccode (nsym : Nat) (lo : Int) (W : Nat) (z : Conf2) : Nat :=
  encW nsym z.tape lo W * (W * 3) + ((z.pos - lo).toNat * 3 + dcode z.dir)

/-- 窓に収まった配置: ヘッドは窓の中、窓の外は空白、記号は nsym 未満。 -/
def InWin (nsym : Nat) (lo : Int) (W : Nat) (z : Conf2) : Prop :=
  lo ≤ z.pos ∧ z.pos < lo + W ∧ (∀ x, (x < lo ∨ lo + W ≤ x) → z.tape x = 0) ∧
    ∀ x, z.tape x < nsym

def csize (nsym W : Nat) : Nat := nsym ^ W * (W * 3)

theorem ccode_lt {nsym : Nat} {lo : Int} {W : Nat} {z : Conf2} (h : InWin nsym lo W z) :
    ccode nsym lo W z < csize nsym W := by
  obtain ⟨h1, h2, _, h4⟩ := h
  have he := encW_lt nsym z.tape W lo (fun i _ => h4 _)
  have hp : (z.pos - lo).toNat * 3 + dcode z.dir < W * 3 := by
    have := dcode_lt z.dir
    have : (z.pos - lo).toNat < W := by omega
    omega
  unfold ccode csize
  have := lt_mul_of_digit hp he
  rw [Nat.mul_comm (nsym ^ W) (W * 3)]
  rw [Nat.mul_comm (encW nsym z.tape lo W) (W * 3)]
  omega

theorem ccode_inj {nsym : Nat} {lo : Int} {W : Nat} {z₁ z₂ : Conf2}
    (h₁ : InWin nsym lo W z₁) (h₂ : InWin nsym lo W z₂)
    (h : ccode nsym lo W z₁ = ccode nsym lo W z₂) : z₁ = z₂ := by
  obtain ⟨a1, a2, a3, a4⟩ := h₁
  obtain ⟨b1, b2, b3, b4⟩ := h₂
  have hW : 0 < W * 3 := by omega
  have hp1 : (z₁.pos - lo).toNat * 3 + dcode z₁.dir < W * 3 := by
    have := dcode_lt z₁.dir; have : (z₁.pos - lo).toNat < W := by omega
    omega
  have hp2 : (z₂.pos - lo).toNat * 3 + dcode z₂.dir < W * 3 := by
    have := dcode_lt z₂.dir; have : (z₂.pos - lo).toNat < W := by omega
    omega
  unfold ccode at h
  rw [Nat.mul_comm (encW nsym z₁.tape lo W), Nat.mul_comm (encW nsym z₂.tape lo W),
    Nat.add_comm, Nat.add_comm _ ((z₂.pos - lo).toNat * 3 + dcode z₂.dir)] at h
  obtain ⟨e1, e2⟩ := digit_eq hW hp1 hp2 h
  have hd1 := dcode_lt z₁.dir
  have hd2 := dcode_lt z₂.dir
  have e3 : dcode z₁.dir = dcode z₂.dir := by omega
  have e4 : (z₁.pos - lo).toNat = (z₂.pos - lo).toNat := by omega
  have hpos : z₁.pos = z₂.pos := by omega
  have hdir : z₁.dir = z₂.dir := dcode_inj e3
  have htape : z₁.tape = z₂.tape := by
    funext x
    by_cases hx : x < lo ∨ lo + W ≤ x
    · rw [a3 x hx, b3 x hx]
    · have := encW_inj nsym z₁.tape z₂.tape W lo (fun i _ => a4 _) (fun i _ => b4 _) e2
        (x - lo).toNat (by omega)
      rw [show lo + ((x - lo).toNat : Int) = x by omega] at this
      exact this
  cases z₁; cases z₂
  simp only at hpos hdir htape
  subst hpos; subst hdir; subst htape; rfl

end URTM.TwoState
