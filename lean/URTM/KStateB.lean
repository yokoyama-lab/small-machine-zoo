/-
  定理 B（ブロック化、docs/03_kstate_2026-09-23.md §3）の一般の模倣証明。

  状態番号を (ブロック b, オフセット i) に分け、b を T' の状態に、i をテープに持たせる。
  Q₊ を b₊ 個、Q₋ を b₋ 個のブロックに分けると、
  状態は H(d, b)（b₊ + b₋ 個）と A(d, b)（各方向 max(b₊, b₋) 個）、
  記号は素の n 個と計数 `[i, s]`（1 ≤ i ≤ ⌈m₊/b₊⌉ + ⌈m₋/b₋⌉）。

  共通部分（機械・配置・ステップ・`dir`・テープの補題）は `URTM.KState` を使う。
  主定理は `convB_main`（(a) 決定性・可逆性の保存、(b) 1 ステップの模倣と停止の対応、
  (c) 多ステップ、状態と記号の範囲）。b₊ = b₋ = 1 のとき規則の形は定理 A と同じ
  （状態の型だけが違う）。
-/
import URTM.KState

namespace URTM.KStateB

open URTM (Dir)
open URTM.KState

/-- T' の状態: `H d b`（安定配置）、`A d b`（往復中）。`d` は入る方向、`b` はブロック。 -/
inductive BSt where
  | H (d : Dir) (b : Nat)
  | A (d : Dir) (b : Nat)
  deriving DecidableEq, Repr

/-- 方向ごとのブロック数。 -/
def beta (βp βm : Nat) : Dir → Nat
  | .L => βm
  | _ => βp

@[simp] theorem beta_L (βp βm : Nat) : beta βp βm .L = βm := rfl
@[simp] theorem beta_R (βp βm : Nat) : beta βp βm .R = βp := rfl

variable {Q P S : Type}

section Conv
variable [DecidableEq Q] [DecidableEq P]

/-- R1 / R1'。 -/
def rule1 (T : Machine Q P S) (blk off : Q → Nat) (r : Rule Q P S) : Rule BSt P (KSym S) :=
  match r.q with
  | .go q => ⟨.H (dir T r.p) (blk r.p), .ctr (off r.p) r.s, .ctr (off q) r.t, r.d, .go (.H r.d (blk q))⟩
  | .halt h => ⟨.H (dir T r.p) (blk r.p), .ctr (off r.p) r.s, .pl r.t, r.d, .halt h⟩

/-- 方向 `d`・ブロック `b` の往復（R2〜R5）。 -/
def shuttle (Bp Bm : Nat) (ss : List S) (d : Dir) (b : Nat) : List (Rule BSt P (KSym S)) :=
  if lo Bp d ≤ hi Bp Bm d then
    ss.map (fun s₂ => ⟨.H d b, .pl s₂, .ctr (lo Bp d) s₂, opp d, .go (.A (opp d) b)⟩) ++
    (List.range' (lo Bp d + 1) (hi Bp Bm d - lo Bp d)).flatMap
      (fun i => ss.map (fun t => ⟨.A (opp d) b, .ctr i t, .ctr (i - 1) t, d, .go (.A d b)⟩)) ++
    ss.map (fun t => ⟨.A (opp d) b, .ctr (lo Bp d) t, .pl t, d, .go (.H d b)⟩) ++
    (List.range' (lo Bp d) (hi Bp Bm d - lo Bp d)).flatMap
      (fun j => ss.map (fun s₂ => ⟨.A d b, .ctr j s₂, .ctr (j + 1) s₂, opp d, .go (.A (opp d) b)⟩))
  else []

/-- 番号付け（ブロック `blk`、オフセット `off`）とブロック数・範囲を与えた変換。 -/
def convWith (T : Machine Q P S) (blk off : Q → Nat) (βp βm Bp Bm : Nat) (ss : List S) :
    Machine BSt P (KSym S) :=
  T.map (rule1 T blk off) ++ (List.range' 1 βp).flatMap (shuttle Bp Bm ss .R) ++
    (List.range' 1 βm).flatMap (shuttle Bp Bm ss .L)

/-- 番号付けの条件。 -/
structure GoodNum (T : Machine Q P S) (blk off : Q → Nat) (βp βm Bp Bm : Nat) : Prop where
  inj : ∀ a b, dir T a = dir T b → blk a = blk b → off a = off b → a = b
  rngR : ∀ q, dir T q = .R → 1 ≤ off q ∧ off q ≤ Bp ∧ 1 ≤ blk q ∧ blk q ≤ βp
  rngL : ∀ q, dir T q = .L → Bp + 1 ≤ off q ∧ off q ≤ Bp + Bm ∧ 1 ≤ blk q ∧ blk q ≤ βm

/-- 配置の符号化。 -/
def enc (T : Machine Q P S) (blk off : Q → Nat) (c : Cfg Q P S) : Cfg BSt P (KSym S) :=
  match c.st with
  | .go p => ⟨.go (.H (dir T p) (blk p)), c.pos,
      fun j => if j = c.pos then .ctr (off p) (c.tape j) else .pl (c.tape j)⟩
  | .halt h => ⟨.halt h, c.pos, fun j => .pl (c.tape j)⟩

theorem enc_go (p : Q) (pos : Int) (tape : Int → S) (T : Machine Q P S) (blk off : Q → Nat) :
    enc T blk off ⟨.go p, pos, tape⟩ =
      ⟨.go (.H (dir T p) (blk p)), pos,
        fun j => if j = pos then .ctr (off p) (tape j) else .pl (tape j)⟩ := rfl

/-- 規則の分類。 -/
inductive Kind (T : Machine Q P S) (blk off : Q → Nat) (βp βm Bp Bm : Nat) :
    Rule BSt P (KSym S) → Prop
  | r1go (p : Q) (s t : S) (d : Dir) (q : Q) :
      (⟨p, s, t, d, .go q⟩ : Rule Q P S) ∈ T → (d = .L ∨ d = .R) →
      Kind T blk off βp βm Bp Bm
        ⟨.H (dir T p) (blk p), .ctr (off p) s, .ctr (off q) t, d, .go (.H d (blk q))⟩
  | r1halt (p : Q) (s t : S) (d : Dir) (h : P) :
      (⟨p, s, t, d, .halt h⟩ : Rule Q P S) ∈ T →
      Kind T blk off βp βm Bp Bm ⟨.H (dir T p) (blk p), .ctr (off p) s, .pl t, d, .halt h⟩
  | r2 (d : Dir) (b : Nat) (s₂ : S) : (d = .L ∨ d = .R) → 1 ≤ b → b ≤ beta βp βm d →
      lo Bp d ≤ hi Bp Bm d →
      Kind T blk off βp βm Bp Bm ⟨.H d b, .pl s₂, .ctr (lo Bp d) s₂, opp d, .go (.A (opp d) b)⟩
  | r3 (d : Dir) (b i : Nat) (t : S) : (d = .L ∨ d = .R) → 1 ≤ b → b ≤ beta βp βm d →
      lo Bp d < i → i ≤ hi Bp Bm d →
      Kind T blk off βp βm Bp Bm ⟨.A (opp d) b, .ctr i t, .ctr (i - 1) t, d, .go (.A d b)⟩
  | r4 (d : Dir) (b : Nat) (t : S) : (d = .L ∨ d = .R) → 1 ≤ b → b ≤ beta βp βm d →
      lo Bp d ≤ hi Bp Bm d →
      Kind T blk off βp βm Bp Bm ⟨.A (opp d) b, .ctr (lo Bp d) t, .pl t, d, .go (.H d b)⟩
  | r5 (d : Dir) (b j : Nat) (s₂ : S) : (d = .L ∨ d = .R) → 1 ≤ b → b ≤ beta βp βm d →
      lo Bp d ≤ j → j < hi Bp Bm d →
      Kind T blk off βp βm Bp Bm ⟨.A d b, .ctr j s₂, .ctr (j + 1) s₂, opp d, .go (.A (opp d) b)⟩

variable {T : Machine Q P S} {blk off : Q → Nat} {βp βm Bp Bm : Nat} {ss : List S}

theorem mem_shuttle {d : Dir} (hd : d = .L ∨ d = .R) {b : Nat} (hb1 : 1 ≤ b)
    (hb2 : b ≤ beta βp βm d) {ρ : Rule BSt P (KSym S)}
    (h : ρ ∈ shuttle Bp Bm ss d b) : Kind T blk off βp βm Bp Bm ρ := by
  unfold shuttle at h
  split at h
  · rename_i hlh
    simp only [List.mem_append, List.mem_map, List.mem_flatMap, List.mem_range'_1] at h
    rcases h with ((⟨s₂, _, rfl⟩ | ⟨i, ⟨h1, h2⟩, t, _, rfl⟩) | ⟨t, _, rfl⟩) | ⟨j, ⟨h1, h2⟩, s₂, _, rfl⟩
    · exact Kind.r2 d b s₂ hd hb1 hb2 hlh
    · exact Kind.r3 d b i t hd hb1 hb2 (by omega) (by omega)
    · exact Kind.r4 d b t hd hb1 hb2 hlh
    · exact Kind.r5 d b j s₂ hd hb1 hb2 h1 (by omega)
  · simp at h

theorem kind_of_mem (hW : ZeroShiftHalts T) {ρ : Rule BSt P (KSym S)}
    (h : ρ ∈ convWith T blk off βp βm Bp Bm ss) : Kind T blk off βp βm Bp Bm ρ := by
  unfold convWith at h
  simp only [List.mem_append, List.mem_map, List.mem_flatMap, List.mem_range'_1] at h
  rcases h with (⟨r, hr, rfl⟩ | ⟨b, ⟨hb1, hb2⟩, h⟩) | ⟨b, ⟨hb1, hb2⟩, h⟩
  · obtain ⟨p, s, t, d, q⟩ := r
    cases q with
    | go q =>
      have hd : d = .L ∨ d = .R := go_dir_LR hW hr rfl
      exact Kind.r1go p s t d q hr hd
    | halt h => exact Kind.r1halt p s t d h hr
  · exact mem_shuttle (.inr rfl) hb1 (by simp; omega) h
  · exact mem_shuttle (.inl rfl) hb1 (by simp; omega) h

theorem mem_of_kind (hS : ∀ s, s ∈ ss) {ρ : Rule BSt P (KSym S)}
    (h : Kind T blk off βp βm Bp Bm ρ) : ρ ∈ convWith T blk off βp βm Bp Bm ss := by
  unfold convWith
  simp only [List.mem_append, List.mem_flatMap, List.mem_range'_1]
  have hsh : ∀ d b, (d = .L ∨ d = .R) → 1 ≤ b → b ≤ beta βp βm d →
      ρ ∈ shuttle Bp Bm ss d b →
      (ρ ∈ T.map (rule1 T blk off) ∨ ∃ a, (1 ≤ a ∧ a < 1 + βp) ∧ ρ ∈ shuttle Bp Bm ss .R a) ∨
        ∃ a, (1 ≤ a ∧ a < 1 + βm) ∧ ρ ∈ shuttle Bp Bm ss .L a := by
    rintro d b (rfl | rfl) h1 h2 h
    · exact .inr ⟨b, ⟨h1, by simp at h2; omega⟩, h⟩
    · exact .inl (.inr ⟨b, ⟨h1, by simp at h2; omega⟩, h⟩)
  cases h with
  | r1go p s t d q hr _ =>
    refine .inl (.inl (List.mem_map.2 ⟨_, hr, ?_⟩))
    simp [rule1]
  | r1halt p s t d h hr =>
    refine .inl (.inl (List.mem_map.2 ⟨_, hr, ?_⟩))
    simp [rule1]
  | r2 d b s₂ hd hb1 hb2 hlh =>
    apply hsh d b hd hb1 hb2
    unfold shuttle; rw [if_pos hlh]
    simp only [List.mem_append, List.mem_map]
    exact .inl (.inl (.inl ⟨s₂, hS _, rfl⟩))
  | r3 d b i t hd hb1 hb2 h1 h2 =>
    apply hsh d b hd hb1 hb2
    unfold shuttle; rw [if_pos (by omega)]
    simp only [List.mem_append, List.mem_map, List.mem_flatMap, List.mem_range'_1]
    exact .inl (.inl (.inr ⟨i, ⟨by omega, by omega⟩, t, hS _, rfl⟩))
  | r4 d b t hd hb1 hb2 hlh =>
    apply hsh d b hd hb1 hb2
    unfold shuttle; rw [if_pos hlh]
    simp only [List.mem_append, List.mem_map]
    exact .inl (.inr ⟨t, hS _, rfl⟩)
  | r5 d b j s₂ hd hb1 hb2 h1 h2 =>
    apply hsh d b hd hb1 hb2
    unfold shuttle; rw [if_pos (by omega)]
    simp only [List.mem_append, List.mem_map, List.mem_flatMap, List.mem_range'_1]
    exact .inr ⟨j, ⟨h1, by omega⟩, s₂, hS _, rfl⟩

/-! ## (a) 決定性と可逆性の保存 -/

theorem convWith_det (hW : ZeroShiftHalts T) (hD : Deterministic T)
    (hinj : ∀ a b, dir T a = dir T b → blk a = blk b → off a = off b → a = b) :
    Deterministic (convWith T blk off βp βm Bp Bm ss) := by
  intro a ha b hb hne hp hs
  have ka := kind_of_mem hW ha
  have kb := kind_of_mem hW hb
  clear ha hb
  rcases ka with ⟨p, s, t, d, q, hr, (rfl | rfl)⟩ | ⟨p, s, t, d, ph, hr⟩ |
      ⟨d, e, s₂, (rfl | rfl), he1, he2, hlh⟩ | ⟨d, e, i, t, (rfl | rfl), he1, he2, h1, h2⟩ |
      ⟨d, e, t, (rfl | rfl), he1, he2, hlh⟩ | ⟨d, e, j, s₂, (rfl | rfl), he1, he2, h1, h2⟩ <;>
  rcases kb with ⟨p', s', t', d', q', hr', (rfl | rfl)⟩ | ⟨p', s', t', d', ph', hr'⟩ |
      ⟨d', e', s₂', (rfl | rfl), he1', he2', hlh'⟩ |
      ⟨d', e', i', t', (rfl | rfl), he1', he2', h1', h2'⟩ |
      ⟨d', e', t', (rfl | rfl), he1', he2', hlh'⟩ |
      ⟨d', e', j', s₂', (rfl | rfl), he1', he2', h1', h2'⟩
  all_goals first
    | (simp only [BSt.H.injEq] at hp
       obtain ⟨hd1, hb1⟩ := hp
       simp only [KSym.ctr.injEq] at hs
       obtain ⟨h1, rfl⟩ := hs
       obtain rfl := hinj _ _ hd1 hb1 h1
       have := detT_eq hD hr hr' rfl rfl
       simp_all)
    | (simp_all; done)
    | (simp_all; omega)

theorem convWith_rev (hW : ZeroShiftHalts T) (hR : Reversible T)
    (hinj : ∀ a b, dir T a = dir T b → blk a = blk b → off a = off b → a = b) :
    Reversible (convWith T blk off βp βm Bp Bm ss) := by
  intro a ha b hb hne hq
  have ka := kind_of_mem hW ha
  have kb := kind_of_mem hW hb
  clear ha hb
  rcases ka with ⟨p, s, t, d, q, hr, (rfl | rfl)⟩ | ⟨p, s, t, d, ph, hr⟩ |
      ⟨d, e, s₂, (rfl | rfl), he1, he2, hlh⟩ | ⟨d, e, i, t, (rfl | rfl), he1, he2, h1, h2⟩ |
      ⟨d, e, t, (rfl | rfl), he1, he2, hlh⟩ | ⟨d, e, j, s₂, (rfl | rfl), he1, he2, h1, h2⟩ <;>
  rcases kb with ⟨p', s', t', d', q', hr', (rfl | rfl)⟩ | ⟨p', s', t', d', ph', hr'⟩ |
      ⟨d', e', s₂', (rfl | rfl), he1', he2', hlh'⟩ |
      ⟨d', e', i', t', (rfl | rfl), he1', he2', h1', h2'⟩ |
      ⟨d', e', t', (rfl | rfl), he1', he2', hlh'⟩ |
      ⟨d', e', j', s₂', (rfl | rfl), he1', he2', h1', h2'⟩
  all_goals first
    | -- R1 と R1（行き先が実状態）
      (refine ⟨rfl, ?_⟩
       intro ht
       simp only [KSym.ctr.injEq] at ht
       obtain ⟨h1, rfl⟩ := ht
       have hb : blk q = blk q' := by simpa using hq
       have e1 := dir_eq hW hR hr rfl
       have e2 := dir_eq hW hR hr' rfl
       obtain rfl := hinj _ _ (e1.trans e2.symm) hb h1
       have := revT_eq hR hr hr' rfl rfl
       simp_all)
    | -- R1' と R1'（同じ疑似状態）
      (have hh : ph = ph' := by simpa using hq
       subst hh
       have hne' : (⟨p, s, t, d, .halt ph⟩ : Rule Q P S) ≠ ⟨p', s', t', d', .halt ph⟩ := by
         intro e; simp_all
       have := hR _ hr _ hr' hne' rfl
       simp_all)
    | -- R3 と R3（同じブロック・同じ方向）
      (refine ⟨rfl, ?_⟩
       intro ht
       apply hne
       simp only [KSym.ctr.injEq] at ht
       obtain ⟨hi, rfl⟩ := ht
       have he : e = e' := by simpa using hq
       subst he
       have : i = i' := by omega
       subst this
       rfl)
    | (simp_all; done)
    | (simp_all; omega)
    | (simp_all; intros; omega)
    | (simp_all; intro h3; exact hne (by omega))

/-! ## (b) 1 ステップの模倣 -/

/-- T の 1 ステップ（行き先配置 `c'`）に要する T' のステップ数。 -/
def cost (T : Machine Q P S) (off : Q → Nat) (Bp : Nat) (c' : Cfg Q P S) : Nat :=
  match c'.st with
  | .go q => 3 + 2 * (off q - lo Bp (dir T q))
  | .halt _ => 1

theorem cost_pos {c' : Cfg Q P S} : 1 ≤ cost T off Bp c' := by
  unfold cost; split <;> omega

theorem sim_go (hW : ZeroShiftHalts T) (hR : Reversible T) (hN : GoodNum T blk off βp βm Bp Bm)
    (hS : ∀ s, s ∈ ss) {p q : Q} {s t : S} {d : Dir}
    (hr : (⟨p, s, t, d, .go q⟩ : Rule Q P S) ∈ T) (pos : Int) (tape : Int → S)
    (hs : tape pos = s) :
    StepN (convWith T blk off βp βm Bp Bm ss) (3 + 2 * (off q - lo Bp (dir T q)))
      (enc T blk off ⟨.go p, pos, tape⟩) (enc T blk off ⟨.go q, pos + mv d, upd tape pos t⟩) := by
  have hdq : dir T q = d := dir_eq hW hR hr rfl
  have hd : d = .L ∨ d = .R := go_dir_LR hW hr rfl
  have hrng : lo Bp d ≤ off q ∧ off q ≤ hi Bp Bm d ∧ 1 ≤ blk q ∧ blk q ≤ beta βp βm d := by
    rcases hd with rfl | rfl
    · have := hN.rngL q hdq; simp; omega
    · have := hN.rngR q hdq; simp; omega
  obtain ⟨h1, h2, hb1, hb2⟩ := hrng
  subst hs
  rw [enc_go, enc_go, hdq]
  exact sim_go_gen hd h1 (mem_of_kind hS (.r1go p _ t d q hr hd))
    (mem_of_kind hS (.r2 d (blk q) _ hd hb1 hb2 (by omega)))
    (fun i h1 h2 => mem_of_kind hS (.r3 d (blk q) i t hd hb1 hb2 h1 (by omega)))
    (fun j h1 h2 => mem_of_kind hS (.r5 d (blk q) j _ hd hb1 hb2 h1 (by omega)))
    (mem_of_kind hS (.r4 d (blk q) t hd hb1 hb2 (by omega)))

theorem sim_halt (hS : ∀ s, s ∈ ss) {p : Q} {s t : S} {d : Dir} {h : P}
    (hr : (⟨p, s, t, d, .halt h⟩ : Rule Q P S) ∈ T) (pos : Int) (tape : Int → S)
    (hs : tape pos = s) :
    StepN (convWith T blk off βp βm Bp Bm ss) 1
      (enc T blk off ⟨.go p, pos, tape⟩) (enc T blk off ⟨.halt h, pos + mv d, upd tape pos t⟩) := by
  have hk := Kind.r1halt (T := T) (blk := blk) (off := off) (βp := βp) (βm := βm) (Bp := Bp)
    (Bm := Bm) p s t d h hr
  refine StepN.single (step_of (mem_of_kind hS hk) rfl (by simp [enc, hs]) rfl rfl ?_)
  funext j; simp only [enc, upd]
  by_cases h : j = pos <;> simp [h]

theorem convWith_simulates (hW : ZeroShiftHalts T) (hR : Reversible T)
    (hN : GoodNum T blk off βp βm Bp Bm) (hS : ∀ s, s ∈ ss) {c c' : Cfg Q P S} (h : Step T c c') :
    StepN (convWith T blk off βp βm Bp Bm ss) (cost T off Bp c')
      (enc T blk off c) (enc T blk off c') := by
  obtain ⟨⟨p, s, t, d, q⟩, hr, hst, hs, rfl⟩ := h
  obtain ⟨st, pos, tape⟩ := c
  simp only at hst hs
  subst hst
  cases q with
  | go q => exact sim_go hW hR hN hS hr pos tape hs
  | halt h => exact sim_halt hS hr pos tape hs

theorem convWith_halted (hW : ZeroShiftHalts T)
    (hinj : ∀ a b, dir T a = dir T b → blk a = blk b → off a = off b → a = b)
    {c : Cfg Q P S} (hH : Halted T c) :
    Halted (convWith T blk off βp βm Bp Bm ss) (enc T blk off c) := by
  intro c'' ⟨ρ, hρ, hst, hs, _⟩
  obtain ⟨st, pos, tape⟩ := c
  cases st with
  | halt h => simp [enc] at hst
  | go p =>
    rw [enc_go] at hst hs
    simp at hst hs
    rcases kind_of_mem hW hρ with ⟨p', s', t', d', q', hr, _⟩ | ⟨p', s', t', d', ph', hr⟩ |
        ⟨d', e', s₂', hd, _⟩ | ⟨d', e', i', t', hd, _⟩ | ⟨d', e', t', hd, _⟩ |
        ⟨d', e', j', s₂', hd, _⟩
    · simp only [BSt.H.injEq] at hst
      obtain ⟨hd1, hb1⟩ := hst
      simp only [KSym.ctr.injEq] at hs
      obtain ⟨h1, rfl⟩ := hs
      obtain rfl := hinj _ _ hd1 hb1 h1
      exact hH _ ⟨_, hr, rfl, rfl, rfl⟩
    · simp only [BSt.H.injEq] at hst
      obtain ⟨hd1, hb1⟩ := hst
      simp only [KSym.ctr.injEq] at hs
      obtain ⟨h1, rfl⟩ := hs
      obtain rfl := hinj _ _ hd1 hb1 h1
      exact hH _ ⟨_, hr, rfl, rfl, rfl⟩
    · simp at hs
    · simp at hst
    · simp at hst
    · simp at hst

/-! ## (c) 多ステップ -/

theorem convWith_haltsIn (hW : ZeroShiftHalts T) (hR : Reversible T)
    (hN : GoodNum T blk off βp βm Bp Bm) (hS : ∀ s, s ∈ ss) :
    ∀ {n : Nat} {c cf : Cfg Q P S}, HaltsIn T n c cf →
      ∃ N, n ≤ N ∧ HaltsIn (convWith T blk off βp βm Bp Bm ss) N
        (enc T blk off c) (enc T blk off cf) :=
  fun h => haltsIn_of_sim _ _ (fun _ => True) (fun _ => cost_pos)
    (fun h₁ _ _ => convWith_simulates hW hR hN hS h₁) (fun hH _ => convWith_halted hW hN.inj hH) h trivial

theorem convWith_haltsIn_rev (hW : ZeroShiftHalts T) (hD : Deterministic T) (hR : Reversible T)
    (hN : GoodNum T blk off βp βm Bp Bm) (hS : ∀ s, s ∈ ss) :
    ∀ (N : Nat) {c : Cfg Q P S} {e : Cfg BSt P (KSym S)},
      HaltsIn (convWith T blk off βp βm Bp Bm ss) N (enc T blk off c) e →
      ∃ n cf, HaltsIn T n c cf ∧ e = enc T blk off cf :=
  fun N _ _ h => haltsIn_rev_of_sim _ _ (fun _ => True) (convWith_det hW hD hN.inj) (fun _ => cost_pos)
    (fun _ _ => trivial) (fun _ h₁ => convWith_simulates hW hR hN hS h₁)
    (fun _ hH => convWith_halted hW hN.inj hH) N trivial h

/-! ## 状態と記号の範囲 -/

/-- 状態の全体: `H R b`（b ≤ b₊）、`H L b`（b ≤ b₋）、`A d b`（b ≤ max(b₊, b₋)）。 -/
def stUniverse (βp βm : Nat) : List BSt :=
  (List.range' 1 βp).map (.H .R) ++ (List.range' 1 βm).map (.H .L) ++
    (List.range' 1 (max βp βm)).map (.A .R) ++ (List.range' 1 (max βp βm)).map (.A .L)

theorem stUniverse_length (βp βm : Nat) :
    (stUniverse βp βm).length = βp + βm + 2 * max βp βm := by
  simp [stUniverse]; omega

theorem convWith_states (hW : ZeroShiftHalts T) (hR : Reversible T)
    (hN : GoodNum T blk off βp βm Bp Bm)
    {ρ : Rule BSt P (KSym S)} (hρ : ρ ∈ convWith T blk off βp βm Bp Bm ss) :
    ρ.p ∈ stUniverse βp βm ∧ ∀ x, ρ.q = .go x → x ∈ stUniverse βp βm := by
  have hmax1 := Nat.le_max_left βp βm
  have hmax2 := Nat.le_max_right βp βm
  have hsrc : ∀ q, BSt.H (dir T q) (blk q) ∈ stUniverse βp βm := fun q => by
    rcases dir_cases T q with h | h
    · have := hN.rngL q h; simp [stUniverse, h]; omega
    · have := hN.rngR q h; simp [stUniverse, h]; omega
  rcases kind_of_mem hW hρ with ⟨p, s, t, d, q, hr, _⟩ | ⟨p, s, t, d, ph, hr⟩ |
      ⟨d, e, s₂, (rfl | rfl), he1, he2, hlh⟩ | ⟨d, e, i, t, (rfl | rfl), he1, he2, h1, h2⟩ |
      ⟨d, e, t, (rfl | rfl), he1, he2, hlh⟩ | ⟨d, e, j, s₂, (rfl | rfl), he1, he2, h1, h2⟩
  · have hdq := dir_eq hW hR hr rfl
    have hq := hsrc q
    rw [hdq] at hq
    refine ⟨hsrc p, ?_⟩
    intro x hx
    simp only [Tgt.go.injEq] at hx
    subst hx
    exact hq
  · exact ⟨hsrc p, by simp⟩
  all_goals (simp at he2; simp [stUniverse]; omega)


/-! ## 記号の範囲 -/

theorem convWith_symbols (hW : ZeroShiftHalts T) (hN : GoodNum T blk off βp βm Bp Bm)
    {ρ : Rule BSt P (KSym S)} (hρ : ρ ∈ convWith T blk off βp βm Bp Bm ss) :
    ∀ σ ∈ [ρ.s, ρ.t], (∃ x, σ = .pl x) ∨ (∃ i x, σ = .ctr i x ∧ 1 ≤ i ∧ i ≤ Bp + Bm) := by
  have hoff : ∀ q, 1 ≤ off q ∧ off q ≤ Bp + Bm := fun q => by
    rcases dir_cases T q with h | h
    · have := hN.rngL q h; omega
    · have := hN.rngR q h; omega
  rcases kind_of_mem hW hρ with ⟨p, s, t, d, q, _, _⟩ | ⟨p, s, t, d, ph, _⟩ |
      ⟨d, e, s₂, (rfl | rfl), he1, he2, hlh⟩ | ⟨d, e, i, t, (rfl | rfl), he1, he2, h1, h2⟩ |
      ⟨d, e, t, (rfl | rfl), he1, he2, hlh⟩ | ⟨d, e, j, s₂, (rfl | rfl), he1, he2, h1, h2⟩ <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false] <;> rintro σ (rfl | rfl) <;>
    simp_all [lo, hi] <;> omega

/-! ## 標準の番号付け（`tools/kstate.py` と同じ: ブロック = k / B + 1、オフセット = lo + k % B） -/

/-- ⌈m / β⌉。 -/
def ceilDiv (m β : Nat) : Nat := (m + β - 1) / β

theorem ceil_facts {m β k : Nat} (hβ : 1 ≤ β) (hk : k < m) :
    0 < ceilDiv m β ∧ k % ceilDiv m β < ceilDiv m β ∧ k / ceilDiv m β < β := by
  have hB : 0 < ceilDiv m β := Nat.div_pos (by omega) (by omega)
  refine ⟨hB, Nat.mod_lt _ hB, ?_⟩
  rw [Nat.div_lt_iff_lt_mul hB]
  have h1 := Nat.div_add_mod (m + β - 1) β
  have h2 := Nat.mod_lt (m + β - 1) (by omega : 0 < β)
  unfold ceilDiv
  generalize β * ((m + β - 1) / β) = Y at h1 ⊢
  omega

theorem divmod_inj {B a b : Nat} (h1 : a / B = b / B) (h2 : a % B = b % B) : a = b := by
  have ha := Nat.div_add_mod a B
  have hb := Nat.div_add_mod b B
  rw [h1, h2] at ha
  omega

/-- Q₊ のオフセット幅 ⌈m₊/b₊⌉。 -/
def canonBp (T : Machine Q P S) (qs : List Q) (βp : Nat) : Nat := ceilDiv (plusList T qs).length βp
/-- Q₋ のオフセット幅 ⌈m₋/b₋⌉。 -/
def canonBm (T : Machine Q P S) (qs : List Q) (βm : Nat) : Nat := ceilDiv (minusList T qs).length βm

def canonBlk (T : Machine Q P S) (qs : List Q) (βp βm : Nat) (q : Q) : Nat :=
  if dir T q = .R then ix q (plusList T qs) / canonBp T qs βp + 1
  else ix q (minusList T qs) / canonBm T qs βm + 1

def canonOffB (T : Machine Q P S) (qs : List Q) (βp βm : Nat) (q : Q) : Nat :=
  if dir T q = .R then 1 + ix q (plusList T qs) % canonBp T qs βp
  else canonBp T qs βp + 1 + ix q (minusList T qs) % canonBm T qs βm

/-- **定理 B の変換**（関数）。b₊ = βp、b₋ = βm。 -/
def convB (T : Machine Q P S) (qs : List Q) (ss : List S) (βp βm : Nat) : Machine BSt P (KSym S) :=
  convWith T (canonBlk T qs βp βm) (canonOffB T qs βp βm) βp βm (canonBp T qs βp) (canonBm T qs βm) ss

theorem canonB_good {qs : List Q} (hQ : ∀ q, q ∈ qs) {βp βm : Nat} (hβp : 1 ≤ βp) (hβm : 1 ≤ βm) :
    GoodNum T (canonBlk T qs βp βm) (canonOffB T qs βp βm) βp βm (canonBp T qs βp) (canonBm T qs βm) := by
  have memP : ∀ q, dir T q = .R → q ∈ plusList T qs := fun q h => by
    simp [plusList, List.mem_filter, hQ q, h]
  have memM : ∀ q, dir T q = .L → q ∈ minusList T qs := fun q h => by
    simp [minusList, List.mem_filter, hQ q, h]
  refine ⟨?_, ?_, ?_⟩
  · intro a b hd hb ho
    unfold canonBlk at hb
    unfold canonOffB at ho
    rcases dir_cases T a with ha | ha
    · have hb' : dir T b = .L := hd ▸ ha
      simp only [ha, hb', reduceCtorEq, if_false] at hb ho
      exact ix_inj (memM a ha) (memM b hb') (divmod_inj (B := canonBm T qs βm) (by omega) (by omega))
    · have hb' : dir T b = .R := hd ▸ ha
      simp only [ha, hb', if_true] at hb ho
      exact ix_inj (memP a ha) (memP b hb') (divmod_inj (B := canonBp T qs βp) (by omega) (by omega))
  · intro q h
    have := ceil_facts hβp (ix_lt (memP q h))
    simp only [canonOffB, canonBlk, h, if_true, canonBp]
    generalize ix q (plusList T qs) / ceilDiv (plusList T qs).length βp = x at *
    generalize ix q (plusList T qs) % ceilDiv (plusList T qs).length βp = y at *
    omega
  · intro q h
    have := ceil_facts hβm (ix_lt (memM q h))
    simp only [canonOffB, canonBlk, h, reduceCtorEq, if_false, canonBm]
    generalize ix q (minusList T qs) / ceilDiv (minusList T qs).length βm = x at *
    generalize ix q (minusList T qs) % ceilDiv (minusList T qs).length βm = y at *
    omega

section MainB
variable {qs : List Q}

/-- **定理 B**（まとめ）。b₊, b₋ ≥ 1。状態は `stUniverse b₊ b₋`（b₊ + b₋ + 2 max(b₊,b₋) 個）、
    記号は `symUniverse (⌈m₊/b₊⌉ + ⌈m₋/b₋⌉) ss`（(⌈m₊/b₊⌉ + ⌈m₋/b₋⌉ + 1) n 個）に入る。 -/
theorem convB_main (hW : ZeroShiftHalts T) (hD : Deterministic T) (hR : Reversible T)
    (hQ : ∀ q, q ∈ qs) (hS : ∀ s, s ∈ ss) {βp βm : Nat} (hβp : 1 ≤ βp) (hβm : 1 ≤ βm) :
    let T' := convB T qs ss βp βm
    let blk := canonBlk T qs βp βm
    let off := canonOffB T qs βp βm
    let Bp := canonBp T qs βp
    let Bm := canonBm T qs βm
    Deterministic T' ∧ Reversible T' ∧
    (∀ c c' : Cfg Q P S, Step T c c' →
      StepN T' (cost T off Bp c') (enc T blk off c) (enc T blk off c')) ∧
    (∀ c : Cfg Q P S, Halted T c ↔ Halted T' (enc T blk off c)) ∧
    (∀ (n : Nat) (c cf : Cfg Q P S), HaltsIn T n c cf →
      ∃ N, n ≤ N ∧ HaltsIn T' N (enc T blk off c) (enc T blk off cf)) ∧
    (∀ (N : Nat) (c : Cfg Q P S) (e : Cfg BSt P (KSym S)),
      HaltsIn T' N (enc T blk off c) e → ∃ n cf, HaltsIn T n c cf ∧ e = enc T blk off cf) ∧
    (∀ c : Cfg Q P S, (∀ n cf, ¬ HaltsIn T n c cf) ↔ (∀ N e, ¬ HaltsIn T' N (enc T blk off c) e)) ∧
    (∀ ρ ∈ T', ρ.p ∈ stUniverse βp βm ∧ ∀ x, ρ.q = .go x → x ∈ stUniverse βp βm) ∧
    (∀ ρ ∈ T', ρ.s ∈ symUniverse (Bp + Bm) ss ∧ ρ.t ∈ symUniverse (Bp + Bm) ss) := by
  intro T' blk off Bp Bm
  have hN := canonB_good (T := T) hQ hβp hβm
  have hD' : Deterministic T' := convWith_det hW hD hN.inj
  have hsim : ∀ c c' : Cfg Q P S, Step T c c' →
      StepN T' (cost T off Bp c') (enc T blk off c) (enc T blk off c') :=
    fun _ _ h => convWith_simulates hW hR hN hS h
  have hhin := fun {n} {c cf : Cfg Q P S} (h : HaltsIn T n c cf) =>
    convWith_haltsIn (ss := ss) hW hR hN hS h
  have hrev := fun N {c : Cfg Q P S} {e} (h : HaltsIn T' N (enc T blk off c) e) =>
    convWith_haltsIn_rev hW hD hR hN hS N h
  refine ⟨hD', convWith_rev hW hR hN.inj, hsim, ?_, fun _ _ _ h => hhin h,
    fun N _ _ h => hrev N h, ?_, fun _ h => convWith_states hW hR hN h, ?_⟩
  · intro c
    constructor
    · exact convWith_halted hW hN.inj
    · intro h c' hs
      have := hsim _ _ hs
      have hp := cost_pos (T := T) (off := off) (Bp := Bp) (c' := c')
      obtain ⟨x, hx⟩ := StepN.first this hp
      exact h x hx
  · exact fun c => diverges_iff_of (fun _ _ hn => let ⟨N, _, hN'⟩ := hhin hn; ⟨N, _, hN'⟩)
      (fun N _ he => let ⟨n, cf, hn, _⟩ := hrev N he; ⟨n, cf, hn⟩)
  · intro ρ hρ
    have h := convWith_symbols hW hN hρ
    have key : ∀ σ ∈ [ρ.s, ρ.t], σ ∈ symUniverse (Bp + Bm) ss := by
      intro σ hσ
      unfold symUniverse
      rcases h σ hσ with ⟨x, rfl⟩ | ⟨i, x, rfl, h1, h2⟩
      · exact List.mem_append.2 (.inl (List.mem_map.2 ⟨x, hS x, rfl⟩))
      · exact List.mem_append.2 (.inr (mem_ctrs (hS x) h1 h2))
    exact ⟨key _ (by simp), key _ (by simp)⟩

end MainB

end Conv

end URTM.KStateB
