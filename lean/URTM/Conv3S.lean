/-
  改良版の 3 状態化（docs/09_three_state_2026-09-26.md）の合成: 1WU 化（Conv1W.lean）の後に
  3 状態化（Conv3P.lean）をかけた機械 `conv` が T を模倣すること、左右反転してから変換して反転し直した機械
  `convM` が T を模倣すること、どちらも決定的・可逆であること（一般定理）。

  * `conv_main`  : conv（反転なし）。停止の対応（T が N ステップで e に止まる ⇔ conv が fin N e に止まる）。
  * `convM_main` : convM = mirror (conv (mirror T))（(3,600) の形）。符号化は flipC ∘ enc ∘ flipC。

  番号付け idx と計数の上限 need は引数。仮定は、W の規則について idx が 1 以上で書く記号の計数が足りること
  （`hidx`、具体機械では `decide`）と、W の各状態が読みうる記号の計数が足りること（`need_*`）。

  mathlib 非依存。未証明の穴・新規公理・native_decide を使わない。
-/
import URTM.Conv1W
import URTM.Conv3P

set_option linter.unusedSectionVars false

namespace URTM.Conv3S

open URTM URTM.KState URTM.SimLemmas URTM.Conv3Base
open URTM.Conv1W (VSt VSym isPlus allSyms)
open URTM.Conv3P (CSym)
open URTM.Conv510 (TSt shapeOK)

variable {Q P S : Type} [DecidableEq Q] [DecidableEq S]

/-- W の記号の列挙（空白が先頭。`threestate.py` の W.symbols と同じ順）。 -/
def wsyms (ss : List S) (qm : List Q) (Gl : List (Q × S)) : List (VSym Q S) := .bl :: allSyms ss qm Gl

/-- **改良版の 3 状態化**（反転なし）: 1WU 化 W の後に 3 状態化。 -/
def conv (T : Machine Q P S) (b : S) (ss : List S) (qm : List Q) (Rl Gl : List (Q × S))
    (idx : VSt Q S → Nat) (need : VSym Q S → Nat) : Machine TSt P (CSym (VSym Q S)) :=
  Conv3P.conv (Conv1W.conv T b ss qm Rl Gl) .L .bl idx need (wsyms ss qm Gl)

/-- T の配置 c（組の始まり a0、長さ n0）の符号化。 -/
def enc (T : Machine Q P S) (idx : VSt Q S → Nat) (a0 : Int) (n0 : Nat) (c : Cfg Q P S) :
    Cfg TSt P (CSym (VSym Q S)) :=
  Conv3P.enc .L idx (Conv1W.Wc T a0 n0 0 c)

/-- T が N ステップで e に止まったときの停止配置。 -/
def fin (T : Machine Q P S) (idx : VSt Q S → Nat) (a0 : Int) (n0 : Nat) (N : Nat) (e : Cfg Q P S) :
    Cfg TSt P (CSym (VSym Q S)) :=
  Conv3P.enc .L idx (Conv1W.Ev T a0 n0 N e)

/-- 仮定のまとめ。 -/
structure Hyp (T : Machine Q P S) (b : S) (ss : List S) (qm : List Q) (Rl Gl : List (Q × S))
    (idx : VSt Q S → Nat) (need : VSym Q S → Nat) : Prop where
  hS : ∀ s, s ∈ ss
  /-- 規則はどれも実状態へ入り、左右どちらかへ動く（停止規則・0 シフト規則を除いた機械）。 -/
  hG : ∀ r ∈ T, r.q.isGo = true ∧ r.d ≠ .Z
  hD : Deterministic T
  hR : Reversible T
  /-- qm はちょうど Q₋ の状態。 -/
  hqm : ∀ q, isPlus T q = false → q ∈ qm
  hqm' : ∀ p ∈ qm, isPlus T p = false
  /-- Rl は右移動の行き先と書込記号の組をすべて含み、Gl ⊇ Rl は Q₊ の状態の組。 -/
  hRl : ∀ r ∈ T, ∀ q, r.q = .go q → r.d = .R → (q, r.t) ∈ Rl
  hRG : ∀ pv ∈ Rl, pv ∈ Gl
  hGl : ∀ pv ∈ Gl, isPlus T pv.1 = true
  /-- W の規則の行き先の番号は 1 以上で、書く記号の計数はその番号まである。 -/
  hidx : ∀ r ∈ Conv1W.conv T b ss qm Rl Gl, ∀ q, r.q = .go q → q ≠ .L → 1 ≤ idx q ∧ idx q ≤ need r.t
  hinj : ∀ p q : VSt Q S, p ≠ .L → q ≠ .L → idx p = idx q → p = q
  /-- 刈り込みの健全性: c s は W の任意の記号を、r・g は素の記号を、e1・e2 は空白を読む。 -/
  need_c : ∀ s, ∀ x ∈ wsyms ss qm Gl, idx (.c s) ≤ need x
  need_r : ∀ pv ∈ Rl, ∀ x, idx (.r pv.1 pv.2) ≤ need (.pl x)
  need_g : ∀ pv ∈ Gl, ∀ u, idx (.g pv.1 pv.2) ≤ need (.pl u)
  need_e1 : idx .e1 ≤ need .bl
  need_e2 : idx .e2 ≤ need .bl

section Main
variable {T : Machine Q P S} {b : S} {ss : List S} {qm : List Q} {Rl Gl : List (Q × S)}
  {idx : VSt Q S → Nat} {need : VSym Q S → Nat}

theorem pl_mem (hS : ∀ s, s ∈ ss) (s : S) : (.pl s : VSym Q S) ∈ wsyms ss qm Gl := by
  simp only [wsyms, allSyms, List.mem_cons, List.mem_append, List.mem_map, List.mem_flatMap]
  right; left; left; exact ⟨s, hS s, rfl⟩

theorem mk_mem (hS : ∀ s, s ∈ ss) {p : Q} (hp : p ∈ qm) (s : S) : (.mk p s : VSym Q S) ∈ wsyms ss qm Gl := by
  simp only [wsyms, allSyms, List.mem_cons, List.mem_append, List.mem_map, List.mem_flatMap]
  right; left; right; exact ⟨p, hp, s, hS s, rfl⟩

theorem mkp_mem {pv : Q × S} (hpv : pv ∈ Gl) : (.mkp pv.1 pv.2 : VSym Q S) ∈ wsyms ss qm Gl := by
  simp only [wsyms, allSyms, List.mem_cons, List.mem_append, List.mem_map, List.mem_flatMap]
  right; right; exact ⟨pv, hpv, rfl⟩

theorem bl_mem : (.bl : VSym Q S) ∈ wsyms ss qm Gl := List.mem_cons_self ..

/-- 読む記号の述語。 -/
def good (idx : VSt Q S → Nat) (need : VSym Q S → Nat) (ws : List (VSym Q S)) (q : VSt Q S) (x : VSym Q S) :
    Prop :=
  q = .L ∨ (idx q ≤ need x ∧ x ∈ ws)

theorem hyp1W (H : Hyp T b ss qm Rl Gl idx need) :
    Conv1W.Hyp T b ss qm Rl Gl (good idx need (wsyms ss qm Gl)) where
  hS := H.hS
  hG := H.hG
  hD := H.hD
  hLm := Conv1W.hLm_of_rev H.hR
  hqm := H.hqm
  hR := H.hRl
  hRG := H.hRG
  good_c := fun s x hx => .inr ⟨H.need_c s x hx, hx⟩
  good_r := fun pv hpv x => .inr ⟨H.need_r pv hpv x, pl_mem H.hS x⟩
  good_g := fun pv hpv u => .inr ⟨H.need_g pv hpv u, pl_mem H.hS u⟩
  good_e1 := .inr ⟨H.need_e1, bl_mem⟩
  good_e2 := .inr ⟨H.need_e2, bl_mem⟩
  good_L := fun _ => .inl rfl

/-- W の規則が読み書きする記号は列挙にある。 -/
theorem w_syms (H : Hyp T b ss qm Rl Gl idx need) {ρ : Rule (VSt Q S) P (VSym Q S)}
    (h : ρ ∈ Conv1W.conv T b ss qm Rl Gl) : ρ.s ∈ wsyms ss qm Gl ∧ ρ.t ∈ wsyms ss qm Gl := by
  have hLm := Conv1W.hLm_of_rev H.hR
  rcases Conv1W.mem_conv h with rfl | ⟨x, hx, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, rfl⟩ | ⟨s, p, u, hp, e⟩ | ⟨_, pv, hpv, rfl⟩ |
    rfl | rfl | ⟨pv, x, hpv, rfl⟩ | ⟨pv, u, hpv, e⟩
  · exact ⟨bl_mem, bl_mem⟩
  · exact ⟨List.mem_cons_of_mem _ hx, List.mem_cons_of_mem _ hx⟩
  · exact ⟨pl_mem H.hS _, pl_mem H.hS _⟩
  · exact ⟨bl_mem, pl_mem H.hS _⟩
  · obtain ⟨r, hl, q, hq, hc⟩ := Conv1W.headC_spec e
    obtain ⟨hr, _, _⟩ := Conv1W.look_some hl
    rcases hc with ⟨hd, rfl⟩ | ⟨_, rfl⟩
    · exact ⟨mk_mem H.hS hp _, mk_mem H.hS (H.hqm _ (hLm r hr q hq hd)) _⟩
    · exact ⟨mk_mem H.hS hp _, pl_mem H.hS _⟩
  · exact ⟨mkp_mem hpv, pl_mem H.hS _⟩
  · exact ⟨bl_mem, pl_mem H.hS _⟩
  · exact ⟨bl_mem, bl_mem⟩
  · exact ⟨pl_mem H.hS _, mkp_mem (H.hRG pv hpv)⟩
  · obtain ⟨r, hl, q, hq, hc⟩ := Conv1W.headG_spec e
    obtain ⟨hr, _, _⟩ := Conv1W.look_some hl
    rcases hc with ⟨hd, rfl⟩ | ⟨_, rfl⟩
    · exact ⟨pl_mem H.hS _, mk_mem H.hS (H.hqm _ (hLm r hr q hq hd)) _⟩
    · exact ⟨pl_mem H.hS _, pl_mem H.hS _⟩

/-- W の規則は 1WU の形。 -/
theorem w_shape {ρ : Rule (VSt Q S) P (VSym Q S)} (h : ρ ∈ Conv1W.conv T b ss qm Rl Gl) :
    shapeOK .L .bl ρ = true := by
  rcases Conv1W.mem_conv h with rfl | ⟨x, hx, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, rfl⟩ | ⟨s, p, u, hp, e⟩ | ⟨_, pv, hpv, rfl⟩ |
    rfl | rfl | ⟨pv, x, hpv, rfl⟩ | ⟨pv, u, hpv, e⟩
  · simp [shapeOK]
  · have := Conv1W.allSyms_ne hx
    simp [shapeOK, this]
  · simp [shapeOK]
  · simp [shapeOK]
  · obtain ⟨r, hl, q, hq, hc⟩ := Conv1W.headC_spec e
    rcases hc with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp [shapeOK]
  · simp [shapeOK]
  · simp [shapeOK]
  · simp [shapeOK]
  · simp [shapeOK]
  · obtain ⟨r, hl, q, hq, hc⟩ := Conv1W.headG_spec e
    rcases hc with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp [shapeOK]

theorem hyp3P (H : Hyp T b ss qm Rl Gl idx need) :
    Conv3P.Hyp (Conv1W.conv T b ss qm Rl Gl) .L .bl idx need (wsyms ss qm Gl) where
  hS := fun _ h => w_syms H h
  hshape := fun _ h => w_shape h
  hidx := H.hidx
  hinj := H.hinj

theorem good_needOK (c : Cfg (VSt Q S) P (VSym Q S))
    (h : Conv1W.Good (good idx need (wsyms ss qm Gl)) c) : Conv3P.NeedOK .L idx need (wsyms ss qm Gl) c := by
  intro q hq hqL
  rcases h q hq with h | h
  · exact absurd h hqL
  · exact h

theorem conv_det (H : Hyp T b ss qm Rl Gl idx need) : Deterministic (conv T b ss qm Rl Gl idx need) :=
  Conv3P.conv_det Conv1W.conv_det (fun _ h => w_shape h) H.hinj

theorem conv_rev (H : Hyp T b ss qm Rl Gl idx need) : Reversible (conv T b ss qm Rl Gl idx need) :=
  Conv3P.conv_rev (Conv1W.conv_rev ⟨H.hR, H.hD, H.hqm', H.hGl⟩) (fun _ h => w_shape h) H.hinj

/-- T が N ステップで止まるなら、conv も N ステップ以上で fin N e に止まる。 -/
theorem halts_fwd (H : Hyp T b ss qm Rl Gl idx need) {a0 : Int} {n0 : Nat} {c0 : Cfg Q P S} {p0 : Q}
    (hc0 : c0.st = .go p0) (hI : Conv1W.Inv T b Gl a0 n0 p0 c0.pos c0.tape) {N : Nat} {e : Cfg Q P S}
    (h : HaltsIn T N c0 e) :
    ∃ M, N ≤ M ∧ HaltsIn (conv T b ss qm Rl Gl idx need) M (enc T idx a0 n0 c0) (fin T idx a0 n0 N e) := by
  obtain ⟨M, hM, hrun, hH⟩ := Conv1W.halts_sim (hyp1W H) hc0 hI h
  obtain ⟨M', hM', hs⟩ := Conv3P.grun_sim (hyp3P H) good_needOK hrun
  obtain ⟨⟨p, hp, _⟩, _⟩ := Conv1W.run_sim (hyp1W H) hc0 hI N h.1
  have hE : (Conv1W.Ev T a0 n0 N e).st = .go (if isPlus T p then .g p (e.tape (e.pos - 1)) else .c (e.tape (e.pos - 1))) := by
    simp [Conv1W.Ev, hp, Conv1W.haltV]
  refine ⟨M', by omega, hs, Conv3P.halted_sim (hyp3P H) hE ?_ hH⟩
  split <;> nofun

/-- **模倣（反転なし）**。T は停止規則を除いた可逆機械、c0 は不変量を満たす配置。conv は決定的・可逆で:
    1. T が c0 から N ステップで e に止まるなら、conv は enc c0 から N ステップ以上で fin N e に止まる。
    2. conv が enc c0 から止まるなら、T も c0 から止まり、停止配置は 1 の形。 -/
theorem conv_main (H : Hyp T b ss qm Rl Gl idx need) {a0 : Int} {n0 : Nat} {c0 : Cfg Q P S} {p0 : Q}
    (hc0 : c0.st = .go p0) (hI : Conv1W.Inv T b Gl a0 n0 p0 c0.pos c0.tape) :
    Deterministic (conv T b ss qm Rl Gl idx need) ∧ Reversible (conv T b ss qm Rl Gl idx need) ∧
    (∀ N e, HaltsIn T N c0 e →
      ∃ M, N ≤ M ∧ HaltsIn (conv T b ss qm Rl Gl idx need) M (enc T idx a0 n0 c0) (fin T idx a0 n0 N e)) ∧
    (∀ M e', HaltsIn (conv T b ss qm Rl Gl idx need) M (enc T idx a0 n0 c0) e' →
      ∃ N e, HaltsIn T N c0 e ∧ e' = fin T idx a0 n0 N e) := by
  have hD := conv_det H
  refine ⟨hD, conv_rev H, fun N e h => halts_fwd H hc0 hI h,
    back_of_fwd hD (fin T idx a0 n0) (fun N e h => let ⟨M, _, hM⟩ := halts_fwd H hc0 hI h; ⟨M, hM⟩)
      fun _ N _ hb => ?_⟩
  obtain ⟨_, M₁, hM₁, hrun⟩ := Conv1W.run_sim (hyp1W H) hc0 hI N hb
  obtain ⟨M₂, hM₂, hs⟩ := Conv3P.grun_sim (hyp3P H) good_needOK hrun
  exact ⟨M₂, by omega, _, hs⟩

/-! ## 反転してから変換（(3,600) の形） -/

/-- **反転版**: T を左右反転して変換し、方向を入れ替え直した機械（元の T を模倣する）。 -/
def convM (T : Machine Q P S) (b : S) (ss : List S) (qm : List Q) (Rl Gl : List (Q × S))
    (idx : VSt Q S → Nat) (need : VSym Q S → Nat) : Machine TSt P (CSym (VSym Q S)) :=
  mirror (conv (mirror T) b ss qm Rl Gl idx need)

/-- 反転版の符号化: T の配置を折り返し、反転した T の符号化をとり、それを折り返す。 -/
def encM (T : Machine Q P S) (idx : VSt Q S → Nat) (a0 : Int) (n0 : Nat) (c : Cfg Q P S) :
    Cfg TSt P (CSym (VSym Q S)) :=
  flipC (enc (mirror T) idx a0 n0 (flipC c))

def finM (T : Machine Q P S) (idx : VSt Q S → Nat) (a0 : Int) (n0 : Nat) (N : Nat) (e : Cfg Q P S) :
    Cfg TSt P (CSym (VSym Q S)) :=
  flipC (fin (mirror T) idx a0 n0 N (flipC e))

/-- **模倣（反転版）**。仮定は反転した機械 mirror T について述べる（qm・Rl・Gl・idx・need も反転した機械のもの）。
    不変量は折り返した初期配置について。 -/
theorem convM_main (H : Hyp (mirror T) b ss qm Rl Gl idx need) {a0 : Int} {n0 : Nat} {c0 : Cfg Q P S} {p0 : Q}
    (hc0 : c0.st = .go p0) (hI : Conv1W.Inv (mirror T) b Gl a0 n0 p0 (-c0.pos) (fun i => c0.tape (-i))) :
    Deterministic (convM T b ss qm Rl Gl idx need) ∧ Reversible (convM T b ss qm Rl Gl idx need) ∧
    (∀ N e, HaltsIn T N c0 e →
      ∃ M, N ≤ M ∧ HaltsIn (convM T b ss qm Rl Gl idx need) M (encM T idx a0 n0 c0) (finM T idx a0 n0 N e)) ∧
    (∀ M e', HaltsIn (convM T b ss qm Rl Gl idx need) M (encM T idx a0 n0 c0) e' →
      ∃ N e, HaltsIn T N c0 e ∧ e' = finM T idx a0 n0 N e) := by
  obtain ⟨hD, hR, hf, hb⟩ := conv_main (c0 := flipC c0) H hc0 hI
  refine ⟨det_mirror hD, rev_mirror hR, fun N e h => ?_, fun M e' he' => ?_⟩
  · obtain ⟨M, hM, hh⟩ := hf N (flipC e) (haltsIn_mirror_iff.mpr h)
    exact ⟨M, hM, haltsIn_mirror_iff.mpr hh⟩
  · have := haltsIn_mirror_of (T := conv (mirror T) b ss qm Rl Gl idx need) he'
    obtain ⟨N, e, h, he⟩ := hb M _ this
    refine ⟨N, flipC e, ?_, ?_⟩
    · exact haltsIn_mirror_of h
    · rw [finM, flipC_flipC, ← he, flipC_flipC]

/-- 反転版の規則が読み書きする記号はすべて `univ need (wsyms ss qm Gl)` にある
    （W の各規則の現状態が読む記号の計数も足りていれば）。 -/
theorem convM_syms (H : Hyp (mirror T) b ss qm Rl Gl idx need)
    (hsrc : ∀ r ∈ Conv1W.conv (mirror T) b ss qm Rl Gl, r.p ≠ .L → 1 ≤ idx r.p ∧ idx r.p ≤ need r.s) :
    ∀ ρ ∈ convM T b ss qm Rl Gl idx need,
      ρ.s ∈ Conv3P.univ need (wsyms ss qm Gl) ∧ ρ.t ∈ Conv3P.univ need (wsyms ss qm Gl) := by
  intro ρ h
  have := Conv3P.conv_syms (fun _ h => w_syms H h) (fun _ h => w_shape h) H.hidx hsrc _ (mem_mirror.mp h)
  exact this

end Main

end URTM.Conv3S
