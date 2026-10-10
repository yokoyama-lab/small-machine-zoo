#!/usr/bin/env python3
"""ブロック分け × 役割の併合 × ε の変換（`lean/URTM/KStateBlocks.lean` の `bconv`、docs/22）を具体機械に適用する
Lean モジュール。

    python3 tools/gen_blocks_lean.py results/kstate_blocks/records/urtm4-46.json \\
        --module KB4_46 --base K10_8 > lean/URTM/Gen/KB4_46.lean

T・St・Sy・Ps は生成済みの密な版モジュール `URTM.Gen.BASE`（tools/gen_kstate_lean.py）のものを使う。
足すもの:
  * `spB : BSpec St k` — 解（JSON）のブロック `blk`・計数値 `v`・番兵 `sg`・役割の類 `cls`
    （類の番号は `tools/kstate_blocks.py` の `Gen.states` の並び。規則を持たない類は 0 に寄せる）
  * `qsB` — Python の `Gen._build` が往復の規則を置く順（+ のブロック 1.. → − のブロック 1..、各ブロック内は
    T の状態の順）。`ssB` — 記号を名前の順に並べたもの（Python の `sorted(reads[q])`・`sorted(W[q])`）
  * `TpyB` — `tools/kstate_blocks.py` の `Gen` が作る T'（規則の並びもそのまま）
  * `bconv_eq_py : bconv T spB qsB ssB = TpyB`（カーネルの `decide`）— Lean の変換と Python の表は
    規則の並びまで一致する
  * `det_rev` — 生成表の決定性・可逆性（カーネルの `decide`。主定理の仮定 `hD'` にも使う）
  * `card` — 規則数、記号の全体 `symB`（Python の `Gen.symbols`）の長さと重複の無さ、表の記号が `symB` に
    入ること、`symB` のどの記号も表に現れること、`Fin k` のどの状態も表の現状態に現れること
"""

import argparse
import json
import sys

sys.path.insert(0, __file__.rsplit("/", 1)[0])
import kstate_blocks  # noqa: E402

DIR = {"-": ".L", "0": ".Z", "+": ".R"}


def main(sol, module, base):
    r = json.load(open(sol))
    info = kstate_blocks.Info(kstate_blocks.machine_path(r["machine"]))
    T = info.T
    g = kstate_blocks.gen_of(info, r)
    assert not g.conflicts(), g.conflicts()[:2]
    k = g.k
    bp, bm = g.bp, g.bm

    sid = {s: f"q{i}" for i, s in enumerate(T.states)}
    yid = {s: f"s{i}" for i, s in enumerate(T.symbols)}
    pid = {s: f"h{i}" for i, s in enumerate(T.pseudo)}
    sidx = {name: i for i, name in enumerate(g.states)}

    def sym(x):
        if g.is_counter(x):
            i, s = g.split_counter(x)
            assert i >= 0, x
            return f"KSym.ctr {i} Sy.{yid[s]}"
        return f"KSym.pl Sy.{yid[x]}"

    def st(c):
        return f"({sidx[c]} : Fin {k})"

    def tgt(q):
        return f".halt Ps.{pid[q]}" if q in T.pseudo else f".go {st(q)}"

    qsB = [q for d in "+-" for b in range(1, (bp if d == "+" else bm) + 1)
           for q in info.Qd[d] if g.blk[q] == b]
    assert sorted(qsB) == sorted(T.states)
    ssB = sorted(T.symbols)
    rules = g.quints
    nsym = len(g.symbols)

    cls_lines = []
    for role in kstate_blocks.roles_of(bp, bm):
        kind, d, b = role
        name = g.cls[role]
        cls_lines.append(f"    | .{kind}, {DIR[d]}, {b} => {sidx.get(name, 0)}")

    L = []
    L.append("/-")
    L.append(f"  {r['machine']} と {sol.split('/')[-1]} から自動生成（tools/gen_blocks_lean.py）。手で編集しないこと。")
    L.append(f"  ブロック分け × 役割の併合 × ε（tools/kstate_blocks.py、docs/22）: ブロック ({bp},{bm})、"
             f"状態 {k} / 記号 {nsym} / 五つ組 {len(rules)}")
    L.append("  併合: " + "; ".join("&".join(x) for x in g.groups) if g.groups else "  併合: なし")
    L.append("  状態の番号: " + ", ".join(f"{i}={n}" for i, n in enumerate(g.states)))
    L.append("  計数値: " + ", ".join(f"{q}={info.dir[q]}{g.blk[q]}:{g.v[q]}" for q in qsB)
             + "、番兵: " + ", ".join(f"{key}={val}" for key, val in sorted(g.sigma.items())))
    L.append("-/")
    L.append("import URTM.KStateBlocks")
    L.append(f"import URTM.Gen.{base}")
    L.append("")
    L.append("set_option maxRecDepth 100000")
    L.append("")
    L.append(f"namespace URTM.Gen.{module}")
    L.append("")
    L.append(f"open URTM URTM.KState URTM.KStateSparse URTM.KStateBlocks URTM.Gen.{base}")
    L.append("")
    L.append("/-- ブロック分け・計数値・番兵・役割の類（解の JSON から）。 -/")
    L.append(f"def spB : BSpec St {k} where")
    L.append("  blk q := match q with")
    L += [f"    | .{sid[q]} => {g.blk[q]}" for q in T.states]
    L.append("  v q := match q with")
    L += [f"    | .{sid[q]} => {g.v[q]}" for q in T.states]
    L.append("  sg d b := match d, b with")
    L += [f"    | {DIR[key[0]]}, {int(key[1:])} => {val}" for key, val in sorted(g.sigma.items())]
    L.append("    | _, _ => 0")
    L.append("  cls r d b := match r, d, b with")
    L += cls_lines
    L.append("    | _, _, _ => 0")
    L.append("")
    L.append("/-- 往復の規則を置く状態の順（Python の `Gen._build` の順）。 -/")
    L.append("def qsB : List St := [" + ", ".join(f".{sid[q]}" for q in qsB) + "]")
    L.append("/-- 記号を名前の順に（Python の `sorted`）。 -/")
    L.append("def ssB : List Sy := [" + ", ".join(f".{yid[s]}" for s in ssB) + "]")
    L.append("")
    L.append("/-- `tools/kstate_blocks.py` の `Gen` が作った T'（規則の並びもそのまま）。 -/")
    L.append(f"def TpyB : Machine (Fin {k}) Ps (KSym Sy) := [")
    L.append(",\n".join(f"  ⟨{st(p)}, {sym(s)}, {sym(t)}, {DIR[d]}, {tgt(q)}⟩" for (p, s, t, d, q) in rules))
    L.append("]")
    L.append("")
    L.append("/-- 記号の全体（Python の `Gen.symbols`: T の記号と、表に現れる計数記号）。 -/")
    L.append("def symB : List (KSym Sy) := [" + ", ".join(sym(x) for x in g.symbols) + "]")
    L.append("")
    L.append("theorem hQB : ∀ q, q ∈ qsB := by intro q; cases q <;> decide")
    L.append("theorem hSB : ∀ s, s ∈ ssB := by intro s; cases s <;> decide")
    L.append("")
    L.append("/-- Lean の変換 `bconv` と Python の生成表は、規則の並びまで一致する（カーネルで検査）。 -/")
    L.append("theorem bconv_eq_py : bconv T spB qsB ssB = TpyB := by decide +kernel")
    L.append("")
    L.append("/-- 生成表の決定性・可逆性（カーネルの `decide`）。 -/")
    L.append("theorem det_rev : Deterministic TpyB ∧ Reversible TpyB := by")
    L.append("  constructor <;> decide +kernel")
    L.append("")
    L.append(f"theorem card : TpyB.length = {len(rules)} ∧ symB.length = {nsym} ∧ symB.Nodup ∧")
    L.append("    (∀ ρ ∈ TpyB, ρ.s ∈ symB ∧ ρ.t ∈ symB) ∧ (∀ σ ∈ symB, ∃ ρ ∈ TpyB, ρ.s = σ ∨ ρ.t = σ) ∧")
    L.append(f"    (∀ x : Fin {k}, ∃ ρ ∈ TpyB, ρ.p = x) := by decide +kernel")
    L.append("")
    L.append(f"""/-- 変換を {r['machine']} に適用した結論。T' = `bconv T spB qsB ssB`（= `TpyB`）は
    {k} 状態（型 `Fin {k}`、どの状態も現状態に現れる）・記号は {nsym} 要素の `symB` に入る（どれも実際に現れる）・
    規則 {len(rules)} 本の決定的可逆機械で、T の各ステップを `bcost` = 3 + 2|v − σ| ステップで模倣する。 -/
theorem main :
    let T' := bconv T spB qsB ssB
    let E := benc T spB
    Deterministic T' ∧ Reversible T' ∧
    (∀ ρ ∈ T', ρ.s ∈ symB ∧ ρ.t ∈ symB) ∧ symB.length = {nsym} ∧ symB.Nodup ∧
    (∀ x : Fin {k}, ∃ ρ ∈ T', ρ.p = x) ∧ T'.length = {len(rules)} ∧ T' = TpyB ∧
    (∀ c c' : Cfg St Ps Sy, Step T c c' → Live T c' → StepN T' (bcost T spB c') (E c) (E c')) ∧
    (∀ (n : Nat) (c cf : Cfg St Ps Sy), HaltsIn T n c cf → (∃ h, cf.st = .halt h) →
      ∃ N, n ≤ N ∧ HaltsIn T' N (E c) (E cf)) ∧
    (∀ (N : Nat) (c : Cfg St Ps Sy) (e : Cfg (Fin {k}) Ps (KSym Sy)), NoStuck T c →
      HaltsIn T' N (E c) e → ∃ n cf, HaltsIn T n c cf ∧ e = E cf) ∧
    (∀ c : Cfg St Ps Sy, NoStuck T c →
      ((∀ n cf, ¬ HaltsIn T n c cf) ↔ (∀ N e, ¬ HaltsIn T' N (E c) e))) := by
  intro T' E
  have hT : T' = TpyB := bconv_eq_py
  obtain ⟨hD', hR'⟩ := det_rev
  obtain ⟨hlen, hsl, hsn, hsym, -, hst⟩ := card
  rw [← hT] at hD' hR' hsym hst hlen
  exact ⟨hD', hR', hsym, hsl, hsn, hst, hlen, hT, bconv_main hW hR hQB hSB hD'⟩""")
    L.append("")
    L.append(f"end URTM.Gen.{module}")
    print("\n".join(L))


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("solution", help="tools/kstate_blocks.py の解の JSON（results/kstate_blocks/records/*.json）")
    ap.add_argument("--module", required=True)
    ap.add_argument("--base", required=True, help="同じ記述ファイルから作った密な版のモジュール名（K10_8 など）")
    a = ap.parse_args()
    main(a.solution, a.module, a.base)
