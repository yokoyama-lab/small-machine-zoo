#!/usr/bin/env python3
"""ε 逆向きの 4 状態化（`lean/URTM/KStateEps.lean` の `econv`、docs/20 §3）を具体機械に適用する Lean モジュール。

    python3 tools/gen_eps_lean.py data/urtm/urtm10-8.txt results/kstate5/urtm10-8.k4.eps-.json \\
        --module KE10_8 --base K10_8 > lean/URTM/Gen/KE10_8.lean

T・St・Sy・Ps は生成済みの密な版モジュール `URTM.Gen.BASE`（tools/gen_kstate_lean.py）のものを使う。
足すもの:
  * `qsE` — 状態の並び。Lean の標準の番号付け `ecanonOff T qsE`（Q₊ は下から 1..m₊、Q₋ は上から M..）が
    CP-SAT の解（JSON の v）と一致するように、Q₊ を v の昇順、Q₋ を v の降順に並べる（一致しなければ止まる）
  * `TpyE` — `tools/kstate5.py` の `Gen`（k4, ε₋ = −1）が作る T' を、Lean の `econv` の並び
    （R1 → R2⁺ → R2⁻ → R4⁺ → R4⁻ → dec 2..M → inc 1..M−1、各々は記号の並び順）に並べて写したもの。
    Python の規則がすべてこの並びに現れることも確かめる（現れなければ止まる）
  * `econv_eq_py : econv T qsE ss = TpyE`（カーネルの `decide`）— Lean の「構文的に要る規則」の選択が
    Python と規則の並びまで一致する
  * `card` — 規則数・記号の全体の長さ、全体のどの記号も表に現れること（記号数がちょうどその数であること）
"""

import argparse
import json
import sys

sys.path.insert(0, __file__.rsplit("/", 1)[0])
import kstate5  # noqa: E402

DIR = {"-": ".L", "0": ".Z", "+": ".R"}
KST = {"hp": "KSt.Hp", "hm": "KSt.Hm", "op_dm": "KSt.Am", "dp_om": "KSt.Ap"}


def main(path, sol, module, base):
    info = kstate5.Info(path)
    T = info.T
    r = json.load(open(sol))
    assert r["partition"] == "k4", r["partition"]
    v, sigma, eps = r["v"], r["sigma"], r["eps"]
    assert eps == {"+": 1, "-": -1}, eps
    g = kstate5.Gen(info, "k4", v, sigma, eps)
    assert not g.conflicts(), g.conflicts()[:2]
    plus = sorted(info.Qd["+"], key=lambda q: v[q])
    minus = sorted(info.Qd["-"], key=lambda q: -v[q])
    M = max(len(plus), len(minus))
    # Lean の ecanonOff: Q₊ は ix+1、Q₋ は M − ix。番兵は σ₊ = 1、σ₋ = M。
    if [v[q] for q in plus] != list(range(1, len(plus) + 1)) or sigma["+"] != 1:
        raise SystemExit(f"Q+ numbering is not 1..m+ with sigma+=1: {[(q, v[q]) for q in plus]} {sigma}")
    if [v[q] for q in minus] != [M - i for i in range(len(minus))] or sigma["-"] != M:
        raise SystemExit(f"Q- numbering is not M..M-m-+1 with sigma-=M: {[(q, v[q]) for q in minus]} {sigma}")

    sid = {s: f"q{i}" for i, s in enumerate(T.states)}
    yid = {s: f"s{i}" for i, s in enumerate(T.symbols)}
    pid = {s: f"h{i}" for i, s in enumerate(T.pseudo)}
    C = g.C

    def sym(x):
        if g.is_counter(x):
            i, s = g.split_counter(x)
            return f"KSym.ctr {i} Sy.{yid[s]}"
        return f"KSym.pl Sy.{yid[x]}"

    def tgt(q):
        return f".halt Ps.{pid[q]}" if q in T.pseudo else f".go {KST[q]}"

    # Lean の econvWith の並び（密な場合の全候補）。Python の規則集合に入るものだけを残す。
    py = set(g.quints)
    order = []
    for (p, s, t, d, q) in T.quints:          # R1（T の並び）
        src = "hp" if info.dir[p] == "+" else "hm"
        if q in T.pseudo:
            order.append((src, C(v[p], s), t, d, q))
        else:
            order.append((src, C(v[p], s), C(v[q], t), d, "hp" if d == "+" else "hm"))
    X = list(T.symbols)
    slots = ([lambda x: ("hp", x, C(1, x), "-", "op_dm")] +
             [lambda x: ("hm", x, C(M, x), "+", "dp_om")] +
             [lambda x: ("op_dm", C(1, x), x, "+", "hp")] +
             [lambda x: ("dp_om", C(M, x), x, "-", "hm")] +
             [(lambda i: lambda x: ("op_dm", C(i, x), C(i - 1, x), "+", "dp_om"))(i) for i in range(2, M + 1)] +
             [(lambda j: lambda x: ("dp_om", C(j, x), C(j + 1, x), "-", "op_dm"))(j) for j in range(1, M)])
    for mk in slots:
        for x in X:
            rule = mk(x)
            if rule in py:
                order.append(rule)
    missing = py - set(order)
    if missing or len(order) != len(py):
        raise SystemExit(f"Python rules not in Lean order: {sorted(missing)[:4]} (order {len(order)} vs {len(py)})")
    n2 = (M + 1) * len(T.symbols)
    assert len(g.symbols) == n2, (len(g.symbols), n2)

    L = []
    L.append("/-")
    L.append(f"  {path.split('/')[-1]} と {sol.split('/')[-1]} から自動生成（tools/gen_eps_lean.py）。手で編集しないこと。")
    L.append(f"  ε 逆向きの 4 状態化（kstate5.py k4, ε₋ = −1）: 状態 {g.k} / 記号 {len(g.symbols)} / 五つ組 {len(order)}")
    L.append("  状態の並び: + は " + ", ".join(f"{q}={v[q]}" for q in plus) + "、- は "
             + ", ".join(f"{q}={v[q]}" for q in minus) + f"（σ₊ = 1, σ₋ = {M}）")
    L.append("  状態名の対応: hp = Hp, hm = Hm, op_dm = Am（O⁺ と D⁻）, dp_om = Ap（D⁺ と O⁻）")
    L.append("-/")
    L.append("import URTM.KStateEps")
    L.append(f"import URTM.Gen.{base}")
    L.append("")
    L.append("set_option maxRecDepth 100000")
    L.append("")
    L.append(f"namespace URTM.Gen.{module}")
    L.append("")
    L.append(f"open URTM URTM.KState URTM.KStateSparse URTM.KStateEps URTM.Gen.{base}")
    L.append("")
    L.append("/-- 状態の並び（Q₊ を v の昇順、続いて Q₋ を v の降順）。番号は `ecanonOff T qsE`。 -/")
    L.append("def qsE : List St := [" + ", ".join(f".{sid[q]}" for q in plus + minus) + "]")
    L.append("")
    L.append("/-- `tools/kstate5.py` が生成した T'（k4, ε₋ = −1）を Lean の `econv` の並びで写したもの。 -/")
    L.append("def TpyE : Machine KSt Ps (KSym Sy) := [")
    L.append(",\n".join(f"  ⟨{KST[p]}, {sym(s)}, {sym(t)}, {DIR[d]}, {tgt(q)}⟩" for (p, s, t, d, q) in order))
    L.append("]")
    L.append("")
    L.append("theorem hQE : ∀ q, q ∈ qsE := by intro q; cases q <;> decide")
    L.append("")
    L.append("/-- Lean の変換 `econv` と Python の生成表は、規則の並びまで一致する（カーネルで検査）。 -/")
    L.append("theorem econv_eq_py : econv T qsE ss = TpyE := by decide +kernel")
    L.append("")
    L.append("/-- 番号付けは CP-SAT の解（JSON の v）と一致する。 -/")
    L.append("theorem off_eq_py : (qsE.map (ecanonOff T qsE)) = [" +
             ", ".join(str(v[q]) for q in plus + minus) + "] := by decide +kernel")
    L.append("")
    L.append(f"theorem card : emax T qsE = {M} ∧ (symUniverse {M} ss).length = {n2} ∧ (symUniverse {M} ss).Nodup ∧"
             f" TpyE.length = {len(order)} ∧")
    L.append(f"    (∀ σ ∈ symUniverse {M} ss, ∃ ρ ∈ TpyE, ρ.s = σ ∨ ρ.t = σ) := by decide +kernel")
    L.append("")
    L.append("/-- 生成表の決定性・可逆性をカーネルの `decide` で直接（主定理とは独立に）。 -/")
    L.append("theorem TpyE_det_rev : Deterministic TpyE ∧ Reversible TpyE := by")
    L.append("  constructor <;> decide +kernel")
    L.append("")
    L.append(f"""/-- ε 逆向きの 4 状態化を {path.split('/')[-1]} に適用した結論。T' = `econv T qsE ss`（= `TpyE`）は
    4 状態（型 `KSt`）・記号は {n2} 要素の `symUniverse {M} ss` に入る（どれも実際に現れる）・
    規則 {len(order)} 本の決定的可逆機械。 -/
theorem main :
    let T' := econv T qsE ss
    let E := enc T (ecanonOff T qsE)
    Deterministic T' ∧ Reversible T' ∧
    (∀ c c' : Cfg St Ps Sy, Step T c c' → Live T c' →
      StepN T' (ecost T (ecanonOff T qsE) {M} c') (E c) (E c')) ∧
    (∀ (n : Nat) (c cf : Cfg St Ps Sy), HaltsIn T n c cf → (∃ h, cf.st = .halt h) →
      ∃ N, n ≤ N ∧ HaltsIn T' N (E c) (E cf)) ∧
    (∀ (N : Nat) (c : Cfg St Ps Sy) (e : Cfg KSt Ps (KSym Sy)), NoStuck T c →
      HaltsIn T' N (E c) e → ∃ n cf, HaltsIn T n c cf ∧ e = E cf) ∧
    (∀ c : Cfg St Ps Sy, NoStuck T c →
      ((∀ n cf, ¬ HaltsIn T n c cf) ↔ (∀ N e, ¬ HaltsIn T' N (E c) e))) ∧
    (∀ ρ ∈ T', ρ.s ∈ symUniverse {M} ss ∧ ρ.t ∈ symUniverse {M} ss) ∧
    (symUniverse {M} ss).length = {n2} ∧
    T' = TpyE ∧ T'.length = {len(order)} := by
  have h := econv_main (ss := ss) hW hD hR hQE hS
  have hc := card
  have hM : emax T qsE = {M} := hc.1
  rw [hM] at h
  refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, hc.2.1,
    econv_eq_py, ?_⟩
  rw [econv_eq_py]; exact hc.2.2.2.1""")
    L.append("")
    L.append(f"end URTM.Gen.{module}")
    print("\n".join(L))


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("path")
    ap.add_argument("solution", help="kstate5.py の解（k4, ε₋ = −1）の JSON")
    ap.add_argument("--module", required=True)
    ap.add_argument("--base", required=True, help="同じ記述ファイルから作った密な版のモジュール名（K10_8 など）")
    a = ap.parse_args()
    main(a.path, a.solution, a.module, a.base)
