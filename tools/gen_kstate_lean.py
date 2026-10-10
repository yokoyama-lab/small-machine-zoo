#!/usr/bin/env python3
"""Morita の記述ファイル → 定理 A（`lean/URTM/KState.lean`）を具体機械に適用する Lean モジュール。

    python3 tools/gen_kstate_lean.py data/urtm/urtm10-8.txt --module K10_8 > lean/URTM/Gen/K10_8.lean

生成されるもの（手で書き写さない。記述ファイルが唯一の正本）:
  * `St` / `Sy` / `Ps` — T の状態・記号・疑似状態（halt, null など）の有限型
  * `T : Machine St Ps Sy` — 記述ファイルの五つ組そのもの
  * `hW` `hD` `hR` `hQ` `hS` — 主定理の仮定をカーネルの `decide` で
  * `Tpy` — `tools/kstate.py`（k4, blocks 1,1）が出力する T' を Lean の項に写したもの
  * `conv_eq_py : conv T qs ss = Tpy` — Lean の変換と Python の生成表が**規則の並びまで一致**
  * `main` — 主定理 `conv_main` を適用した結論（4 状態、記号は (m+1)n 要素の集合に入る、規則数）

`--sparse BASE` を付けると定理 A の疎版（`lean/URTM/KStateSparse.lean` の `sconv`、
`tools/kstate_sparse_k4.py` の `Sparse`）版を生成する。T・St・Sy・Ps は生成済みの密な版モジュール
`URTM.Gen.BASE` のものを使い（CTSH の模倣の定理と同じ T）、状態の並び `qsS`（Sparse が選んだ順）と
Python の表 `TpyS`・記号の表 `symPy` だけを足す。

`--blocks b+,b-` を付けると定理 B（`lean/URTM/KStateB.lean` の `convB`）版を生成する。
状態は `BSt.H d b` / `BSt.A d b`、主定理は `convB_main`。

`lean/URTM/Gen/` は生成物なので gitignore 対象。`tools/gen_all_lean.sh` が CI で生成する。
"""

import argparse
import re
import sys

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from kstate import Construction, Machine  # noqa: E402

DIR = {"-": ".L", "0": ".Z", "+": ".R"}
KST = {"hp": "KSt.Hp", "hm": "KSt.Hm", "ap": "KSt.Ap", "am": "KSt.Am"}


def bst(name):
    m = re.match(r"^([ha])([pm])(\d*)$", name)
    assert m, name
    kind = "H" if m.group(1) == "h" else "A"
    d = ".R" if m.group(2) == "p" else ".L"
    return f"(BSt.{kind} {d} {int(m.group(3) or 1)})"


def emit_a(L, C, m, n, path):
    L.append("")
    L.append("/-- Lean の変換 `conv` と Python の生成表は、規則の並びまで一致する（カーネルで検査）。 -/")
    L.append("theorem conv_eq_py : conv T qs ss = Tpy := by decide +kernel")
    L.append("")
    L.append(f"theorem card : qs.length = {m} ∧ ss.length = {n} ∧ (symUniverse qs.length ss).length = {(m + 1) * n}"
             f" ∧ Tpy.length = {len(C.quints)} := by decide")
    L.append("")
    L.append(f"""/-- 定理 A を {path.split('/')[-1]} に適用した結論。T' = `conv T qs ss`（= `Tpy`）は
    4 状態（型 `KSt`）・記号は {(m + 1) * n} 要素の `symUniverse {m} ss` に入る・規則 {len(C.quints)} 本の
    決定的可逆機械で、T の任意の配置からの計算を模倣する。 -/
theorem main :
    let T' := conv T qs ss
    let off := canonOff T qs
    Deterministic T' ∧ Reversible T' ∧
    (∀ c c' : Cfg St Ps Sy, Step T c c' →
      StepN T' (cost T off (plusList T qs).length c') (enc T off c) (enc T off c')) ∧
    (∀ c : Cfg St Ps Sy, Halted T c ↔ Halted T' (enc T off c)) ∧
    (∀ (n : Nat) (c cf : Cfg St Ps Sy), HaltsIn T n c cf →
      ∃ N, n ≤ N ∧ HaltsIn T' N (enc T off c) (enc T off cf)) ∧
    (∀ (N : Nat) (c : Cfg St Ps Sy) (e : Cfg KSt Ps (KSym Sy)),
      HaltsIn T' N (enc T off c) e → ∃ n cf, HaltsIn T n c cf ∧ e = enc T off cf) ∧
    (∀ c : Cfg St Ps Sy, (∀ n cf, ¬ HaltsIn T n c cf) ↔ (∀ N e, ¬ HaltsIn T' N (enc T off c) e)) ∧
    (∀ ρ ∈ T', ρ.s ∈ symUniverse {m} ss ∧ ρ.t ∈ symUniverse {m} ss) ∧
    (symUniverse {m} ss).length = {(m + 1) * n} ∧
    T' = Tpy ∧ T'.length = {len(C.quints)} := by
  have h := conv_main hW hD hR hQ hS
  have hc := card
  refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, ?_, hc.2.2.1,
    conv_eq_py, ?_⟩
  · rw [← hc.1]; exact h.2.2.2.2.2.2.2
  · rw [conv_eq_py]; exact hc.2.2.2""")


def emit_b(L, C, m, n, blocks):
    bp, bm = blocks
    NB = C.B["+"] + C.B["-"]
    k = C.k
    L.append("")
    L.append(f"/-- Lean の変換 `convB`（b₊={bp}, b₋={bm}）と Python の生成表は、規則の並びまで一致する。 -/")
    L.append(f"theorem conv_eq_py : convB T qs ss {bp} {bm} = Tpy := by decide +kernel")
    L.append("")
    L.append(f"theorem card : canonBp T qs {bp} + canonBm T qs {bm} = {NB} ∧ ss.length = {n} ∧"
             f" (stUniverse {bp} {bm}).length = {k} ∧ (symUniverse {NB} ss).length = {(NB + 1) * n} ∧"
             f" Tpy.length = {len(C.quints)} := by decide")
    L.append("")
    L.append(f"""/-- 定理 B（b₊={bp}, b₋={bm}）の適用。T' = `convB T qs ss {bp} {bm}`（= `Tpy`）は
    状態 {k} 個の `stUniverse {bp} {bm}`・記号 {(NB + 1) * n} 個の `symUniverse {NB} ss` に収まる
    規則 {len(C.quints)} 本の決定的可逆機械で、T の任意の配置からの計算を模倣する。 -/
theorem main :
    let T' := convB T qs ss {bp} {bm}
    let blk := canonBlk T qs {bp} {bm}
    let off := canonOffB T qs {bp} {bm}
    Deterministic T' ∧ Reversible T' ∧
    (∀ c c' : Cfg St Ps Sy, Step T c c' →
      StepN T' (KStateB.cost T off (canonBp T qs {bp}) c') (KStateB.enc T blk off c) (KStateB.enc T blk off c')) ∧
    (∀ c : Cfg St Ps Sy, Halted T c ↔ Halted T' (KStateB.enc T blk off c)) ∧
    (∀ (n : Nat) (c cf : Cfg St Ps Sy), HaltsIn T n c cf →
      ∃ N, n ≤ N ∧ HaltsIn T' N (KStateB.enc T blk off c) (KStateB.enc T blk off cf)) ∧
    (∀ (N : Nat) (c : Cfg St Ps Sy) (e : Cfg BSt Ps (KSym Sy)),
      HaltsIn T' N (KStateB.enc T blk off c) e → ∃ n cf, HaltsIn T n c cf ∧ e = KStateB.enc T blk off cf) ∧
    (∀ c : Cfg St Ps Sy, (∀ n cf, ¬ HaltsIn T n c cf) ↔ (∀ N e, ¬ HaltsIn T' N (KStateB.enc T blk off c) e)) ∧
    (∀ ρ ∈ T', ρ.p ∈ stUniverse {bp} {bm} ∧ ∀ x, ρ.q = .go x → x ∈ stUniverse {bp} {bm}) ∧
    (∀ ρ ∈ T', ρ.s ∈ symUniverse {NB} ss ∧ ρ.t ∈ symUniverse {NB} ss) ∧
    (stUniverse {bp} {bm}).length = {k} ∧ (symUniverse {NB} ss).length = {(NB + 1) * n} ∧
    T' = Tpy ∧ T'.length = {len(C.quints)} := by
  have h := convB_main (T := T) (ss := ss) hW hD hR hQ hS (βp := {bp}) (βm := {bm}) (by decide) (by decide)
  have hc := card
  refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.1, ?_, hc.2.2.1, hc.2.2.2.1, conv_eq_py, ?_⟩
  · rw [← hc.1]; exact h.2.2.2.2.2.2.2.2
  · rw [conv_eq_py]; exact hc.2.2.2.2""")


def main_sparse(path, module, base):
    from kstate_sparse_k4 import Sparse
    T = Machine(path)
    C = Sparse(T, "k4", (1, 1))
    sid = {s: f"q{i}" for i, s in enumerate(T.states)}
    yid = {s: f"s{i}" for i, s in enumerate(T.symbols)}
    pid = {s: f"h{i}" for i, s in enumerate(T.pseudo)}

    def sym_T2(x):
        if C.is_counter(x):
            i, s = C.split_counter(x)
            return f"KSym.ctr {i} Sy.{yid[s]}"
        return f"KSym.pl Sy.{yid[x]}"

    def tgt_T2(q):
        return f".halt Ps.{pid[q]}" if q in T.pseudo else f".go {KST[q]}"

    order = C.Qd["+"] + C.Qd["-"]
    m, n, n2, r2 = len(T.states), len(T.symbols), len(C.symbols), len(C.quints)
    L = []
    L.append("/-")
    L.append(f"  {path.split('/')[-1]} から自動生成（tools/gen_kstate_lean.py --sparse {base}）。手で編集しないこと。")
    L.append(f"  定理 A の疎版（kstate_sparse_k4.py）: 状態 {len(C.states)} / 記号 {n2} / 五つ組 {r2}"
             f"（密なら記号 {(m + 1) * n}）")
    L.append("  状態の並び（下から）: + は " + ", ".join(C.Qd["+"]) + "、- は " + ", ".join(C.Qd["-"]))
    L.append("-/")
    L.append("import URTM.KStateSparse")
    L.append(f"import URTM.Gen.{base}")
    L.append("")
    L.append("set_option maxRecDepth 100000")
    L.append("set_option maxHeartbeats 0")
    L.append("")
    L.append(f"namespace URTM.Gen.{module}")
    L.append("")
    L.append(f"open URTM URTM.KState URTM.KStateSparse URTM.Gen.{base}")
    L.append("")
    L.append("/-- 疎版の状態の並び（Q₊ を下から、続いて Q₋ を下から）。番号は `canonOff T qsS`。 -/")
    L.append("def qsS : List St := [" + ", ".join(f".{sid[q]}" for q in order) + "]")
    L.append("")
    L.append("/-- `tools/kstate_sparse_k4.py` が生成した疎版 T' をそのまま写したもの。 -/")
    L.append("def TpyS : Machine KSt Ps (KSym Sy) := [")
    L.append(",\n".join(f"  ⟨{KST[p]}, {sym_T2(s)}, {sym_T2(t)}, {DIR[d]}, {tgt_T2(q)}⟩"
                        for (p, s, t, d, q) in C.quints))
    L.append("]")
    L.append("")
    L.append("/-- `tools/kstate_sparse_k4.py` の記号の表（並びまで）。 -/")
    L.append("def symPy : List (KSym Sy) := [" + ", ".join(sym_T2(x) for x in C.symbols) + "]")
    L.append("")
    L.append("theorem hQS : ∀ q, q ∈ qsS := by intro q; cases q <;> decide")
    L.append("")
    L.append("/-- Lean の疎版 `sconv` と Python の生成表は、規則の並びまで一致する（カーネルで検査）。 -/")
    L.append("theorem sconv_eq_py : sconv T qsS ss = TpyS := by decide +kernel")
    L.append("")
    L.append("/-- Lean の記号の全体 `sparseUniverse` と Python の記号の表は、並びまで一致する。 -/")
    L.append("theorem universe_eq_py : sparseUniverse T qsS ss = symPy := by decide +kernel")
    L.append("")
    L.append(f"theorem card : qsS.length = {m} ∧ (sparseUniverse T qsS ss).length = {n2} ∧"
             f" TpyS.length = {r2} := by decide +kernel")
    L.append("")
    L.append(f"""/-- 定理 A の疎版を {path.split('/')[-1]} に適用した結論。T' = `sconv T qsS ss`（= `TpyS`）は
    4 状態（型 `KSt`）・記号は {n2} 要素の `sparseUniverse T qsS ss` に入る・規則 {r2} 本の決定的可逆機械。 -/
theorem main :
    let T' := sconv T qsS ss
    let E := enc T (canonOff T qsS)
    Deterministic T' ∧ Reversible T' ∧
    (∀ c c' : Cfg St Ps Sy, Step T c c' → Live T c' →
      StepN T' (cost T (canonOff T qsS) (plusList T qsS).length c') (E c) (E c')) ∧
    (∀ (n : Nat) (c cf : Cfg St Ps Sy), HaltsIn T n c cf → (∃ h, cf.st = .halt h) →
      ∃ N, n ≤ N ∧ HaltsIn T' N (E c) (E cf)) ∧
    (∀ (N : Nat) (c : Cfg St Ps Sy) (e : Cfg KSt Ps (KSym Sy)), NoStuck T c →
      HaltsIn T' N (E c) e → ∃ n cf, HaltsIn T n c cf ∧ e = E cf) ∧
    (∀ c : Cfg St Ps Sy, NoStuck T c →
      ((∀ n cf, ¬ HaltsIn T n c cf) ↔ (∀ N e, ¬ HaltsIn T' N (E c) e))) ∧
    (∀ ρ ∈ T', ρ.s ∈ sparseUniverse T qsS ss ∧ ρ.t ∈ sparseUniverse T qsS ss) ∧
    (sparseUniverse T qsS ss).length = {n2} ∧
    T' = TpyS ∧ T'.length = {r2} := by
  have h := sconv_main (ss := ss) hW hD hR hQS hS
  have hc := card
  refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2, hc.2.1,
    sconv_eq_py, ?_⟩
  rw [sconv_eq_py]; exact hc.2.2""")
    L.append("")
    L.append(f"end URTM.Gen.{module}")
    print("\n".join(L))


def main(path, module, blocks=None):
    T = Machine(path)
    C = Construction(T, variant="k4", blocks=blocks or (1, 1))
    st2 = bst if blocks else (lambda q: KST[q])
    sid = {s: f"q{i}" for i, s in enumerate(T.states)}
    yid = {s: f"s{i}" for i, s in enumerate(T.symbols)}
    pid = {s: f"h{i}" for i, s in enumerate(T.pseudo)}

    def tgt_T(q):
        return f".halt Ps.{pid[q]}" if q in T.pseudo else f".go St.{sid[q]}"

    def sym_T2(x):
        if C.is_counter(x):
            i, s = C.split_counter(x)
            return f"KSym.ctr {i} Sy.{yid[s]}"
        return f"KSym.pl Sy.{yid[x]}"

    def tgt_T2(q):
        return f".halt Ps.{pid[q]}" if q in T.pseudo else f".go {st2(q)}"

    m, n = len(T.states), len(T.symbols)
    L = []
    L.append("/-")
    L.append(f"  {path.split('/')[-1]} から自動生成（tools/gen_kstate_lean.py）。手で編集しないこと。")
    L.append(f"  状態 {m} / 記号 {n} / 疑似状態 {len(T.pseudo)} / 五つ組 {len(T.quints)}")
    L.append(f"  kstate.py k4 の出力: 状態 {len(C.states)} / 記号 {len(C.symbols)} / 五つ組 {len(C.quints)}")
    L.append("-/")
    L.append("import URTM.KStateB" if blocks else "import URTM.KState")
    L.append("")
    L.append("set_option maxRecDepth 100000")
    L.append("set_option maxHeartbeats 0")
    L.append("")
    L.append(f"namespace URTM.Gen.{module}")
    L.append("")
    L.append("open URTM URTM.KState" + (" URTM.KStateB" if blocks else ""))
    L.append("")
    L.append("-- 状態: " + ", ".join(f"{v}={k}" for k, v in sid.items()))
    L.append("inductive St where\n  | " + " | ".join(sid.values()) + "\n  deriving DecidableEq, Repr")
    L.append("-- 記号: " + ", ".join(f"{v}={k}" for k, v in yid.items()))
    L.append("inductive Sy where\n  | " + " | ".join(yid.values()) + "\n  deriving DecidableEq, Repr")
    L.append("-- 疑似状態: " + ", ".join(f"{v}={k}" for k, v in pid.items()))
    L.append("inductive Ps where\n  | " + " | ".join(pid.values()) + "\n  deriving DecidableEq, Repr")
    L.append("")
    L.append("def qs : List St := [" + ", ".join(f".{v}" for v in sid.values()) + "]")
    L.append("def ss : List Sy := [" + ", ".join(f".{v}" for v in yid.values()) + "]")
    L.append("")
    L.append("/-- 記述ファイルの五つ組。 -/")
    L.append("def T : Machine St Ps Sy := [")
    L.append(",\n".join(f"  ⟨.{sid[p]}, .{yid[s]}, .{yid[t]}, {DIR[d]}, {tgt_T(q)}⟩"
                        for (p, s, t, d, q) in T.quints))
    L.append("]")
    L.append("")
    L.append(f"/-- `tools/kstate.py`（k4, blocks {blocks or (1, 1)}）が生成した T' をそのまま写したもの。 -/")
    L.append(f"def Tpy : Machine {'BSt' if blocks else 'KSt'} Ps (KSym Sy) := [")
    L.append(",\n".join(f"  ⟨{st2(p)}, {sym_T2(s)}, {sym_T2(t)}, {DIR[d]}, {tgt_T2(q)}⟩"
                        for (p, s, t, d, q) in C.quints))
    L.append("]")
    L.append("")
    L.append("theorem hW : ZeroShiftHalts T := by decide")
    L.append("theorem hD : Deterministic T := by decide")
    L.append("theorem hR : Reversible T := by decide")
    L.append("theorem hQ : ∀ q, q ∈ qs := by intro q; cases q <;> decide")
    L.append("theorem hS : ∀ s, s ∈ ss := by intro s; cases s <;> decide")
    if blocks:
        emit_b(L, C, m, n, blocks)
    else:
        emit_a(L, C, m, n, path)
    L.append("")
    L.append(f"end URTM.Gen.{module}")
    print("\n".join(L))


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("path")
    ap.add_argument("--module", required=True)
    ap.add_argument("--blocks", default=None, help="b+,b-（定理 B 版を生成）")
    ap.add_argument("--sparse", default=None, metavar="BASE",
                    help="定理 A の疎版を生成（BASE は同じ記述ファイルから作った密な版のモジュール名）")
    a = ap.parse_args()
    if a.sparse:
        main_sparse(a.path, a.module, a.sparse)
        sys.exit(0)
    main(a.path, a.module, tuple(int(x) for x in a.blocks.split(",")) if a.blocks else None)
