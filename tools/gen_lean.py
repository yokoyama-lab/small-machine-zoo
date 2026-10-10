#!/usr/bin/env python3
"""URTM 記述ファイル → Lean 4 のモジュール。

Morita の記述ファイルを唯一の正本とし、Lean 側の表は必ずここから生成する
（手で書き写すと、写し間違いを検証したことにならない）。

    python3 tools/gen_lean.py data/urtm/urtm17-5.txt --module M17_5 > lean/URTM/M17_5.lean

生成されるもの:
  * `table` — 五つ組の列（状態・記号は通し番号）
  * `det_ok` / `rev_ok` — 決定性・可逆性を `decide` で**カーネル検証**する定理
  * `case<i>` — 記述ファイルの各初期配置について、主定理と同じ `KState` の機械
    （`Gen/K*.lean` の `T`、(4,168) は `Gen/F4_168.lean` の `T4`、(138,2) は `Gen/F138_2.lean` の `T138`）が
    **ちょうど** Morita の記載したステップ数で停止し、停止配置が `e<i>`（記述ファイルの表を Python で
    実行したもの）であること: `HaltsIn T n (z<i>.cfg bk) (e<i>.cfg bk)`。
    検査器 `URTM.KState.Run.check`（`lean/URTM/KRun.lean`、健全性は一般証明）を
    **カーネルの評価**（`decide +kernel`）で走らせる。`native_decide` は使わない。

オプション:
  --runs kernel|native 実行例の出し方。kernel（Morita の 8 台の既定）は上の `case<i>`。native（それ以外の
                       記述ファイルの既定。kstate の生成機械・CI の変異注入）は従来どおり Basic の意味論
                       （`haltsIn`）の停止ステップ数を `native_decide` で照合する（有界全数検査。層2）。
  --chunk N            kernel の実行例で、N ステップを超える実行を N ステップずつの区間に分け、区間ごとに
                       別の定理（`reach`）としてカーネルに渡す（既定 500。カーネルのメモリを区間で抑える）。
  --max-steps N        期待ステップ数が N を超える例は省く（既定 20000）
  --det-rev native_decide
                       det_ok / rev_ok を `native_decide` にする。`decide` は |δ|² に比例して
                       カーネルで時間がかかる（226 本で 23 秒、386 本で 76 秒。docs/03 §9 の計測）ので、
                       層3 の候補（kstate の生成機械など）を CI で多数回すときだけ使う。
                       **層1 の要件はカーネル `decide` のまま**（Morita の 8 台はこのオプションを使わない）。
"""

import sys

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from check_urtm import parse  # noqa: E402
from simulate import blank_of, read_cases, run as sim_run  # noqa: E402
from kstate import Machine  # noqa: E402

DIR = {"-": "Dir.L", "0": "Dir.Z", "+": "Dir.R"}

# 機械ごとの KState 側の表（生成済みモジュール）と、記述ファイルの名前 → Lean の項。
# (4,168)・(138,2) の表は gen_conv_lean.py が構造化した記号で書き出したもの（F4_168・F138_2）。
# KState 側の表（Gen/K*・F4_168・F138_2）がある記述ファイル。これ以外（kstate の生成機械、CI の変異注入）は
# 従来どおり Basic の意味論と native_decide で出す（--runs native）。
KNOWN = {f"urtm{k}.txt" for k in ("10-8", "13-7", "15-6", "17-5", "24-4", "32-3", "4-168", "138-2")}


def kctx(path):
    """KState 側の機械の文脈: import・open・表の名前・Zip の型・状態/記号の写像・空白。"""
    import gen_conv_lean  # 遅延 import（gen_ctsh_lean が CORRECTIONS をここから読むので循環を避ける）
    fname = path.split("/")[-1]
    if fname == "urtm4-168.txt":
        B = Machine(path.replace(fname, "urtm10-8.txt"))
        yid = {s: f"s{i}" for i, s in enumerate(B.symbols)}
        return dict(imp="URTM.Gen.F4_168", opn="URTM.Conv55 URTM.Gen.K10_8 URTM.Gen.F4_168", T="T4",
                    ty="Zip FSt Ps (FSym Sy)",
                    st=lambda q: f".go .{gen_conv_lean.STATE[q]}",
                    sym=lambda x: gen_conv_lean.sym(x, yid))
    if fname == "urtm138-2.txt":
        B = Machine(path.replace(fname, "urtm24-4.txt"))
        sid = {s: f"q{i}" for i, s in enumerate(B.states)}
        return dict(imp="URTM.Gen.F138_2", opn="URTM.Conv54 URTM.Gen.K24_4 URTM.Gen.F138_2", T="T138",
                    ty="Zip (BSt St) Ps Bool",
                    st=lambda q: f".go {gen_conv_lean.bst(q, sid)}",
                    sym=lambda x: {"0": "false", "1": "true"}[str(x)])
    K = Machine(path)
    sid = {s: f"q{i}" for i, s in enumerate(K.states)}
    yid = {s: f"s{i}" for i, s in enumerate(K.symbols)}
    pid = {s: f"h{i}" for i, s in enumerate(K.pseudo)}
    km = "K" + fname[len("urtm"):-len(".txt")].replace("-", "_")
    return dict(imp=f"URTM.Gen.{km}", opn=f"URTM.Gen.{km}", T="T", ty="Zip St Ps Sy",
                st=lambda q: f".halt Ps.{pid[q]}" if q in pid else f".go St.{sid[q]}",
                sym=lambda x: f".{yid[x]}")


def zrun(quints, blank, st, pos, tape, limit, chunk=None):
    """KRun.zstep と同じ形でジッパーを進める（停止配置のリストの形まで Lean と一致させる）。
    返り値 (ステップ数, 停止配置, chunk ステップごとの途中配置の列)。配置は (状態, 左（近い順）, ヘッド, 右)。
    左端から出たら AssertionError。"""
    delta = {(p, s): (t, d, q) for (p, s, t, d, q) in quints}
    tape = list(tape) + [blank] * max(0, pos + 1 - len(tape))
    l, h, r = list(reversed(tape[:pos])), tape[pos], tape[pos + 1:]
    n, marks = 0, []
    while (st, h) in delta and n <= limit:
        t, d, st = delta[(st, h)]
        if d == "+":
            l, h, r = [t] + l, (r[0] if r else blank), r[1:]
        elif d == "0":
            h = t
        else:
            assert l, "左端から出た"
            l, h, r = l[1:], l[0], [t] + r
        n += 1
        if chunk and n % chunk == 0:
            marks.append((st, l, h, r))
    if chunk and marks and n % chunk == 0:
        marks.pop()  # 最後の区切りが停止配置そのものなら、停止の検査の側に回す
    return n, (st, l, h, r), marks


# 記述ファイルのコメントの誤植を補正する（STATUS.md「既知の不一致」を参照）。
# urtm13-7.txt の case4 は 1073 と書かれているが、独立実装のシミュレータ・
# Lean の native_decide・Morita 2017 の本文（U13,7 と U10,8 の時間は同じ）の
# 3 つが 1173 で一致する。補正はここに集約し、記述ファイルは書き換えない。
CORRECTIONS = {("urtm13-7.txt", 4): 1173}


def main(path, module, max_steps, det_rev="decide", runs=None, chunk=500):
    assert det_rev in ("decide", "native_decide"), det_rev
    if runs is None:
        runs = "kernel" if path.split("/")[-1] in KNOWN else "native"
    assert runs in ("kernel", "native"), runs
    how = "カーネルで検証（`decide`）" if det_rev == "decide" else "`native_decide`（コンパイル済みコードの実行。層3 候補向け）"
    states_decl, symbols, quints = parse(path)
    if not symbols:
        symbols = list(dict.fromkeys([q[1] for q in quints] + [q[2] for q in quints]))
    states = list(dict.fromkeys(list(states_decl or [])
                                + [q[0] for q in quints] + [q[4] for q in quints]))
    sid = {s: i for i, s in enumerate(states)}
    yid = {s: i for i, s in enumerate(symbols)}
    blank = blank_of(path)

    L = []
    L.append("/-")
    L.append(f"  {path.split('/')[-1]} から自動生成（tools/gen_lean.py）。手で編集しないこと。")
    L.append("")
    L.append(f"  状態 {len(states_decl or states)} / 記号 {len(symbols)} / 五つ組 {len(quints)}")
    L.append("-/")
    L.append("import URTM.Basic")
    if runs == "kernel":
        L.append("import URTM.KRun")
        L.append(f"import {kctx(path)['imp']}")
    L.append("")
    L.append("-- 深い再帰（数千ステップの実行）を許す")
    L.append("set_option maxRecDepth 1000000")
    L.append("")
    L.append(f"namespace URTM.{module}")
    L.append("")
    L.append("-- 状態の番号: " + ", ".join(f"{i}={s}" for s, i in sid.items()))
    L.append("-- 記号の番号: " + ", ".join(f"{i}={s}" for s, i in yid.items()))
    L.append("")
    L.append(f"def blank : Nat := {yid[blank]}")
    L.append("")
    L.append("def table : List Quint := [")
    body = []
    for (p, s, t, d, q) in quints:
        body.append(f"  ⟨{sid[p]}, {yid[s]}, {yid[t]}, {DIR[d]}, {sid[q]}⟩")
    L.append(",\n".join(body))
    L.append("]")
    L.append("")
    L.append(f"/-- 決定性。{how}。 -/")
    L.append(f"theorem det_ok : URTM.deterministic table = true := by {det_rev}")
    L.append("")
    L.append(f"/-- 可逆性条件（Morita 2017, Def. 5.4）。{how}。 -/")
    L.append(f"theorem rev_ok : URTM.reversible table = true := by {det_rev}")
    L.append("")

    fname = path.split("/")[-1]
    if runs == "native":
        n = 0
        for idx, (st, pos, tape, exp_steps, exp_out) in enumerate(read_cases(path)):
            exp_steps = CORRECTIONS.get((fname, idx), exp_steps)
            if exp_steps is None or exp_steps > max_steps:
                continue
            cells = ", ".join(str(yid[x]) for x in tape)
            L.append(f"def init{n} : Conf :=")
            L.append(f"  {{ st := {sid[st]}, pos := {pos}, tape := #[{cells}] }}")
            L.append(f"/-- 記述ファイルの期待値: {exp_steps} ステップで停止"
                     + (f"（出力 {exp_out}）" if exp_out else "") + " -/")
            L.append(f"example : haltsIn table blank {exp_steps + 5} init{n} "
                     f"= some {exp_steps} := by native_decide")
            L.append("")
            n += 1
        L.append(f"-- 実行例 {n} 件（`native_decide` = 有界全数検査。層2）")
        L.append("")
        L.append(f"end URTM.{module}")
        print("\n".join(L))
        return

    n = 0
    K = kctx(path)
    lst = lambda xs: "[" + ", ".join(K["sym"](x) for x in xs) + "]"
    zip_ = lambda q, l, h, r: f"⟨{K['st'](q)}, {lst(l)}, {K['sym'](h)}, {lst(r)}⟩"
    bk = K["sym"](blank)
    ex = []
    for idx, (st, pos, tape, exp_steps, exp_out) in enumerate(read_cases(path)):
        exp_steps = CORRECTIONS.get((fname, idx), exp_steps)
        if exp_steps is None or exp_steps > max_steps:
            continue
        steps, (fq, fl, fh, fr), marks = zrun(quints, blank, st, pos, tape, exp_steps + 5, chunk)
        # 独立実装（simulate.run、片側テープの配列）と停止ステップ数を突き合わせる
        s2, _, _ = sim_run(quints, blank, st, pos, tape, exp_steps + 5)
        assert steps == exp_steps == s2, (fname, idx, steps, exp_steps, s2)
        tape = list(tape) + [blank] * max(0, pos + 1 - len(tape))
        ex.append(f"/-- 記述ファイルの初期配置 {idx}（状態 {st}, ヘッド {pos}）。 -/")
        ex.append(f"def z{n} : {K['ty']} :=\n  {zip_(st, list(reversed(tape[:pos])), tape[pos], tape[pos + 1:])}")
        ex.append(f"/-- 停止配置（状態 {fq}, ヘッド {len(fl)}。記述ファイルの表を Python で実行したもの）。 -/")
        ex.append(f"def e{n} : {K['ty']} :=\n  {zip_(fq, fl, fh, fr)}")
        # 長い実行は chunk ステップごとに区切り、区間ごとに別の定理としてカーネルに渡す（メモリを区間で抑える）
        prev, names = f"z{n}", []
        for j, (q, l, h, r) in enumerate(marks, 1):
            ex.append(f"/-- 途中配置（{j * chunk} ステップ後、状態 {q}, ヘッド {len(l)}）。 -/")
            ex.append(f"def z{n}_{j} : {K['ty']} :=\n  {zip_(q, l, h, r)}")
            ex.append(f"theorem r{n}_{j} : reach {bk} {K['T']} {chunk} {prev} z{n}_{j} = true := by decide +kernel")
            prev = f"z{n}_{j}"
            names.append(f"r{n}_{j}")
        rest = exp_steps - chunk * len(marks) if chunk else exp_steps
        ex.append(f"/-- 記述ファイルの期待値: {exp_steps} ステップで停止"
                  + (f"（出力 {exp_out}）" if exp_out else "")
                  + "。カーネルの評価で照合（`decide +kernel`）"
                  + (f"。{chunk} ステップずつ {len(marks)} 区間 + 残り {rest} ステップ" if marks else "")
                  + "。 -/")
        # 後ろから: 停止までの残りを区間ごとの定理にする（1 つの定理で合成する数の等式は 1 個だけ）
        tail = f"halts_of_check (bk := {bk}) (T := {K['T']}) (n := {rest}) (z := {prev}) (e := e{n}) (by decide +kernel)"
        for j in range(len(marks), 0, -1):
            src = f"z{n}_{j}"
            ex.append(f"theorem h{n}_{j} : HaltsIn {K['T']} {rest + chunk * (len(marks) - j)} ({src}.cfg {bk}) (e{n}.cfg {bk}) :=\n  {tail}")
            tail = f"halts_of_reach r{n}_{j} h{n}_{j}"
        ex.append(f"theorem case{n} : HaltsIn {K['T']} {exp_steps} (z{n}.cfg {bk}) (e{n}.cfg {bk}) :=\n  {tail}")
        ex.append("")
        n += 1
    L.append(f"end URTM.{module}")
    L.append("")
    L.append(f"namespace URTM.{module}.K")
    L.append("")
    L.append(f"open URTM URTM.KState URTM.KState.Run {K['opn']}")
    L.append("")
    L += ex
    L.append(f"-- 実行例 {n} 件（主定理と同じ KState の機械について、カーネル検証。コンパイル済みコードの実行を使わない）")
    L.append("")
    L.append(f"end URTM.{module}.K")
    print("\n".join(L))


if __name__ == "__main__":
    mod = sys.argv[sys.argv.index("--module") + 1] if "--module" in sys.argv else "M"
    mx = int(sys.argv[sys.argv.index("--max-steps") + 1]) if "--max-steps" in sys.argv else 20000
    dr = sys.argv[sys.argv.index("--det-rev") + 1] if "--det-rev" in sys.argv else "decide"
    rn = sys.argv[sys.argv.index("--runs") + 1] if "--runs" in sys.argv else None
    ch = int(sys.argv[sys.argv.index("--chunk") + 1]) if "--chunk" in sys.argv else 500
    main(sys.argv[1], mod, mx, dr, rn, ch)
