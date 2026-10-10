#!/usr/bin/env python3
"""Morita の変換で得た URTM(4,168) の記述ファイル → 構造化した記号で書いた Lean モジュール。

    python3 tools/gen_conv_lean.py table   data/urtm/urtm4-168.txt data/urtm/urtm10-8.txt > lean/URTM/Gen/F4_168.lean
    python3 tools/gen_conv_lean.py example data/urtm/urtm4-168.txt data/urtm/urtm10-8.txt > lean/URTM/Gen/C4_168.lean

`table`: urtm4-168.txt の 381 本を、状態 r0 r1 l0 l1 ↦ `FSt.R0 …`、記号 u ↦ `.pl u`、[u,i,u] ↦ `.up u i`、
[u,i,d] ↦ `.dn u i`（u は urtm10-8.txt の記号を生成モジュール K10_8 と同じ番号で）として書き出す。
Lean の変換 `URTM.Conv55.conv`（Theorem 5.5）とは独立に、記述ファイルの文字列だけから作る。
一致は `CTSH4_168Main.lean` で `decide` が確かめる。

`example`: 記述ファイルの initial_conf を、(10,8) の CTSH の符号化に読み戻し（`gen_ctsh_lean.decode`）、
Lean の `E (encC C w)` が記述ファイルの初期配置そのもの（窓の中のテープ・ヘッド位置・状態）であること、
表を Python で停止まで実行した配置が `E (unhalt f10 (finCfg C vf mf rm))` と一致することを `decide` で照合する。

`lean/URTM/Gen/` は生成物（gitignore）。`tools/gen_all_lean.sh` が CI で生成する。
"""

import re
import sys

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from check_urtm import parse  # noqa: E402
from kstate import Machine  # noqa: E402
from simulate import read_cases, run, blank_of  # noqa: E402
from gen_ctsh_lean import decode, ctsh_run, lch  # noqa: E402
from check_urtm import split_top  # noqa: E402

STATE = {"r0": "R0", "r1": "R1", "l0": "L0", "l1": "L1"}
DIR = {"-": ".L", "0": ".Z", "+": ".R"}


def sym(x, yid):
    """記述ファイルの記号 → Lean の FSym 項。"""
    m = re.fullmatch(r"\[(.+),(\d+),([ud])\]", x)
    if m:
        k = {"u": "up", "d": "dn"}[m.group(3)]
        return f"(.{k} .{yid[m.group(1)]} {int(m.group(2))})"
    return f"(.pl .{yid[x]})"


def table(path, base):
    B = Machine(base)
    yid = {s: f"s{i}" for i, s in enumerate(B.symbols)}
    _, _, quints = parse(path)
    L = []
    L.append(f"/-\n  {path.split('/')[-1]} から自動生成（tools/gen_conv_lean.py table）。手で編集しないこと。\n"
             f"  状態 r0 r1 l0 l1 ↦ FSt.R0 R1 L0 L1、記号は {base.split('/')[-1]} の番号（K10_8 と同じ）で構造化。\n"
             f"  五つ組 {len(quints)} 本。\n-/")
    L.append("import URTM.Conv55")
    L.append("import URTM.Gen.K10_8")
    L.append("")
    L.append("set_option maxRecDepth 100000")
    L.append("")
    L.append("namespace URTM.Gen.F4_168")
    L.append("")
    L.append("open URTM URTM.KState URTM.Conv55 URTM.Gen.K10_8")
    L.append("")
    L.append("/-- 記述ファイルの五つ組。 -/")
    L.append("def T4 : Machine FSt Ps (FSym Sy) := [")
    rows = []
    for (p, s, t, d, q) in quints:
        rows.append(f"⟨.{STATE[p]}, {sym(s, yid)}, {sym(t, yid)}, {DIR[d]}, .go .{STATE[q]}⟩")
    L.append(",\n".join(rows))
    L.append("]")
    L.append("")
    L.append("end URTM.Gen.F4_168")
    print("\n".join(L))


def run4(path, state, pos, tape):
    """記述ファイルの表を停止まで実行（(状態, ヘッド位置, テープ, ステップ数)）。simulate.run と照合する。"""
    _, _, quints = parse(path)
    blank = blank_of(path)
    delta = {(p, s): (t, d, q) for (p, s, t, d, q) in quints}
    tp, q, h, n = list(tape), state, pos, 0
    while True:
        while h >= len(tp):
            tp.append(blank)
        assert h >= 0
        key = (q, tp[h])
        if key not in delta:
            break
        t, d, q = delta[key]
        tp[h] = t
        h += {"-": -1, "0": 0, "+": 1}[d]
        n += 1
    steps, final, why = run(quints, blank, state, pos, tape, 10 ** 6)
    assert steps == n, (steps, n, why)
    return q, h, tp, n


def example(path, base):
    B = Machine(base)
    yid = {s: f"s{i}" for i, s in enumerate(B.symbols)}
    L = []
    L.append(f"/-\n  {path.split('/')[-1]} の試験例から自動生成（tools/gen_conv_lean.py example）。手で編集しないこと。\n-/")
    L.append("import URTM.CTSH4_168Main")
    L.append("")
    L.append("set_option maxRecDepth 100000")
    L.append("")
    L.append("namespace URTM.Gen.C4_168")
    L.append("")
    L.append("open URTM URTM.KState URTM.CTSH URTM.Conv55 URTM.SimLemmas URTM.CTSH.U4_168 URTM.Gen.F4_168")
    L.append("open URTM.CTSH.U10_8 (encC)")
    n = 0
    for (state, pos, tape, steps, out) in read_cases(path):
        n += 1
        # 初期配置のヘッドの記号 [s,0,u] を s に戻して (10,8) の符号化として読む
        m = re.fullmatch(r"\[(.+),0,u\]", tape[pos])
        assert m and state == "r0", (state, tape[pos])
        plain = list(tape)
        plain[pos] = m.group(1)
        C, w = decode(pos, plain)
        erased = []
        (vf, mf), halted, cyc = ctsh_run(C, w, 1000, erased)
        assert halted and steps is not None, (C, w)
        assert out == "".join(x.lower() for x in vf) or (out == "null" and vf == []), (out, vf)
        q, h, ftape, nsteps = run4(path, state, pos, tape)
        assert nsteps == steps, (nsteps, steps)
        blank = "b"
        W = max(len(tape), len(ftape)) + 2
        itape = list(tape) + [blank] * (W - len(tape))
        ftape = list(ftape) + [blank] * (W - len(ftape))
        L.append("")
        L.append(f"-- 例 {n}: initial_conf([{state},{pos},[{','.join(tape)}]])  原典のコメント: {steps} {out}")
        L.append(f"def C{n} : CTSH := [" + ", ".join(lch(x) for x in C) + "]")
        L.append(f"def w{n} : List Ch := {lch(w)}")
        L.append(f"/-- `E (encC C{n} w{n})` は記述ファイルの初期配置（状態 r0, ヘッド {pos}）と、"
                 f"テープの窓 [0, {W}) で一致する（窓の外は空白 b）。 -/")
        L.append(f"theorem enc{n} : (E (encC C{n} w{n})).st = .go .R0 ∧ (E (encC C{n} w{n})).pos = {pos} ∧\n"
                 f"    (List.range {W}).map (fun (i : Nat) => (E (encC C{n} w{n})).tape (Int.ofNat i)) =\n"
                 f"      [" + ", ".join(sym(x, yid) for x in itape) + "] := by decide")
        L.append(f"theorem run{n} : run C{n} 1000 (w{n}, 0) = (({lch(vf)}, {mf}), true) := by decide +kernel")
        L.append("/-- 一般定理の具体例への適用: U4_168 は初期配置から停止する。 -/")
        L.append(f"theorem halts{n} : ∃ N rm, HaltsIn T4 N (E (encC C{n} w{n})) (fin4 C{n} {lch(vf)} {mf} rm) := by")
        L.append(f"  obtain ⟨k, hk⟩ := run_sound 1000 (by decide) run{n}")
        L.append(f"  obtain ⟨N, rm, -, h⟩ := (urtm4_168_simulates_ctsh C{n} w{n}).2.2.2.2.1 k _ _ hk")
        L.append("  exact ⟨N, rm, h⟩")
        L.append(f"/-- 停止配置の形の照合: 記述ファイルの表を Python で {nsteps} ステップ実行した停止配置"
                 f"（{q}, ヘッド {h}）が `fin4 C{n} {''.join(vf) or 'λ'} {mf} rm`（rm = {''.join(erased) or 'λ'}）と"
                 f"テープの窓 [0, {W}) で一致する。 -/")
        L.append(f"theorem fin{n} : (fin4 C{n} {lch(vf)} {mf} {lch(erased)}).st = .go .{STATE[q]} ∧\n"
                 f"    (fin4 C{n} {lch(vf)} {mf} {lch(erased)}).pos = {h} ∧\n"
                 f"    (List.range {W}).map (fun (i : Nat) => (fin4 C{n} {lch(vf)} {mf} {lch(erased)}).tape (Int.ofNat i)) =\n"
                 f"      [" + ", ".join(sym(x, yid) for x in ftape) + "] := by decide")
    L.append("")
    L.append("end URTM.Gen.C4_168")
    print("\n".join(L))


# ---------------------------------------------------------------------------
# URTM(138,2)（Theorem 5.4 の 2 ビット版で U24_4 から変換）
# ---------------------------------------------------------------------------

CODE2 = {"b": (0, 0), "y": (0, 1), "n": (1, 0), "*": (1, 1)}  # urtm138-2.txt の codes(...) の注記どおり


def bst(x, sid):
    """[name_r] / [name_r,x] / [name_w,x] / [name_s] → Lean の BSt 項。"""
    m = re.fullmatch(r"\[(.+)_([rws])(?:,([01]))?\]", x)
    assert m, x
    q, k, b = sid[m.group(1)], m.group(2), m.group(3)
    if k == "r" and b is None:
        return f"(.r .{q})"
    if k == "r":
        return f"(.r1 .{q} {'true' if b == '1' else 'false'})"
    if k == "w":
        return f"(.w .{q} {'true' if b == '1' else 'false'})"
    assert b is None
    return f"(.s .{q})"


def table2(path, base):
    B = Machine(base)
    sid = {s: f"q{i}" for i, s in enumerate(B.states)}
    _, _, quints = parse(path)
    L = []
    L.append(f"/-\n  {path.split('/')[-1]} から自動生成（tools/gen_conv_lean.py table2）。手で編集しないこと。\n"
             f"  状態 [q_r] [q_r,x] [q_w,x] [q_s] ↦ BSt.r / r1 / w / s（q は {base.split('/')[-1]} の番号、K24_4 と同じ）、"
             f"記号 0 1 ↦ false true。\n  五つ組 {len(quints)} 本。\n-/")
    L += ["import URTM.Conv54", "import URTM.Gen.K24_4", "", "set_option maxRecDepth 100000", "",
          "namespace URTM.Gen.F138_2", "", "open URTM URTM.KState URTM.Conv54 URTM.Gen.K24_4", "",
          "/-- 記述ファイルの五つ組。 -/", "def T138 : Machine (BSt St) Ps Bool := ["]
    rows = []
    for (p, s, t, d, q) in quints:
        bit = {"0": "false", "1": "true"}
        rows.append(f"⟨{bst(p, sid)}, {bit[str(s)]}, {bit[str(t)]}, {DIR[d]}, .go {bst(q, sid)}⟩")
    L.append(",\n".join(rows))
    L += ["]", "", "end URTM.Gen.F138_2"]
    print("\n".join(L))


def example2(path, base):
    L = []
    L.append(f"/-\n  {path.split('/')[-1]} の試験例から自動生成（tools/gen_conv_lean.py example2）。手で編集しないこと。\n-/")
    L += ["import URTM.CTSH138_2Main", "", "set_option maxRecDepth 100000", "", "namespace URTM.Gen.C138_2", "",
          "open URTM URTM.KState URTM.CTSH URTM.Conv54 URTM.SimLemmas URTM.CTSH.U138_2 URTM.Gen.F138_2",
          "open URTM.CTSH.U24_4 (encC24)"]
    dec = {v: k for k, v in CODE2.items()}
    # 記述ファイル urtm138-2.txt の例は 1 件だけ（停止は halt）。null で止まる場合（pre が δr を 1 回進む分岐）も
    # 照合するため、urtm24-4.txt の試験例を ϕ3（上の CODE2）で符号化したものも加える。期待値は表の Python 実行から。
    cases = [(st, p_, tp, sp, o, "urtm138-2.txt") for (st, p_, tp, sp, o) in read_cases(path)]
    for (st, p_, tp, sp, o) in read_cases(base):
        if sp is None:
            continue
        bits_ = [b for x in tp for b in CODE2[x]]
        cases.append(("[begin__r]", 2 * p_, bits_, None, o, "urtm24-4.txt を ϕ3 で符号化"))
    n = 0
    for (state, pos, tape, steps, out, src) in cases:
        n += 1
        assert state == "[begin__r]" and pos % 2 == 0, (state, pos)
        bits = [int(x) for x in tape]
        if len(bits) % 2:
            bits.append(0)
        plain = [dec[(bits[i], bits[i + 1])] for i in range(0, len(bits), 2)]
        C, w = decode(pos // 2, plain, "b")
        erased = []
        (vf, mf), halted, cyc = ctsh_run(C, w, 1000, erased)
        assert halted, (C, w)
        assert out == "".join(x.lower() for x in vf) or (out == "null" and vf == []), (out, vf)
        q, h, ftape, nsteps = run4(path, state, pos, [str(x) for x in tape])
        assert steps is None or nsteps == steps, (nsteps, steps)
        W = max(len(tape), len(ftape)) + 2
        W += W % 2
        bit = {"0": "false", "1": "true"}
        itape = [str(x) for x in tape] + ["0"] * (W - len(tape))
        ftape = [str(x) for x in ftape] + ["0"] * (W - len(ftape))
        B = Machine(base)
        sid = {s: f"q{i}" for i, s in enumerate(B.states)}
        L.append("")
        L.append(f"-- 例 {n}（{src}）: initial_conf([{state},{pos},[{','.join(str(x) for x in tape)}]])  "
                 + (f"原典のコメント: {steps} {out}" if steps is not None else f"期待する最終文字列: {out}"))
        L.append(f"def C{n} : CTSH := [" + ", ".join(lch(x) for x in C) + "]")
        L.append(f"def w{n} : List Ch := {lch(w)}")
        L.append(f"/-- `E (encC24 C{n} w{n})` は記述ファイルの初期配置（状態 [begin_r], ヘッド {pos}）と、"
                 f"テープの窓 [0, {W}) で一致する（窓の外は 0）。 -/")
        L.append(f"theorem enc{n} : (E (encC24 C{n} w{n})).st = .go (.r .q0) ∧ (E (encC24 C{n} w{n})).pos = {pos} ∧\n"
                 f"    (List.range {W}).map (fun (i : Nat) => (E (encC24 C{n} w{n})).tape (Int.ofNat i)) =\n"
                 f"      [" + ", ".join(bit[x] for x in itape) + "] := by decide")
        L.append(f"theorem run{n} : run C{n} 1000 (w{n}, 0) = (({lch(vf)}, {mf}), true) := by decide +kernel")
        L.append("/-- 一般定理の具体例への適用: U138_2 は初期配置から停止する。 -/")
        L.append(f"theorem halts{n} : ∃ N rm, HaltsIn T138 N (E (encC24 C{n} w{n})) (fin138 C{n} {lch(vf)} {mf} rm) := by")
        L.append(f"  obtain ⟨k, hk⟩ := run_sound 1000 (by decide) run{n}")
        L.append(f"  obtain ⟨N, rm, -, h⟩ := (urtm138_2_simulates_ctsh C{n} w{n}).2.2.2.2.1 k _ _ hk")
        L.append("  exact ⟨N, rm, h⟩")
        L.append(f"/-- 停止配置の形の照合: 記述ファイルの表を Python で {nsteps} ステップ実行した停止配置"
                 f"（{q}, ヘッド {h}）が `fin138 C{n} {''.join(vf) or 'λ'} {mf} rm`（rm = {''.join(erased) or 'λ'}）と"
                 f"テープの窓 [0, {W}) で一致する。 -/")
        L.append(f"theorem fin{n} : (fin138 C{n} {lch(vf)} {mf} {lch(erased)}).st = .go {bst(q, sid)} ∧\n"
                 f"    (fin138 C{n} {lch(vf)} {mf} {lch(erased)}).pos = {h} ∧\n"
                 f"    (List.range {W}).map (fun (i : Nat) => (fin138 C{n} {lch(vf)} {mf} {lch(erased)}).tape (Int.ofNat i)) =\n"
                 f"      [" + ", ".join(bit[x] for x in ftape) + "] := by decide")
    L += ["", "end URTM.Gen.C138_2"]
    print("\n".join(L))


# ---------------------------------------------------------------------------
# URTM(3,36654)（Lemma 5.9 → Lemma 5.10 で U32_3 から変換）
# ---------------------------------------------------------------------------

def _q3_ctx(base):
    B = Machine(base)
    return B, {s: f"q{i}" for i, s in enumerate(B.states)}, {s: f"s{i}" for i, s in enumerate(B.symbols)}


def wsym3(x, sid, yid):
    """記述ファイルの T̂ の記号 → Lean の WSym 項（b ↦ bl、[s,t] ↦ pr、[[q_p,s],t] ↦ hp）。"""
    x = x.strip()
    if x == "b":
        return ".bl"
    a, c = split_top(x[1:-1])
    if a.startswith("["):
        pq, s_ = split_top(a[1:-1])
        assert pq.startswith("q_"), pq
        return f"(.hp .{sid[pq[2:]]} .{yid[s_]} .{yid[c]})"
    return f"(.pr .{yid[a]} .{yid[c]})"


def fsym3(x, sid, yid):
    x = x.strip()
    if x.startswith("["):
        parts = split_top(x[1:-1])
        if len(parts) == 3 and parts[2] in ("u", "d"):
            return f"(.{'up' if parts[2] == 'u' else 'dn'} {wsym3(parts[0], sid, yid)} {int(parts[1])})"
    return f"(.pl {wsym3(x, sid, yid)})"


def code_w(x, qs, ss):
    x = x.strip()
    if x == "b":
        return 0
    a, c = split_top(x[1:-1])
    if a.startswith("["):
        pq, s_ = split_top(a[1:-1])
        return 10 + 9 * qs.index(pq[2:]) + 3 * ss.index(s_) + ss.index(c)
    return 1 + 3 * ss.index(a) + ss.index(c)


def code_f(x, qs, ss):
    x = x.strip()
    if x.startswith("["):
        parts = split_top(x[1:-1])
        if len(parts) == 3 and parts[2] in ("u", "d"):
            w = code_w(parts[0], qs, ss)
            k = int(parts[1])
            return 298 + 2 * (k * 298 + w) + (0 if parts[2] == "u" else 1)
    return code_w(x, qs, ss)


ST3 = {"l": ("L", 0), "r0": ("R0", 1), "r1": ("R1", 2)}
DIR3 = {"-": 0, "0": 1, "+": 2}


def key3(rule, qs, ss):
    """Lean の `key3` と同じ鍵（CTSH3_36654Main.lean）。"""
    p, s_, t, d, q = rule
    R = 2 ** 20
    return ((((ST3[p][1] * R + code_f(s_, qs, ss)) * R + code_f(t, qs, ss)) * 4 + DIR3[d]) * 8
            + ST3[q][1])


def hat_numbering(path):
    """記述ファイルのコメントの T̂ の規則（数字の状態）から、T̂ の状態番号 → 記号的な状態 を復元する。
    q_L = 0、q(s0) = δ̂1 の行き先（コメントの 1 本目）から、(状態, 記号) の対応をたどる。"""
    num = {}
    for line in open(path, encoding="utf-8", errors="replace"):
        m = re.fullmatch(r"% \[(\d+),(.*),(.*),([-+0]),(\d+)\]\s*", line)
        if not m:
            continue
        parts = split_top(line.strip()[3:-1])
        if len(parts) != 5:
            continue
        p, s_, t, d, q = parts
        num.setdefault(int(p), {})[s_] = (t, d, int(q))
    return num


def hat_states(path, base):
    """Lemma 5.9 を Python で記号的に適用した T̂ と、記述ファイルのコメントの（数字の状態の）T̂ の規則を
    q_L = 0 から BFS で突き合わせ、番号順の記号的状態の列と、T̂ に現れない WSt の値の列を返す。"""
    B = Machine(base)
    S, st = B.symbols, B.states
    T = [r for r in parse(base)[2] if r[4] in st]
    b = "b"
    Qp = {r[4] for r in T if r[3] == "+"}
    has = {(r[0], r[1]) for r in T}
    pr = lambda s_, t: f"[{s_},{t}]"  # noqa: E731
    hpr = lambda p_, s_, t: f"[[q_{p_},{s_}],{t}]"  # noqa: E731
    sym = {}

    def add(p_, s_, t, d, q):
        sym.setdefault(p_, {})[s_] = (t, d, q)
    add(("L",), b, b, "+", ("q", b))
    for s_ in S:
        for t in S:
            for u in S:
                add(("q", s_), pr(t, u), pr(s_, t), "+", ("q", u))
                add(("h", s_), pr(t, u), pr(s_, t), "+", ("h", u))
    for (p_, t, t1, d, p1) in T:
        for s_ in S:
            for u in S:
                if d == "-":
                    add(("q", s_), hpr(p_, t, u), hpr(p1, s_, t1), "+", ("q", u) if (p1, s_) in has else ("h", u))
                else:
                    add(("q", s_), hpr(p_, t, u), pr(s_, t1), "+", ("qp", p1, u))
    for p1 in Qp:
        for u in S:
            for s_ in S:
                for t in S:
                    add(("qp", p1, u), pr(s_, t), hpr(p1, u, s_), "+", ("q", t) if (p1, u) in has else ("h", t))
    for s_ in S:
        add(("q", s_), b, pr(s_, b), "+", ("lam",))
    add(("lam",), b, b, "-", ("L",))
    num = hat_numbering(path)
    m = {0: ("L",)}
    todo = [0]
    while todo:
        n = todo.pop()
        for s_, (t, d, nq) in num.get(n, {}).items():
            sp = m[n]
            if sp == ("L",) and s_ != b:
                continue  # q_L の左移動（δ̂10, 11）は Lemma 5.10 が δ8† にまとめる
            t2, d2, q2 = sym[sp][s_]
            assert (t, d) == (t2, d2), (n, sp, s_, t, t2)
            if nq in m:
                assert m[nq] == q2, (nq, m[nq], q2)
            else:
                m[nq] = q2
                todo.append(nq)
    assert sorted(m) == list(range(len(m))), sorted(m)
    order = [m[i] for i in range(len(m))]
    allw = [("L",), ("lam",)] + [("q", s_) for s_ in S] + [("h", s_) for s_ in S] + \
        [("qp", p_, s_) for p_ in st for s_ in S]
    rest = [x for x in allw if x not in order]
    return order, rest


def table3(path, base):
    B, sid, yid = _q3_ctx(base)
    qs, ss = B.states, B.symbols
    _, _, quints = parse(path)
    rows = sorted(quints, key=lambda r: key3(r, qs, ss))
    keys = [key3(r, qs, ss) for r in rows]
    assert all(a < b for a, b in zip(keys, keys[1:])), "鍵が衝突した"
    CH = 1000
    L = []
    L.append(f"/-\n  {path.split('/')[-1]} から自動生成（tools/gen_conv_lean.py table3）。手で編集しないこと。\n"
             f"  状態 l r0 r1 ↦ TSt.L R0 R1、記号は Conv510.FSym (Conv59.WSym St Sy)（St, Sy は {base.split('/')[-1]} の番号、K32_3 と同じ）。\n"
             f"  五つ組 {len(rows)} 本を、鍵 `key3`（CTSH3_36654Main.lean）の昇順に並べ替えて {CH} 本ずつに分けた。\n-/")
    L += ["import URTM.Conv510", "import URTM.Conv59", "import URTM.Gen.K32_3", "",
          "set_option maxRecDepth 100000", "", "namespace URTM.Gen.F3_36654", "",
          "open URTM URTM.KState URTM.Conv510 URTM.Conv59 URTM.Gen.K32_3", "open URTM.Conv55 (FSym)", ""]
    names = []
    for c in range(0, len(rows), CH):
        nm = f"T3_{c // CH}"
        names.append(nm)
        L.append(f"def {nm} : Machine TSt Ps (FSym (WSym St Sy)) := [")
        L.append(",\n".join(f"⟨.{ST3[p][0]}, {fsym3(s_, sid, yid)}, {fsym3(t, sid, yid)}, {'.L' if d == '-' else '.R' if d == '+' else '.Z'}, .go .{ST3[q][0]}⟩"
                             for (p, s_, t, d, q) in rows[c:c + CH]))
        L.append("]")
    L.append("")
    L.append("/-- 記述ファイルの五つ組（鍵の昇順）。 -/")
    L.append("def T3 : Machine TSt Ps (FSym (WSym St Sy)) :=\n  " + " ++\n  ".join(names))
    # T̂ の状態番号（記述ファイルのコメントから復元）
    order, rest = hat_states(path, base)

    def wst(t):
        if t == ("L",):
            return ".L"
        if t == ("lam",):
            return ".lam"
        if t[0] == "q":
            return f"(.q .{yid[t[1]]})"
        if t[0] == "h":
            return f"(.h .{yid[t[1]]})"
        return f"(.qp .{sid[t[1]]} .{yid[t[2]]})"
    L.append("")
    L.append("/-- T̂ の状態番号 0..61（記述ファイルのコメントの T̂ の規則から復元。0 は q_L）。 -/")
    L.append("def num3 : List (WSt St Sy) := [" + ", ".join(wst(t) for t in order) + "]")
    L.append("/-- T̂ に現れない WSt の値（番号 62 以降。番号付けを単射にするためだけに使う）。 -/")
    L.append("def rest3 : List (WSt St Sy) := [" + ", ".join(wst(t) for t in rest) + "]")
    L.append("")
    L.append("end URTM.Gen.F3_36654")
    print("\n".join(L))


def verify3(path, base):
    """F3_36654 の表を塊ごとに照合する Lean モジュール（Gen/V3_36654.lean）。"""
    B, sid, yid = _q3_ctx(base)
    qs, ss = B.states, B.symbols
    _, _, quints = parse(path)
    rows = sorted(quints, key=lambda r: key3(r, qs, ss))
    keys = [key3(r, qs, ss) for r in rows]
    CH = 1000
    chunks = [(c // CH, rows[c:c + CH], keys[c:c + CH]) for c in range(0, len(rows), CH)]
    L = [f"/-\n  {path.split('/')[-1]} の表（F3_36654）の照合。自動生成（tools/gen_conv_lean.py verify3）。手で編集しないこと。\n"
         "  塊ごとに、各規則が T† の引き当て `look3` の値そのもの（`chk_i`）、本数（`len_i`）、鍵が狭義単調増加（`inc_i`）、\n"
         "  鍵の範囲（`rng_i`）を `decide +kernel` で確かめ、塊をつないで表全体の性質にする。\n-/",
         "import URTM.CTSH3_36654Main", "", "set_option maxRecDepth 100000", "",
         "namespace URTM.Gen.V3_36654", "",
         "open URTM URTM.KState URTM.CTSH URTM.SimLemmas URTM.Gen.K32_3 URTM.Gen.F3_36654 URTM.CTSH.U3_36654",
         "open URTM.Conv55 (FSym)", "open URTM.Conv59 (WSt WSym)", "open URTM.Conv510 (TSt)", ""]
    for i, rs, ks in chunks:
        L.append(f"theorem chk_{i} : ∀ ρ ∈ T3_{i}, look3 ρ.p ρ.s = some ρ := by decide +kernel")
        L.append(f"theorem len_{i} : T3_{i}.length = {len(rs)} := by decide +kernel")
        L.append(f"theorem inc_{i} : (T3_{i}.map key3).Pairwise (· < ·) := incr_pairwise _ (by decide +kernel)")
        L.append(f"theorem rng_{i} : InRange (T3_{i}.map key3) {ks[0]} {ks[-1]} := inRange_of_all (by decide +kernel)")
    n = len(chunks)
    L.append("")
    L.append("/-- 表の各規則は T† の引き当ての値。 -/")
    L.append("theorem chk3 : ∀ ρ ∈ T3, look3 ρ.p ρ.s = some ρ := by")
    L.append("  simp only [T3, List.forall_mem_append]")
    L.append("  exact " + "⟨" * (n - 1) + "chk_0" + "".join(f", chk_{i}⟩" for i in range(1, n)))
    L.append(f"theorem len3 : T3.length = {len(rows)} := by")
    L.append("  simp only [T3, List.length_append, " + ", ".join(f"len_{i}" for i in range(n)) + "]")
    L.append("/-- 表の鍵は狭義単調増加（したがって重複が無い）。 -/")
    L.append("theorem inc3 : (T3.map key3).Pairwise (· < ·) := by")
    L.append("  simp only [T3, List.map_append]")
    L.append("  have g1 := glue inc_0 rng_0 inc_1 rng_1 (by decide) (by decide) (by decide)")
    prev = "g1"
    for i in range(2, n):
        L.append(f"  have g{i} := glue {prev}.1 {prev}.2 inc_{i} rng_{i} (by decide) (by decide) (by decide)")
        prev = f"g{i}"
    L.append(f"  exact {prev}.1")
    L.append("")
    L.append("end URTM.Gen.V3_36654")
    print("\n".join(L))


def example3(path, base):
    """urtm3-36654 の試験例（Gen/C3_36654.lean）。表を Python で停止まで実行し、主定理の停止配置と照合する。"""
    from gen_ctsh_lean import decode2
    B, sid, yid = _q3_ctx(base)
    _, _, q3 = parse(path)
    delta = {(p_, s_): (t, d, q) for (p_, s_, t, d, q) in q3}
    st32, S32, qu32 = parse(base)
    T32 = [r for r in qu32 if r[4] in st32]
    d32 = {(p_, s_): (t, d, q) for (p_, s_, t, d, q) in T32}
    L = [f"/-\n  {path.split('/')[-1]} の試験例から自動生成（tools/gen_conv_lean.py example3）。手で編集しないこと。\n-/",
         "import URTM.CTSH3_36654Thm", "", "set_option maxRecDepth 100000", "", "namespace URTM.Gen.C3_36654", "",
         "open URTM URTM.KState URTM.CTSH URTM.SimLemmas URTM.Gen.K32_3 URTM.Gen.F3_36654 URTM.CTSH.U3_36654",
         "open URTM.Conv55 (FSym)", "open URTM.Conv59 (WSt WSym)", "open URTM.Conv510 (TSt)",
         "open URTM.CTSH.U32_3 (nm32)"]
    n = 0
    for (state, pos, tape, steps, out) in read_cases(path):
        n += 1
        assert state == "l" and pos == 0 and tape[0] == "b", (state, pos, tape[:2])
        # T̂ の組を U32_3 のテープに戻す
        cells, hx = [], None
        for x in tape[1:]:
            a, c = split_top(x[1:-1])
            if a.startswith("["):
                pq, s_ = split_top(a[1:-1])
                assert pq == "q_begin_", pq
                hx = len(cells)
                cells += [s_, c]
            else:
                cells += [a, c]
        n0 = len(tape) - 1
        C, w = decode2(hx, cells)
        erased = []
        (vf, mf), halted, cyc = ctsh_run(C, w, 1000, erased)
        assert halted and steps is not None
        assert out == "".join(x.lower() for x in vf) or (out == "null" and vf == []), (out, vf)
        # U32_3'（停止規則なし）のステップ数 N
        tp, q, h, N = list(cells), "begin_", hx, 0
        while True:
            while h >= len(tp):
                tp.append("b")
            if (q, tp[h]) not in d32:
                break
            t, d, q = d32[(q, tp[h])]
            tp[h] = t
            h += {"-": -1, "+": 1}[d]
            N += 1
        # 3 状態の表を停止まで実行
        T, P_, H, M = list(tape), "l", 0, 0
        while True:
            while H >= len(T):
                T.append("b")
            key = (P_, T[H])
            if key not in delta:
                break
            t, d, P_ = delta[key]
            T[H] = t
            H += {"-": -1, "+": 1, "0": 0}[d]
            M += 1
        assert M == steps, (M, steps)
        while len(T) > 1 and T[-1] == "b":
            T.pop()
        W = max(len(T), n0 + 1) + 2
        itape = list(tape) + ["b"] * (W - len(tape))
        ftape = list(T) + ["b"] * (W - len(T))
        L.append("")
        L.append(f"-- 例 {n}: 原典のコメント: {steps} {out}（U32_3' のステップ数 N = {N}、組の数 n0 = {n0}）")
        L.append(f"def C{n} : CTSH := [" + ", ".join(lch(x) for x in C) + "]")
        L.append(f"def w{n} : List Ch := {lch(w)}")
        L.append(f"theorem hn{n} : (URTM.CTSH.U32_3.RA nm32 C{n} 0).length + 6 ≤ 2 * {n0} ∧\n"
                 f"    (URTM.CTSH.U32_3.tapeList nm32 C{n} 0 [] w{n}).length + 1 ≤ 2 * {n0} := by decide")
        L.append(f"/-- `E3 C{n} w{n} {n0}` は記述ファイルの初期配置（状態 l, ヘッド 0）と、テープの窓 [0, {W}) で一致する。 -/")
        L.append(f"theorem enc{n} : (E3 C{n} w{n} {n0}).st = .go .L ∧ (E3 C{n} w{n} {n0}).pos = 0 ∧\n"
                 f"    (List.range {W}).map (fun (i : Nat) => (E3 C{n} w{n} {n0}).tape (Int.ofNat i)) =\n"
                 f"      [" + ", ".join(fsym3(x, sid, yid) for x in itape) + "] := by decide")
        L.append(f"theorem run{n} : run C{n} 1000 (w{n}, 0) = (({lch(vf)}, {mf}), true) := by decide +kernel")
        L.append("/-- 一般定理の具体例への適用: U3_36654 は初期配置から停止する。 -/")
        L.append(f"theorem halts{n} : ∃ N M rm, HaltsIn T3 M (E3 C{n} w{n} {n0}) (fin3 {n0} C{n} {lch(vf)} {mf} rm N) := by")
        L.append(f"  obtain ⟨k, hk⟩ := run_sound 1000 (by decide) run{n}")
        L.append(f"  obtain ⟨N, M, rm, -, -, h⟩ := (urtm3_36654_simulates_ctsh C{n} w{n} {n0} hn{n}).2.1 k _ _ hk")
        L.append("  exact ⟨N, M, rm, h⟩")
        L.append(f"/-- 停止配置の形の照合: 記述ファイルの表を Python で {M} ステップ実行した停止配置（{P_}, ヘッド {H}）が "
                 f"`fin3 {n0} C{n} {''.join(vf) or 'λ'} {mf} rm {N}`（rm = {''.join(erased) or 'λ'}）とテープの窓 [0, {W}) で一致する。 -/")
        fc = f"(fin3 {n0} C{n} {lch(vf)} {mf} {lch(erased)} {N})"
        L.append(f"theorem fin{n} : {fc}.st = .go .{ST3[P_][0]} ∧ {fc}.pos = {H} ∧\n"
                 f"    (List.range {W}).map (fun (i : Nat) => {fc}.tape (Int.ofNat i)) =\n"
                 f"      [" + ", ".join(fsym3(x, sid, yid) for x in ftape) + "] := by decide +kernel")
    L += ["", "end URTM.Gen.C3_36654"]
    print("\n".join(L))


if __name__ == "__main__":
    mode, path, base = sys.argv[1:4]
    {"table": table, "example": example, "table2": table2, "example2": example2,
     "table3": table3, "verify3": verify3, "example3": example3}[mode](path, base)
