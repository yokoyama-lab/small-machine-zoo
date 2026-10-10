#!/usr/bin/env python3
"""URTM(3,36654) の試験例の停止までのステップ数を、表 T3（T†）を回さずに、Lemma 5.9・5.10 の歩数の式と
(32,3) の実行から出す Lean モジュールを生成する（C14、lean/URTM/CTSH3_36654Cost.lean の具体例）。

    python3 tools/gen_cost36654_lean.py data/urtm/urtm3-36654_Be_careful.txt data/urtm/urtm32-3.txt lean/URTM/Gen

生成されるもの（どれも lean/URTM/Gen/ の下、gitignore。記述ファイルのテープを含むので再配布しない）:
  * `W3_36654Z.lean` — 試験例ごとに、(32,3) から停止規則を除いた T32' の初期配置・停止配置（ジッパー `u<n>_0`・`ue<n>`）、
    T̂（Lemma 5.9 の変換）の初期配置 `y<n>_0`、`chunk` ステップごとの途中配置 `y<n>_<j>`、停止配置 `ey<n>`。
  * `W3_36654P<k>.lean` — T̂ の区間ごとの検査
      `s<n>_<j> : freachW bkh lookH cost3 <ステップ数> y<n>_<j-1> y<n>_<j> <歩数の和> = true`（`decide +kernel`）。
    T̂ の規則は `Conv59.hatLookup` で引き、入った状態ごとに Lemma 5.10 の歩数（q_L なら 1、q_j なら 2j + 1）を足す。
  * `W3_36654.lean` — 例ごとに
      `run32_<n> : HaltsIn T32' N (encC32 C w) (unhalt f32 (finCfg32 C vf mf rm))`（(32,3) の実行、`KRun.check`）、
      `hat<n>    : HaltsIn That K (W 0 12 0 (encC32 C w)) (E .s0 0 12 N …)`（Lemma 5.9 の式、K = (N−1)(2n0+N+2)+n0+N）、
      `hatW<n>   : StepW That cost3 K M (W …) (E …)`（T̂ の実行に沿った Lemma 5.10 の歩数の和、区間をつないだもの）、
      `dag<n>    : HaltsIn T3 M (E3 C w 12) (fin3 12 C vf mf rm N)`（`dag_of_hat`）。
    このモジュールは T† を回した `S3_36654` に依らない。
  * `W3_36654Same.lean` — `same<n> : dag<n> = S3_36654.steps<n>`（`rfl`。2 つの道筋が同じ命題を示したことのカーネルの確認）。

T̂ は Lemma 5.9 を Python で記号的に当てた規則（`gen_conv_lean.hat_states` と同じ構成に、q_L の左移動 δ̂10・δ̂11 を
足したもの）で回す。生成時に次をすべて確かめ、一つでも合わなければ止まる:
  T̂ のステップ数 = Lemma 5.9 の式、歩数の和 = 記述ファイルのコメントのステップ数（471,798・2,348,492・57,220）、
  T32' のステップ数 N = `gen_steps36654_lean.py` と同じ求め方の値。
"""

import sys

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from check_urtm import parse, split_top  # noqa: E402
from simulate import read_cases, blank_of  # noqa: E402
from kstate import Machine  # noqa: E402
from gen_conv_lean import _q3_ctx, wsym3, hat_states  # noqa: E402
from gen_ctsh_lean import decode2, ctsh_run, lch  # noqa: E402

HEAD = ["open URTM URTM.KState URTM.KState.Run URTM.KState.RunF URTM.Gen.K32_3 URTM.Gen.F3_36654",
        "open URTM.CTSH URTM.SimLemmas URTM.CTSH.U3_36654",
        "open URTM.Conv55 (FSym)", "open URTM.Conv59 (WSt WSym)", "open URTM.Conv510 (TSt)",
        "open URTM.CTSH.U32_3 (encC32 finCfg32 nm32)"]
TYH = "Zip (WSt St Sy) Ps (WSym St Sy)"
TY32 = "Zip St Ps Sy"


def hat_rules(base):
    """T̂（Lemma 5.9、`Conv59.conv`）の規則 {(状態, 記号): (書く記号, 向き, 次の状態)}。状態はタプル
    （("L",)・("q", s)・("lam",)・("h", s)・("qp", p, s)）、記号は記述ファイルの書き方（b・[s,t]・[[q_p,s],t]）。"""
    B = Machine(base)
    S, st = B.symbols, B.states
    T = [r for r in parse(base)[2] if r[4] in st]          # T32'（疑似状態へ入る規則を除いたもの）
    b = "b"
    Qp = {r[4] for r in T if r[3] == "+"}
    has = {(r[0], r[1]) for r in T}
    pr = lambda s_, t: f"[{s_},{t}]"  # noqa: E731
    hpr = lambda p_, s_, t: f"[[q_{p_},{s_}],{t}]"  # noqa: E731
    R = {}

    def add(p_, s_, t, d, q):
        assert (p_, s_) not in R, (p_, s_)
        R[(p_, s_)] = (t, d, q)
    add(("L",), b, b, "+", ("q", b))                                            # δ̂1
    for s_ in S:
        for t in S:
            add(("L",), pr(s_, t), pr(s_, t), "-", ("L",))                       # δ̂10
            for u in S:
                add(("q", s_), pr(t, u), pr(s_, t), "+", ("q", u))               # δ̂2
                add(("h", s_), pr(t, u), pr(s_, t), "+", ("h", u))               # δ̂12
    for p_ in st:
        for s_ in S:
            for t in S:
                add(("L",), hpr(p_, s_, t), hpr(p_, s_, t), "-", ("L",))         # δ̂11
    for (p_, t, t1, d, p1) in T:
        for s_ in S:
            for u in S:
                if d == "-":                                                     # δ̂3/δ̂4
                    add(("q", s_), hpr(p_, t, u), hpr(p1, s_, t1), "+", ("q", u) if (p1, s_) in has else ("h", u))
                else:                                                            # δ̂5
                    add(("q", s_), hpr(p_, t, u), pr(s_, t1), "+", ("qp", p1, u))
    for p1 in Qp:
        for u in S:
            for s_ in S:
                for t in S:                                                      # δ̂6/δ̂7
                    add(("qp", p1, u), pr(s_, t), hpr(p1, u, s_), "+", ("q", t) if (p1, u) in has else ("h", t))
    for s_ in S:
        add(("q", s_), b, pr(s_, b), "+", ("lam",))                              # δ̂8
    add(("lam",), b, b, "-", ("L",))                                             # δ̂9
    return R


def zrun(rules, blank, st, tape, chunk, cost=None):
    """`KRunF.fstep` と同じ形でジッパーを進める（左右とも stack、末尾がヘッドの隣）。
    返り値: (ステップ数, 重みの和, 停止配置, [(途中配置, そこまでのステップ数, 重みの和)])。"""
    left, h, right = [], tape[0], list(reversed(tape[1:]))
    n, w, marks = 0, 0, []

    def snap():
        return (st, left[::-1], h, right[::-1])
    while (st, h) in rules:
        t, d, st = rules[(st, h)]
        if d == "+":
            left.append(t)
            h = right.pop() if right else blank
        else:
            assert d == "-" and left, "左端から出た"
            right.append(t)
            h = left.pop()
        n += 1
        if cost:
            w += cost(st)
        if chunk and n % chunk == 0:
            marks.append((snap(), n, w))
    if marks and marks[-1][1] == n:
        marks.pop()  # 最後の区切りが停止配置そのものなら、最後の区間の側に回す
    return n, w, snap(), marks


def main(path, base, outdir, chunk=10000, per=6):
    B, sid, yid = _q3_ctx(base)
    assert blank_of(path) == "b"
    R = hat_rules(base)
    order, rest = hat_states(path, base)
    idx = {q: i for i, q in enumerate(order + rest)}
    assert idx[("L",)] == 0
    cost = lambda q: 1 if q == ("L",) else 2 * idx[q] + 1  # noqa: E731   Conv510.cost .L idx3
    st32, _, qu32 = parse(base)
    d32 = {(p, s): (t, d, q) for (p, s, t, d, q) in qu32 if q in st32}  # T32'

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

    def ziph(z):
        st, lf, h, rt = z
        return (f"⟨.go {wst(st)}, [{', '.join(wsym3(x, sid, yid) for x in lf)}], {wsym3(h, sid, yid)}, "
                f"[{', '.join(wsym3(x, sid, yid) for x in rt)}]⟩")

    def zip32(st, tp, hh):
        lf = tp[:hh][::-1]
        return (f"⟨.go .{sid[st]}, [{', '.join('.' + yid[x] for x in lf)}], .{yid[tp[hh]]}, "
                f"[{', '.join('.' + yid[x] for x in tp[hh + 1:])}]⟩")

    Z = ["/-", f"  {path.split('/')[-1]} の試験例の T32'・T̂ の配置（tools/gen_cost36654_lean.py）。手で編集しないこと。",
         "  記述ファイルのテープを含むので再配布しない（gitignore）。", "-/",
         "import URTM.CTSH3_36654Cost", "", "namespace URTM.Gen.W3_36654", ""] + HEAD + [""]
    jobs, tails = [], []
    for n, (state, pos, tape, steps, out) in enumerate(read_cases(path), 1):
        assert state == "l" and pos == 0 and steps is not None, (state, pos, steps)
        tape = [x.replace(" ", "") for x in tape]
        n0 = len(tape) - 1
        # (32,3) のテープ（組をほどいたもの）とヘッド、(C, w)（gen_steps36654_lean.py と同じ）
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
        assert len(cells) == 2 * n0
        C, w = decode2(hx, cells)
        erased = []
        (vf, mf), halted, _ = ctsh_run(C, w, 1000, erased)
        assert halted
        # T32' を停止まで（N ステップ）
        tp, q, hh, N = list(cells), "begin_", hx, 0
        while True:
            while hh >= len(tp):
                tp.append("b")
            if (q, tp[hh]) not in d32:
                break
            t, d, q = d32[(q, tp[hh])]
            tp[hh] = t
            hh += {"-": -1, "+": 1}[d]
            assert hh >= 0
            N += 1
        assert N >= 1
        ra = 2 * (sum(len(x) + 1 for x in C) + 1)          # |RA(m)|（gen_ctsh_lean.py の 32_3）
        tl = 1 + ra + 1 + len(w)                            # |tapeList nm32 C 0 [] w|
        fl = 1 + ra + 1 + len(erased) + len(vf)             # |finList nm32 C vf mf rm|
        assert len(cells) >= tl and len(tp) >= fl and all(x == "b" for x in tp[fl:]), (len(cells), tl, len(tp), fl)
        # T̂ を停止まで、Lemma 5.10 の歩数を足しながら
        K, M, fin, marks = zrun(R, "b", ("L",), list(tape), chunk, cost)
        assert fin[0] == ("h", "b") and len(fin[1]) == n0 + N, (fin[0], len(fin[1]), n0 + N)
        assert K == (N - 1) * (2 * n0 + N + 2) + n0 + N, (K, N, n0)          # Lemma 5.9 の式
        assert M == steps, (M, steps)                                        # 記述ファイルのコメント
        assert len(fin[1]) + 1 + len(fin[3]) >= n0 + N
        cum = [(k, wk) for (_, k, wk) in marks] + [(K, M)]   # 区間の終わりまでの累計（ステップ数, 歩数の和）
        tails.append((n, steps, out, C, w, vf, mf, erased, N, n0, K, M, cum, cells, tp, tl, fl))
        Z.append(f"/-- 例 {n}: T32' の初期配置（状態 begin、ヘッド {hx}）。 -/")
        Z.append(f"def u{n}_0 : {TY32} :=\n  {zip32('begin_', cells, hx)}")
        Z.append(f"/-- 例 {n}: T32' の停止配置（{N} ステップ後、状態 {q}、ヘッド {hh}）。 -/")
        Z.append(f"def ue{n} : {TY32} :=\n  {zip32(q, tp, hh)}")
        Z.append(f"/-- 例 {n}: T̂ の初期配置（記述ファイルの initial_conf の組。状態 q_L、ヘッド 0）。 -/")
        Z.append(f"def y{n}_0 : {TYH} :=\n  {ziph((('L',), [], tape[0], list(tape[1:])))}")
        prev, pk, pw = 0, 0, 0
        for j, (z, k, wk) in enumerate(marks, 1):
            Z.append(f"def y{n}_{j} : {TYH} :=\n  {ziph(z)}")
            jobs.append(f"theorem s{n}_{j} : freachW bkh lookH cost3 {k - pk} y{n}_{j - 1} y{n}_{j} {wk - pw} = true := by decide +kernel")
            prev, pk, pw = j, k, wk
        Z.append(f"/-- 例 {n}: T̂ の停止配置（{K} ステップ後、状態 h(b)、ヘッド {len(fin[1])}）。 -/")
        Z.append(f"def ey{n} : {TYH} :=\n  {ziph(fin)}")
        jobs.append(f"theorem s{n}_{prev + 1} : freachW bkh lookH cost3 {K - pk} y{n}_{prev} ey{n} {M - pw} = true := by decide +kernel")
        Z.append("")
    Z += ["end URTM.Gen.W3_36654", ""]
    open(f"{outdir}/W3_36654Z.lean", "w").write("\n".join(Z))

    parts = [jobs[i:i + per] for i in range(0, len(jobs), per)]
    for k, ps in enumerate(parts):
        P = ["/-", f"  {path.split('/')[-1]} の試験例の T̂ の区間ごとの検査（tools/gen_cost36654_lean.py）。手で編集しないこと。",
             "  カーネルの評価（`decide +kernel`）。`native_decide` は使わない。", "-/",
             "import URTM.Gen.W3_36654Z", "", "set_option maxRecDepth 1000000", "",
             "namespace URTM.Gen.W3_36654", ""] + HEAD + [""] + ps + ["", "end URTM.Gen.W3_36654", ""]
        open(f"{outdir}/W3_36654P{k}.lean", "w").write("\n".join(P))

    F = ["/-", f"  {path.split('/')[-1]} の試験例の停止までのステップ数を、Lemma 5.9・5.10 の歩数の式と (32,3) の実行から"
         " 出したもの（tools/gen_cost36654_lean.py）。手で編集しないこと。",
         "  表 T3（T†）そのものを回した `URTM.Gen.S3_36654` には依らない。", "-/"]
    F += [f"import URTM.Gen.W3_36654P{k}" for k in range(len(parts))]
    F += ["import URTM.Gen.C3_36654", "", "set_option maxRecDepth 1000000", "", "namespace URTM.Gen.W3_36654", ""]
    F += HEAD + ["open URTM.Gen.C3_36654 (C1 C2 C3 w1 w2 w3 hn1 hn2 hn3)", ""]
    for (n, steps, out, C, w, vf, mf, erased, N, n0, K, M, cum, cells, tp, tl, fl) in tails:
        fin32 = f"(unhalt f32 (finCfg32 C{n} {lch(vf)} {mf} {lch(erased)}))"
        Wc = f"(Conv59.W 0 {n0} 0 (encC32 C{n} w{n}))"
        Ec = f"(Conv59.E Sy.s0 0 {n0} {N} {fin32})"
        F.append(f"/-- 例 {n}: (32,3) から停止規則を除いた T32' は `encC32 C{n} w{n}` からちょうど {N} ステップで止まる"
                 f"（カーネルの評価）。 -/")
        F.append(f"theorem run32_{n} : HaltsIn T32' {N} (encC32 C{n} w{n}) {fin32} := by")
        F.append(f"  have h₁ := KState.Run.cfg_eq_of (bk := .s0) (c := encC32 C{n} w{n}) (z := u{n}_0)")
        F.append(f"    (URTM.CTSH.U32_3.tapeList nm32 C{n} 0 [] w{n}) {len(cells) - tl} (by decide) (by decide) rfl (by decide)")
        F.append(f"  have h₂ := KState.Run.cfg_eq_of (bk := .s0) (c := {fin32}) (z := ue{n})")
        F.append(f"    (URTM.CTSH.U32_3.finList nm32 C{n} {lch(vf)} {mf} {lch(erased)}) {len(tp) - fl} (by decide) (by decide) rfl"
                 " (by decide)")
        F.append("  rw [h₁, h₂]; exact run32_of_check (by decide +kernel)")
        F.append(f"/-- **例 {n}（Lemma 5.9 の式）**: T̂ は主定理の初期配置からちょうど "
                 f"{N - 1}·(2·{n0} + {N - 1} + 3) + ({n0} + {N - 1} + 1) = {K} ステップで止まる。T̂ を回さずに、"
                 f"T32' の {N} ステップの実行（`run32_{n}`）と `Conv59.halts_sim_exact` から。 -/")
        F.append(f"theorem hat{n} : HaltsIn That {K} {Wc}\n    {Ec} :=\n"
                 f"  hat_of_run32 (N := {N - 1}) hn{n} run32_{n}")
        F.append(f"theorem init{n} : {Wc} = y{n}_0.cfg bkh :=\n"
                 f"  W0_eq_zip C{n} w{n} {n0} y{n}_0 rfl rfl (by decide) (by decide)")
        F.append(f"theorem final{n} : {Ec} = ey{n}.cfg bkh :=\n"
                 f"  E_eq_zip (by decide) (by decide) (by decide) (by decide) (by decide +kernel)")
        m = len(cum) - 1
        for j, (k, wk) in enumerate(cum, 1):
            tgt = f"y{n}_{j}" if j <= m else f"ey{n}"
            prf = f"hat_of_reachW s{n}_1" if j == 1 else f"StepW.trans t{n}_{j - 1} (hat_of_reachW s{n}_{j})"
            F.append(f"theorem t{n}_{j} : StepW That cost3 {k} {wk} (y{n}_0.cfg bkh) ({tgt}.cfg bkh) :=\n  {prf}")
        F.append(f"/-- **例 {n}（Lemma 5.10 の歩数の和）**: T̂ の {K} ステップの実行に沿って、入った状態の歩数"
                 f"（q_L なら 1、q_j なら 2j + 1）を足すと {M}。 -/")
        F.append(f"theorem hatW{n} : StepW That cost3 {K} {M} {Wc}\n    {Ec} := by\n"
                 f"  rw [init{n}, final{n}]; exact t{n}_{m + 1}")
        F.append(f"/-- **例 {n}（2 つの式から）**: 表 T3 は主定理の初期配置 `E3 C{n} w{n} {n0}` からちょうど {M} ステップで"
                 f"主定理の停止配置に止まる（原典のコメント: {steps:,} {out}）。T† を回さずに、`hat{n}` の T̂ の実行と"
                 f" Lemma 5.10 の歩数（`dag_of_hat`）から。 -/")
        F.append(f"theorem dag{n} : HaltsIn T3 {M} (E3 C{n} w{n} {n0}) (fin3 {n0} C{n} {lch(vf)} {mf} {lch(erased)} {N}) :=\n"
                 f"  dag_of_hat (by decide) hatW{n}")
        F.append("")
    F += ["end URTM.Gen.W3_36654", ""]
    open(f"{outdir}/W3_36654.lean", "w").write("\n".join(F))

    S = ["/-", "  2 つの道筋の一致（tools/gen_cost36654_lean.py）。手で編集しないこと。",
         "  `W3_36654.dag<n>`（Lemma 5.9・5.10 の式と (32,3) の実行から）と `S3_36654.steps<n>`（表 T3 をカーネルで回したもの）が",
         "  同じ命題の証明であることを `rfl` で確かめる（命題が違えば型が合わず落ちる）。", "-/",
         "import URTM.Gen.W3_36654", "import URTM.Gen.S3_36654", "", "namespace URTM.Gen.W3_36654", ""]
    for (n, *_r) in tails:
        S.append(f"theorem same{n} : dag{n} = URTM.Gen.S3_36654.steps{n} := rfl")
    S += ["", "end URTM.Gen.W3_36654", ""]
    open(f"{outdir}/W3_36654Same.lean", "w").write("\n".join(S))
    print(f"W3_36654: chunk {chunk}, {len(jobs)} 区間, {len(parts)} モジュール, "
          + ", ".join(f"例{t[0]} T32' {t[8]} / T̂ {t[10]} / T† {t[11]} ステップ" for t in tails))


if __name__ == "__main__":
    a = sys.argv[1:]
    ch = int(a[a.index("--chunk") + 1]) if "--chunk" in a else 10000
    pr = int(a[a.index("--per") + 1]) if "--per" in a else 6
    main(a[0], a[1], a[2], ch, pr)
