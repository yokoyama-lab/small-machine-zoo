#!/usr/bin/env python3
"""URTM(3,36654) の試験例の停止までのステップ数を、記述ファイルの表 `T3` そのものについてカーネルで示す
Lean モジュールを生成する（他の 8 台の `tools/gen_lean.py` の `case<i>` と同じ意味の定理）。

    python3 tools/gen_steps36654_lean.py data/urtm/urtm3-36654_Be_careful.txt data/urtm/urtm32-3.txt lean/URTM/Gen

生成されるもの（どれも lean/URTM/Gen/ の下、gitignore。記述ファイルの表やテープを含むので再配布しない）:
  * `S3_36654Z.lean` — 試験例ごとの初期配置 `z<n>_0`、`chunk` ステップごとの途中配置 `z<n>_<j>`、停止配置 `e<n>`
    （ジッパー。記述ファイルの表を Python で実行したもの）。
  * `S3_36654P<k>.lean` — 区間ごとの検査 `r<n>_<j> : freach bkz look3 chunk z<n>_<j-1> z<n>_<j> = true` と、
    最後の区間の `c<n> : fcheck bkz look3 rest z<n>_<m> e<n> = true`（`decide +kernel`。bkz = bk3 = `.pl .bl`）。
    Z と P は `CTSH3_36654Steps` に依らない（そちらを直しても重い区間の検査を建て直さない）。
    区間を複数のモジュールに分けるのは、lake にモジュール単位で並列に建てさせるため。
  * `S3_36654.lean` — 区間をつないだ主結果
      `case<n> : HaltsIn T3 <ステップ数> (z<n>_0.cfg bk3) (e<n>.cfg bk3)`
    と、主定理（`urtm3_36654_simulates_ctsh`）の初期配置・停止配置での言い換え
      `steps<n> : HaltsIn T3 <ステップ数> (E3 C<n> w<n> n0) (fin3 n0 C<n> vf mf rm N)`（N・rm は具体値）、
      `ctsh<n> : ∃ N rm, HaltsIn T3 <ステップ数> (E3 C<n> w<n> n0) (fin3 n0 C<n> vf mf rm N) ∧ fin3 … = e<n>.cfg bk3`
    （C<n>・w<n>・halts<n> は `URTM.Gen.C3_36654`。ctsh<n> は主定理が存在を与える停止が同じものだという形）。

ステップ数は記述ファイルのコメントの期待値（471,798・2,348,492・57,220）と、独立実装（`simulate.run`）の
両方に一致することを生成時に確かめる（一致しなければ止まる）。
"""

import sys

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from check_urtm import parse, split_top  # noqa: E402
from simulate import read_cases, run as sim_run, blank_of  # noqa: E402
from gen_conv_lean import _q3_ctx, fsym3  # noqa: E402
from gen_ctsh_lean import decode2, ctsh_run, lch  # noqa: E402

ST3 = {"l": ".L", "r0": ".R0", "r1": ".R1"}
TY = "Zip TSt Ps (FSym (WSym St Sy))"
HEAD = ["open URTM URTM.KState URTM.KState.Run URTM.KState.RunF URTM.Gen.K32_3 URTM.Gen.F3_36654",
        "open URTM.CTSH.U3_36654",
        "open URTM.Conv55 (FSym)", "open URTM.Conv59 (WSt WSym)", "open URTM.Conv510 (TSt)"]


def zrun(delta, blank, st, tape, chunk):
    """KRunF.fstep と同じ形でジッパーを進める。左は stack（末尾がヘッドの隣）、右も stack（末尾がヘッドの隣）。
    返り値: (ステップ数, 停止配置, chunk ステップごとの途中配置)。配置は (状態, 左（近い順）, ヘッド, 右（近い順）)。"""
    left, h, right = [], tape[0], list(reversed(tape[1:]))
    n, marks = 0, []

    def snap():
        return (st, left[::-1], h, right[::-1])
    while (st, h) in delta:
        t, d, st = delta[(st, h)]
        if d == "+":
            left.append(t)
            h = right.pop() if right else blank
        elif d == "-":
            assert left, "左端から出た"
            right.append(t)
            h = left.pop()
        else:
            h = t
        n += 1
        if n % chunk == 0:
            marks.append(snap())
    if marks and n % chunk == 0:
        marks.pop()  # 最後の区切りが停止配置そのものなら、停止の検査の側に回す
    return n, snap(), marks


def main(path, base, outdir, chunk=10000, per=12):
    B, sid, yid = _q3_ctx(base)
    _, _, q3 = parse(path)
    delta = {(p, s): (t, d, q) for (p, s, t, d, q) in q3}
    assert len(delta) == len(q3) == 37936
    blank = blank_of(path)
    assert blank == "b"
    st32, _, qu32 = parse(base)
    d32 = {(p, s): (t, d, q) for (p, s, t, d, q) in qu32 if q in st32}
    sym = lambda x: fsym3(x, sid, yid)  # noqa: E731

    def zip_(z):
        st, lf, h, rt = z
        return (f"⟨.go {ST3[st]}, [{', '.join(sym(x) for x in lf)}], {sym(h)}, "
                f"[{', '.join(sym(x) for x in rt)}]⟩")

    Z = ["/-", f"  {path.split('/')[-1]} の試験例の途中配置（tools/gen_steps36654_lean.py）。手で編集しないこと。",
         "  記述ファイルの表とテープを含むので再配布しない（gitignore）。", "-/",
         "import URTM.CTSH3_36654Main", "import URTM.KRunF", "", "namespace URTM.Gen.S3_36654", ""] + HEAD + [
             "", "/-- 記述ファイルの空白 `b`（`CTSH3_36654Steps.bk3` と同じ項）。 -/",
             "abbrev bkz : FSym (WSym St Sy) := .pl .bl", ""]
    jobs = []      # (例, 区間の番号 or None, 文)
    tails = []     # 例ごとの (ステップ数, 区間数, 残り, 期待出力, vf, mf, n0)
    for n, (state, pos, tape, steps, out) in enumerate(read_cases(path), 1):
        assert state == "l" and pos == 0 and steps is not None, (state, pos, steps)
        M, fin, marks = zrun(delta, blank, state, list(tape), chunk)
        s2, _, why = sim_run(q3, blank, state, pos, list(tape), steps + 5)
        assert M == steps == s2 and why == "halt (no rule)", (n, M, steps, s2, why)
        # 主定理の言い換え用: 試験例を CTSH に読み戻す（gen_conv_lean.example3 と同じ）
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
        C, w = decode2(hx, cells)
        erased = []
        (vf, mf), halted, _ = ctsh_run(C, w, 1000, erased)
        assert halted
        # U32_3'（停止規則なし）のステップ数 N（gen_conv_lean.example3 と同じ）
        tp, q, hh, N = list(cells), "begin_", hx, 0
        while True:
            while hh >= len(tp):
                tp.append("b")
            if (q, tp[hh]) not in d32:
                break
            t, d, q = d32[(q, tp[hh])]
            tp[hh] = t
            hh += {"-": -1, "+": 1}[d]
            N += 1
        assert N >= 1
        n0 = len(tape) - 1
        rest = M - chunk * len(marks)
        assert len(fin[1]) + 1 + len(fin[3]) > n0 + N  # 停止配置の並びは fin3 の詰め方の窓を覆う
        tails.append((n, M, len(marks), rest, out, vf, mf, n0, N, erased))
        Z.append(f"/-- 例 {n} の初期配置（記述ファイルの initial_conf。状態 l、ヘッド 0）。期待値 {steps} ステップ、出力 {out}。 -/")
        Z.append(f"def z{n}_0 : {TY} :=\n  {zip_((state, [], tape[0], list(tape[1:])))}")
        for j, z in enumerate(marks, 1):
            Z.append(f"def z{n}_{j} : {TY} :=\n  {zip_(z)}")
            jobs.append((n, f"theorem r{n}_{j} : freach bkz look3 {chunk} z{n}_{j - 1} z{n}_{j} = true := by decide +kernel"))
        Z.append(f"/-- 例 {n} の停止配置（{M} ステップ後、状態 {fin[0]}、ヘッド {len(fin[1])}）。 -/")
        Z.append(f"def e{n} : {TY} :=\n  {zip_(fin)}")
        jobs.append((n, f"theorem c{n} : fcheck bkz look3 {rest} z{n}_{len(marks)} e{n} = true := by decide +kernel"))
        Z.append("")
    Z += ["end URTM.Gen.S3_36654", ""]
    open(f"{outdir}/S3_36654Z.lean", "w").write("\n".join(Z))

    parts = [jobs[i:i + per] for i in range(0, len(jobs), per)]
    for k, ps in enumerate(parts):
        P = ["/-", f"  {path.split('/')[-1]} の試験例の区間ごとの検査（tools/gen_steps36654_lean.py）。手で編集しないこと。",
             "  カーネルの評価（`decide +kernel`）。`native_decide` は使わない。", "-/",
             "import URTM.Gen.S3_36654Z", "", "set_option maxRecDepth 1000000", "",
             "namespace URTM.Gen.S3_36654", ""] + HEAD + [""]
        P += [s for _, s in ps]
        P += ["", "end URTM.Gen.S3_36654", ""]
        open(f"{outdir}/S3_36654P{k}.lean", "w").write("\n".join(P))

    F = ["/-", f"  {path.split('/')[-1]} の試験例の停止までのステップ数（tools/gen_steps36654_lean.py）。手で編集しないこと。",
         f"  {chunk} ステップずつの区間の検査（`S3_36654P*`）を、健全性 `halts3_of_reach`・`halts3_of_check` でつなぐ。", "-/"]
    F += [f"import URTM.Gen.S3_36654P{k}" for k in range(len(parts))]
    F += ["import URTM.CTSH3_36654Steps", "import URTM.Gen.C3_36654", "", "set_option maxRecDepth 1000000", "",
          "namespace URTM.Gen.S3_36654", ""]
    F += HEAD + ["open URTM.Gen.C3_36654 (C1 C2 C3 w1 w2 w3 halts1 halts2 halts3)", ""]
    for (n, M, m, rest, out, vf, mf, n0, N, erased) in tails:
        tail = f"halts3_of_check c{n}"
        for j in range(m, 0, -1):
            F.append(f"theorem h{n}_{j} : HaltsIn T3 {rest + chunk * (m - j)} (z{n}_{j}.cfg bk3) (e{n}.cfg bk3) :=\n  {tail}")
            tail = f"halts3_of_reach r{n}_{j} h{n}_{j}"
        F.append(f"/-- **例 {n}**: 記述ファイルの表 `T3`（37936 本）は、試験例 {n} の初期配置からちょうど {M} ステップで"
                 f"停止配置 `e{n}` に止まる（原典のコメント: {M:,} {out}）。カーネルの評価で照合。 -/")
        F.append(f"theorem case{n} : HaltsIn T3 {M} (z{n}_0.cfg bk3) (e{n}.cfg bk3) :=\n  {tail}")
        F.append(f"theorem win{n} : (List.range ({n0} + 1)).map (fun i => (E3 C{n} w{n} {n0}).tape (Int.ofNat i)) =\n"
                 f"    z{n}_0.h :: z{n}_0.r := by decide")
        F.append(f"/-- 主定理の初期配置 `E3 C{n} w{n} {n0}` は試験例 {n} の初期配置そのもの。 -/")
        F.append(f"theorem init{n} : E3 C{n} w{n} {n0} = z{n}_0.cfg bk3 :=\n"
                 f"  E3_eq_zip C{n} w{n} {n0} z{n}_0 rfl rfl (by decide) win{n}")
        fc = f"(fin3 {n0} C{n} {lch(vf)} {mf} {lch(erased)} {N})"
        F.append(f"theorem fwin{n} : (List.range (e{n}.l.reverse ++ e{n}.h :: e{n}.r).length).map\n"
                 f"    (fun i => {fc}.tape (Int.ofNat i)) = e{n}.l.reverse ++ e{n}.h :: e{n}.r := by decide +kernel")
        F.append(f"/-- 主定理の停止配置（U32_3' のステップ数 N = {N}、消去済み列 rm = {''.join(erased) or 'λ'}）は試験例 {n} の停止配置 `e{n}` そのもの。 -/")
        F.append(f"theorem final{n} : {fc} = e{n}.cfg bk3 :=\n"
                 f"  fin3_eq_zip (by decide) (by decide +kernel) (by decide +kernel) (by decide) fwin{n}")
        F.append(f"/-- **例 {n}（主定理の言葉で）**: 主定理の初期配置 `E3 C{n} w{n} {n0}` から、主定理の停止配置に"
                 f"ちょうど {M} ステップで止まる。 -/")
        F.append(f"theorem steps{n} : HaltsIn T3 {M} (E3 C{n} w{n} {n0}) {fc} := by\n"
                 f"  rw [init{n}, final{n}]; exact case{n}")
        F.append(f"/-- 主定理が存在を与える停止（`halts{n}`）と同じもの（決定性から）。 -/")
        F.append(f"theorem ctsh{n} : ∃ N rm, HaltsIn T3 {M} (E3 C{n} w{n} {n0}) (fin3 {n0} C{n} {lch(vf)} {mf} rm N) ∧\n"
                 f"    fin3 {n0} C{n} {lch(vf)} {mf} rm N = e{n}.cfg bk3 :=\n"
                 f"  steps_E3 init{n} case{n} halts{n}")
        F.append("")
    F += ["end URTM.Gen.S3_36654", ""]
    open(f"{outdir}/S3_36654.lean", "w").write("\n".join(F))
    print(f"S3_36654: chunk {chunk}, {len(jobs)} 区間, {len(parts)} モジュール, "
          + ", ".join(f"例{n} {M} ステップ" for (n, M, *_) in tails))


if __name__ == "__main__":
    a = sys.argv[1:]
    ch = int(a[a.index("--chunk") + 1]) if "--chunk" in a else 10000
    pr = int(a[a.index("--per") + 1]) if "--per" in a else 12
    main(a[0], a[1], a[2], ch, pr)
