#!/usr/bin/env python3
"""urtm10-8.txt / urtm17-5.txt の試験例（initial_conf）→ CTSH の具体例を照合する Lean モジュール。

    python3 tools/gen_ctsh_lean.py data/urtm/urtm10-8.txt > lean/URTM/Gen/C10_8.lean
    python3 tools/gen_ctsh_lean.py data/urtm/urtm17-5.txt --module C17_5 --machine 17_5 \
        > lean/URTM/Gen/C17_5.lean

各 initial_conf のテープを CTSH (C, w) に読み戻し（`b R_{k-1} * ... R_1 * b $ w b...`）、次を生成する:
  * `encC C w` が記述ファイルの初期配置そのもの（テープの列・ヘッド位置・状態）であること（`decide`）
  * `steps<i>`（停止する例）: 記録どおりのステップ数で `encC C w` から `finCfg C vf mf rm` に停止する。
    `M*.K.case<j>`（tools/gen_lean.py、カーネルの評価）と、初期・停止配置の一致（`KRun.cfg_eq_of`）から
  * CTSH の実行（`CTSH.run`）が、Morita のコメント（`%% 677 yny` / `%% 455 null`）の最終文字列を返すこと
  * それと一般定理 `urtm10_8_simulates_ctsh` から、U10_8 がその初期配置から停止し
    停止配置が `finCfg` の形になること（具体例への適用）
「It does not halt.」の例は、有界の実行で停止しないことだけを確かめる（非停止の証明ではない）。

`--machine 17_5` では、停止する例についてさらに、記述ファイルの表を Python で実行した停止配置
（テープ・ヘッド位置・疑似状態。`simulate.run` と照合済み、ステップ数は原典のコメントと一致）が
`finCfg17 C vf mf rm`（rm は CTSH の実行で消した記号列）そのものであることを `decide` で確かめる。

`lean/URTM/Gen/` は生成物（gitignore）。`tools/gen_all_lean.sh` が CI で生成する。
"""

import argparse
import sys

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from kstate import Machine  # noqa: E402
from simulate import read_cases, run, blank_of  # noqa: E402
from check_urtm import parse  # noqa: E402
from gen_lean import CORRECTIONS, zrun  # noqa: E402  記述ファイルのコメントの誤植（urtm13-7.txt case4: 1073 → 1173）

LO = {"y": "Y", "n": "N"}

# 記述ファイルのコメントの最終文字列の誤植（(ファイル名, 0 始まりの例番号) → 正しい文字列）。
# urtm15-6.txt case0 のコメントは「467 yyn」だが、表を実行した停止テープ（…n $ n y、$ は Y と読む）と
# 原典 p. 190 の t = 466 のスナップショット（U17_5 と同じ）はどちらも YNY。記述ファイルは書き換えない。
OUT_CORRECTIONS = {("urtm15-6.txt", 0): "yny"}


def decode(pos, tape, delim="$"):
    """テープ → (C = [w1, ..., w_{k-1}], w)。原典 p. 183 の初期 ID の形でなければ例外。
    delim は規則領域と消去済みの記号の区切り（U24_4 では b。原典 p. 192）。"""
    if delim == "$":
        d = tape.index("$")
    else:
        # 区切りの b はヘッドの直前。その左が相 0 のマーカー b で、さらに左は規則（y, n, ∗）だけ
        d = pos - 1
        assert tape[d] == delim, (tape, pos)
    assert tape[0] == "b" and tape[d - 1] == "b", tape
    assert pos == d + 1, (pos, d)
    body = tape[1:d - 1]
    assert body == [] or body[-1] == "*", body
    segs, cur = [], []
    for x in body:
        if x == "*":
            segs.append(cur)
            cur = []
        else:
            assert x in LO, x
            cur.append(x)
    # segs = [R_{k-1}, ..., R_1]、R_j = w_j の逆順（小文字）
    C = [[LO[x] for x in reversed(seg)] for seg in reversed(segs)]
    rest = tape[d + 1:]
    while rest and rest[-1] == "b":
        rest.pop()
    assert all(x in LO for x in rest), rest
    w = [LO[x] for x in rest]
    return C, w


def decode2(pos, tape):
    """U32_3 のテープ（原典 p. 194: b ϕ₂(w^R_{k−1}) nn ⋯ nn ϕ₂(w^R_1) nn nb b q_begin ϕ₁(v0) b）→ (C, w)。
    規則は 2 マスずつ yy = Y, ny = N, nn = 区切り、nb = 相 0 の相マーカー（最後の組）。"""
    d = pos - 1
    assert tape[0] == "b" and tape[d] == "b", (tape, pos)
    body = tape[1:d]
    assert len(body) % 2 == 0 and body[-2:] == ["n", "b"], body
    pairs = [tuple(body[i:i + 2]) for i in range(0, len(body) - 2, 2)]
    segs, cur = [], []
    for pr in pairs:
        if pr == ("n", "n"):
            segs.append(cur)
            cur = []
        else:
            cur.append({("y", "y"): "Y", ("n", "y"): "N"}[pr])
    assert cur == [], (body, cur)
    C = [list(reversed(seg)) for seg in reversed(segs)]
    rest = tape[d + 1:]
    while rest and rest[-1] == "b":
        rest.pop()
    assert all(x in LO for x in rest), rest
    return C, [LO[x] for x in rest]


def ctsh_run(C, w, fuel, erased=None):
    k = len(C) + 1
    v, m = list(w), 0
    seen = set()
    for _ in range(fuel):
        if not v or (v[0] == "Y" and m == 0):
            return (v, m), True, False
        key = (tuple(v), m)
        if key in seen:
            return (v, m), False, True  # 周期に入った（非停止）
        seen.add(key)
        if erased is not None:
            erased.append(v[0])
        if v[0] == "Y":
            v = v[1:] + C[m - 1]
        else:
            v = v[1:]
        m = (m + 1) % k
    return (v, m), False, False


def sim_final(path, state, pos, tape):
    """記述ファイルの表を停止まで実行（(疑似状態, ヘッド位置, テープ, ステップ数)）。
    テープと ステップ数は simulate.run（別実装）と照合する。"""
    states, symbols, quints = parse(path)
    blank = blank_of(path)
    delta = {(p, s): (t, d, q) for (p, s, t, d, q) in quints}
    tp, q, h, n = list(tape), state, pos, 0
    while q not in ("halt", "null"):
        while h >= len(tp):
            tp.append(blank)
        assert h >= 0
        t, d, q = delta[(q, tp[h])]
        tp[h] = t
        h += {"-": -1, "0": 0, "+": 1}[d]
        n += 1
    steps, final, why = run(quints, blank, state, pos, tape, 100000)
    assert steps == n and final == "".join(tp) and why == f"halt ({q})", (steps, n, why, q)
    return q, h, tp, n


def lch(xs):
    return "[" + ", ".join(f".{x}" for x in xs) + "]"


# 機械ごとの設定: import、open、名前、停止配置のリスト長（|RA| と rm・vf の長さから）
MACHINES = {
    "10_8": dict(imp="URTM.CTSH10_8", ns="U10_8", gen="K10_8", enc="encC", fin="finCfg",
                 thm="urtm10_8_simulates_ctsh", tl="tapeList", fl=None, finchk=False),
    "17_5": dict(imp="URTM.CTSH17_5Main", ns="U17_5", gen="K17_5", enc="encC17", fin="finCfg17",
                 thm="urtm17_5_simulates_ctsh", tl="tapeList nm17", fl="finList nm17", finchk=True,
                 flen=lambda ra, rm, vf: 1 + ra + 1 + len(rm) + (1 if not vf else len(vf))),
    "13_7": dict(imp="URTM.CTSH13_7Main", ns="U13_7", gen="K13_7", enc="encC13", fin="finCfg13",
                 thm="urtm13_7_simulates_ctsh", tl="tapeList nm13", fl="finList nm13", finchk=True,
                 flen=lambda ra, rm, vf: 1 + ra + 1 + len(rm) + len(vf)),
    "15_6": dict(imp="URTM.CTSH15_6Main", ns="U15_6", gen="K15_6", enc="encC15", fin="finCfg15",
                 thm="urtm15_6_simulates_ctsh", tl="tapeList nm15", fl="finList nm15", finchk=True,
                 flen=lambda ra, rm, vf: 1 + ra + 1 + len(rm) + (1 if not vf else len(vf))),
    "24_4": dict(imp="URTM.CTSH24_4Main", ns="U24_4", gen="K24_4", enc="encC24", fin="finCfg24",
                 thm="urtm24_4_simulates_ctsh", tl="tapeList nm24", fl="finList nm24", finchk=True,
                 delim="b", flen=lambda ra, rm, vf: 1 + ra + 1 + len(rm) + len(vf)),
    "32_3": dict(imp="URTM.CTSH32_3Main", ns="U32_3", gen="K32_3", enc="encC32", fin="finCfg32",
                 thm="urtm32_3_simulates_ctsh", tl="tapeList nm32", fl="finList nm32", finchk=True,
                 decode=decode2, ramul=2, flen=lambda ra, rm, vf: 1 + ra + 1 + len(rm) + len(vf)),
}


def main(path, module, machine):
    T = Machine(path)
    M = MACHINES[machine]
    u17 = M["finchk"]
    yid = {s: f"s{i}" for i, s in enumerate(T.symbols)}
    sid = {s: f"q{i}" for i, s in enumerate(T.states)}
    L = []
    L.append(f"/-\n  {path.split('/')[-1]} の試験例から自動生成（tools/gen_ctsh_lean.py）。手で編集しないこと。\n-/")
    L.append(f"import {M['imp']}")
    L.append(f"import URTM.M{machine}")
    L.append("")
    L.append("set_option maxRecDepth 100000")
    L.append("")
    L.append(f"namespace URTM.Gen.{module}")
    L.append("")
    L.append(f"open URTM URTM.KState URTM.CTSH URTM.CTSH.{M['ns']} URTM.Gen.{M['gen']}")
    _, _, quints = parse(path)
    blank = blank_of(path)
    j = 0  # M{machine}.K の case の番号（停止する例だけを数える。gen_lean.py と同じ順）
    pid = {p: f"h{i}" for i, p in enumerate(T.pseudo)}
    enc, fin, thm, tl = M["enc"], M["fin"], M["thm"], M["tl"]
    n = 0
    for (state, pos, tape, steps, out) in read_cases(path):
        n += 1
        C, w = M["decode"](pos, tape) if "decode" in M else decode(pos, tape, M.get("delim", "$"))
        ra = M.get("ramul", 1) * (sum(len(x) + 1 for x in C) + 1)  # |RA(m)|（相に依らない）
        erased = []
        (vf, mf), halted, cyc = ctsh_run(C, w, 1000, erased)
        exp = "does not halt" if steps is None else f"{steps} {out}"
        out = OUT_CORRECTIONS.get((path.split("/")[-1], n - 1), out)
        if out != (exp.split(" ", 1)[1] if steps is not None else None) and steps is not None:
            exp += f"（最終文字列は誤植、正しくは {out}。gen_ctsh_lean.py の OUT_CORRECTIONS）"
        if steps is None:
            assert not halted and cyc, (C, w)
        else:
            assert halted, (C, w)
            assert (out == "null") == (vf == []), (out, vf)
            if out != "null":
                assert out == "".join(x.lower() for x in vf), (out, vf)
        L.append("")
        L.append(f"-- 例 {n}: initial_conf([{state},{pos},[{','.join(tape)}]])  原典のコメント: {exp}")
        L.append(f"def C{n} : CTSH := [" + ", ".join(lch(x) for x in C) + "]")
        L.append(f"def w{n} : List Ch := {lch(w)}")
        pad = len(tape) - (1 + ra + 1 + len(w))
        assert pad >= 0
        L.append(f"/-- `{enc} C{n} w{n}` は記述ファイルの初期配置（状態 {state}, ヘッド {pos}）と一致する。 -/")
        L.append(f"theorem enc{n} : {tl} C{n} 0 [] w{n} ++ List.replicate {pad} .s0 = "
                 + "[" + ", ".join(f".{yid[x]}" for x in tape) + "] ∧\n"
                 + f"    ({enc} C{n} w{n}).pos = {pos} ∧ ({enc} C{n} w{n}).st = .go St.{sid[state]} := by decide")
        if halted:
            L.append(f"theorem run{n} : run C{n} 1000 (w{n}, 0) = (({lch(vf)}, {mf}), true) := by decide +kernel")
            L.append(f"/-- 一般定理の具体例への適用: U{machine} は初期配置から停止し、停止配置は最終文字列 {''.join(vf) or 'λ'} を表す。 -/")
            L.append(f"theorem halts{n} : ∃ N rm, HaltsIn T N ({enc} C{n} w{n}) ({fin} C{n} {lch(vf)} {mf} rm) := by")
            L.append(f"  obtain ⟨k, hk⟩ := run_sound 1000 (by decide) run{n}")
            L.append(f"  obtain ⟨N, rm, -, h⟩ := ({thm} C{n} w{n}).1 k _ _ hk")
            L.append("  exact ⟨N, rm, h⟩")
            if u17:
                q, h, ftape, nsteps = sim_final(path, state, pos, tape)
                fixed = CORRECTIONS.get((path.split("/")[-1], n - 1), steps)
                assert nsteps == fixed, (nsteps, steps, fixed)
                rm = erased
                flen = M["flen"](ra, rm, vf)
                while len(ftape) > flen and ftape[-1] == "b":
                    ftape.pop()
                fpad = len(ftape) - flen
                assert fpad >= 0, (ftape, flen)
                L.append(f"/-- 停止配置の形の照合: 記述ファイルの表を Python で {nsteps} ステップ実行した停止配置"
                         + (f"（原典のコメント {steps} は誤植、tools/gen_lean.py の CORRECTIONS）" if fixed != steps else "")
                         + f"（{q}, ヘッド {h}）が `{fin} C{n} {''.join(vf) or 'λ'} {mf} rm`（rm = {''.join(rm) or 'λ'}）と一致する。 -/")
                L.append(f"theorem fin{n} : {M['fl']} C{n} {lch(vf)} {mf} {lch(rm)} ++ List.replicate {fpad} .s0 = "
                         + "[" + ", ".join(f".{yid[x]}" for x in ftape) + "] ∧\n"
                         + f"    ({fin} C{n} {lch(vf)} {mf} {lch(rm)}).pos = {h} ∧ "
                         + f"({fin} C{n} {lch(vf)} {mf} {lch(rm)}).st = .halt Ps.{pid[q]} := by decide")
            # 記録どおりのステップ数を CTSH の言葉で: M{machine}.K.case{j}（カーネル検証）と、
            # その初期配置・停止配置が enc / fin に等しいこと（`KRun.cfg_eq_of`）から
            fixed = CORRECTIONS.get((path.split("/")[-1], n - 1), steps)
            nz, (fq, fl_, fh, fr), _ = zrun(quints, blank, state, pos, tape, fixed + 5)
            assert nz == fixed, (nz, fixed)
            zlen = max(len(tape), pos + 1)
            elen = len(fl_) + 1 + len(fr)
            if M["fl"]:
                flist = f"{M['fl']} C{n} {lch(vf)} {mf} {lch(erased)}"
                flen = M["flen"](ra, erased, vf)
            else:  # (10,8): finCfg のテープは tapeOf（= tp .s0 (tapeList …)）
                flist = (f"tapeList C{n} {mf} {lch(erased)} []" if not vf
                         else f"tapeList C{n} 0 {lch(erased)} {lch(vf)}")
                flen = 1 + ra + 1 + len(erased) + len(vf)
            assert elen >= flen and zlen >= 1 + ra + 1 + len(w), (elen, flen)
            L.append(f"/-- 記述ファイルの記録（{fixed} ステップ）を CTSH の言葉で: U{machine} は `{enc} C{n} w{n}` から**ちょうど** "
                     f"{fixed} ステップで `{fin} C{n} {''.join(vf) or 'λ'} {mf} rm`（rm = {''.join(erased) or 'λ'}）に停止する。"
                     f"`M{machine}.K.case{j}`（カーネルの評価）と、初期配置・停止配置の一致から。 -/")
            L.append(f"theorem steps{n} : HaltsIn T {fixed} ({enc} C{n} w{n}) ({fin} C{n} {lch(vf)} {mf} {lch(erased)}) := by")
            L.append(f"  have h₁ := KState.Run.cfg_eq_of (bk := .s0) (c := {enc} C{n} w{n}) (z := M{machine}.K.z{j})")
            L.append(f"    ({tl} C{n} 0 [] w{n}) {zlen - (1 + ra + 1 + len(w))} (by decide) (by decide) rfl (by decide)")
            L.append(f"  have h₂ := KState.Run.cfg_eq_of (bk := .s0) (c := {fin} C{n} {lch(vf)} {mf} {lch(erased)}) (z := M{machine}.K.e{j})")
            L.append(f"    ({flist}) {elen - flen} (by decide) (by decide) rfl (by decide)")
            L.append(f"  rw [h₁, h₂]; exact M{machine}.K.case{j}")
            j += 1
        else:
            L.append("/-- 有界の検査のみ（2000 ステップで停止しない）。非停止の証明ではない。 -/")
            L.append(f"theorem run{n} : (run C{n} 2000 (w{n}, 0)).2 = false := by decide +kernel")
    L.append("")
    L.append(f"end URTM.Gen.{module}")
    print("\n".join(L))


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("path")
    ap.add_argument("--module", default="C10_8")
    ap.add_argument("--machine", default="10_8", choices=sorted(MACHINES))
    a = ap.parse_args()
    main(a.path, a.module, a.machine)
