#!/usr/bin/env python3
"""URTM 記述ファイルのシミュレータ（Morita の SWI-Prolog 版とは独立の実装）。

記述ファイルには `initial_conf([state, pos, [tape...]])` が複数書かれており、
直後の `%%` 行に期待される停止ステップ数と出力がコメントされている。
これを回帰テストの正解表として突き合わせる。

    python3 tools/simulate.py data/urtm/urtm10-8.txt
    python3 tools/simulate.py --check data/urtm/urtm*.txt   # 期待値と一致するか

pos は 0 起点。テープは右へ空白で伸ばす。規則が無ければ停止。
"""

import re
import sys

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from check_urtm import parse, split_top, strip_comments, statements  # noqa: E402

CONF = re.compile(r"initial_conf\(\s*\[")
EXPECT = re.compile(r"^\s*%%\s*([\d,]+)\s*(\S*)")  # 桁区切りのコンマが入ることがある


def read_cases(path):
    """(初期配置, 期待ステップ数 or None, 期待出力 or None) の列を返す。

    コメントアウトされた initial_conf も含める（そちらが本体の試験例）。
    """
    cases = []
    lines = open(path, encoding="utf-8", errors="replace").read().splitlines()
    for i, line in enumerate(lines):
        body = line.lstrip().lstrip("%").strip()
        if not body.startswith("initial_conf("):
            continue
        inner = body[len("initial_conf("):].rstrip()
        inner = inner.rstrip(".").rstrip(")").strip()
        if inner.startswith("[") and inner.endswith("]"):
            inner = inner[1:-1]
        parts = split_top(inner)
        if len(parts) != 3:
            continue
        state, pos, tape = parts[0], int(parts[1]), parts[2]
        tape = split_top(tape.strip()[1:-1])
        steps = out = None
        if i + 1 < len(lines):
            m = EXPECT.match(lines[i + 1])
            if m:
                steps = int(m.group(1).replace(",", ""))
                out = m.group(2) or None
        cases.append((state, pos, tape, steps, out))
    return cases


def fact_of(path, head, default=None):
    """head(...) の引数を文字列で返す。無ければ default。"""
    text = strip_comments(open(path, encoding="utf-8", errors="replace").read())
    for st in statements(text):
        if st.startswith(head + "("):
            return st[len(head) + 1:].rstrip(")").strip()
    return default


def maxstep_of(path):
    return int(fact_of(path, "maxstep", "100000"))


def blank_of(path):
    """空白記号は blank(...) ファクトで決まる。symbols() の先頭ではない
    （urtm4-168 は symbols がソートされており先頭は $）。"""
    return fact_of(path, "blank", "b")


def run(quints, blank, state, pos, tape, limit):
    delta = {(p, s): (t, d, q) for (p, s, t, d, q) in quints}
    tape = list(tape)
    for step in range(limit + 1):
        while pos >= len(tape):
            tape.append(blank)
        if pos < 0:
            return step, "".join(tape), "fell off the left end"
        r = delta.get((state, tape[pos]))
        if r is None:
            return step, "".join(tape), "halt (no rule)"
        t, d, q = r
        tape[pos] = t
        pos += {"-": -1, "0": 0, "+": 1}[d]
        state = q
        if q in ("halt", "null"):
            return step + 1, "".join(tape), f"halt ({q})"
    return limit, "".join(tape), "maxstep reached"


def main(paths, check):
    allok = True
    for path in paths:
        states, symbols, quints = parse(path)
        blank = blank_of(path)
        limit = maxstep_of(path)
        name = path.split("/")[-1]
        for k, (state, pos, tape, exp_steps, exp_out) in enumerate(read_cases(path)):
            steps, final, why = run(quints, blank, state, pos, tape, limit)
            ok = exp_steps is None or steps == exp_steps
            allok &= ok
            mark = "ok " if ok else "NG "
            if check:
                print(f"{mark}{name} case{k}: steps={steps} (expected {exp_steps}) {why}")
            else:
                print(f"{name} case{k}: steps={steps} {why}\n    tape={final}")
    return allok


if __name__ == "__main__":
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    sys.exit(0 if main(args, "--check" in sys.argv) else 1)
