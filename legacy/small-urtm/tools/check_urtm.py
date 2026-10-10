#!/usr/bin/env python3
"""Morita 形式の URTM 記述ファイル（Prolog ファクト）を読み、
サイズ・決定性・可逆性条件を独立に検証する。

使い方:
    python3 tools/check_urtm.py data/urtm/urtm*.txt

可逆性条件 (Morita 2017, Def. 5.4, 五つ組形式):
    相異なる [p1,s1,t1,d1,q1], [p2,s2,t2,d2,q2] について
        q1 = q2  =>  d1 = d2  かつ  t1 != t2
決定性:
        p1 = p2  =>  s1 != s2

注意: 記述ファイルには停止用の 0 シフト五つ組（[...,0,halt] 等）が含まれるため、
五つ組数は Morita 2017 の表の記載より 2 だけ多く出るのが正常。
"""

import sys
from collections import defaultdict


def strip_comments(text: str) -> str:
    return "\n".join(line.split("%")[0] for line in text.splitlines())


def split_top(s: str):
    """深さ 0 のカンマで分割する。"""
    out, depth, cur = [], 0, ""
    for ch in s:
        if ch in "[(":
            depth += 1
        elif ch in "])":
            depth -= 1
        if ch == "," and depth == 0:
            out.append(cur.strip())
            cur = ""
        else:
            cur += ch
    if cur.strip():
        out.append(cur.strip())
    return out


def statements(text: str):
    """深さ 0 の '.' で区切られた節を返す。"""
    depth, cur = 0, ""
    for ch in text:
        if ch in "[(":
            depth += 1
        elif ch in "])":
            depth -= 1
        if ch == "." and depth == 0:
            if cur.strip():
                yield " ".join(cur.split())
            cur = ""
        else:
            cur += ch


def inner(s: str, head: str):
    """head([...]) の中身を返す。無ければ None。"""
    if not s.startswith(head + "("):
        return None
    body = s[len(head) + 1:].strip()
    if body.endswith(")"):
        body = body[:-1].strip()
    if body.startswith("[") and body.endswith("]"):
        body = body[1:-1]
    return split_top(body)


def is_reversible_claim(path):
    """記述ファイルが `reversible(no).` を宣言しているか。

    非可逆の UTM（Rogozhin, Neary-Woods など）も同じ形式で扱えるようにする。
    宣言が無ければ「可逆である」と主張しているとみなして可逆性条件も検査する。"""
    text = strip_comments(open(path, encoding="utf-8", errors="replace").read())
    for st in statements(text):
        if st.replace(" ", "").startswith("reversible(no)"):
            return False
    return True


def parse(path):
    text = strip_comments(open(path, encoding="utf-8", errors="replace").read())
    states = symbols = None
    quints = []
    for st in statements(text):
        got = inner(st, "states")
        if got is not None:
            states = got
            continue
        got = inner(st, "symbols")
        if got is not None:
            symbols = got
            continue
        if st.startswith("["):
            parts = split_top(st[1:-1]) if st.endswith("]") else []
            if len(parts) == 5 and parts[3] in ("+", "-", "0"):
                quints.append(tuple(parts))
    return states, symbols, quints


def check(path):
    states, symbols, quints = parse(path)
    name = path.split("/")[-1]

    used_states = {q[0] for q in quints} | {q[4] for q in quints}
    used_symbols = {q[1] for q in quints} | {q[2] for q in quints}
    declared_states = set(states) if states else set()
    # 停止用の疑似状態（halt, null）は m に数えない
    pseudo = {s for s in used_states - declared_states if s in ("halt", "null")}
    m = len(declared_states) if states else len(used_states - pseudo)
    n = len(symbols) if symbols else len(used_symbols)

    errors = []
    seen = {}
    for q in quints:
        key = (q[0], q[1])
        if key in seen:
            errors.append(f"determinism: duplicated domain {key}")
        seen[key] = q

    claims_rev = is_reversible_claim(path)
    by_next = defaultdict(list)
    for q in quints:
        by_next[q[4]].append(q)
    for nxt, group in (by_next.items() if claims_rev else []):
        dirs = {g[3] for g in group}
        if len(dirs) > 1:
            errors.append(f"reversibility: state {nxt} entered with dirs {sorted(dirs)}")
        writes = [g[2] for g in group]
        if len(set(writes)) != len(writes):
            dup = sorted({w for w in writes if writes.count(w) > 1})
            errors.append(f"reversibility: state {nxt} entered writing same symbol {dup}")

    max_in = max((len(v) for v in by_next.values()), default=0)
    zero_shift = sum(1 for q in quints if q[3] == "0")
    print(f"{name}")
    print(f"  m = {m:5d}  n = {n:6d}  |delta| = {len(quints):5d}"
          f"  (m*n = {m * n}, density {len(quints) / (m * n) * 100:.0f}%,"
          f" zero-shift {zero_shift})")
    print(f"  max in-degree = {max_in} (bound n = {n})"
          + (f", pseudo states {sorted(pseudo)}" if pseudo else ""))
    if symbols and used_symbols - set(symbols):
        print(f"  ! symbols used but not declared: {sorted(used_symbols - set(symbols))[:5]}")
    if not claims_rev:
        print("  非可逆と宣言（reversible(no)）: 決定性のみ検査した")
    if errors:
        for e in errors[:10]:
            print(f"  ! {e}")
        if len(errors) > 10:
            print(f"  ! ... and {len(errors) - 10} more")
        print("  => NOT reversible/deterministic")
    else:
        print("  => deterministic and reversible: OK" if claims_rev
              else "  => deterministic: OK（可逆性は検査対象外）")
    print()
    return not errors


if __name__ == "__main__":
    ok = all([check(p) for p in sys.argv[1:]])
    sys.exit(0 if ok else 1)
