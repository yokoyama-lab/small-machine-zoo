#!/usr/bin/env python3
"""連鎖「タグで 2 状態を併合 → 記号の併合」で得た子の表を、親の表の像として Lean に書くための生成器（2026-11-01）。

子の表を書き写さずに `T.map chg` で定義するため、親と子の記述ファイルと、状態の写像 μ（族 L₁ で併合した対から
決まる。引数で与える。この道具は推定しない）から、規則ごとの読む記号・書く記号の書き換え
（親の規則 (p,s,t,d,q) ↦ 子の規則 (μp,s',t',d,μq)）を求め、Lean の `mu` と `chg` を出力する。
対応は「同じ向き・同じ行き先（μ で写したもの）の子の規則」から取る: 親の読み書きのままの候補があればそれ、
候補がただ 1 つならそれ、複数なら子の表を親と並走させて実際に使われた規則で決める。
検査: 記述ファイルに同じ (状態, 読む記号) の規則が 2 本あれば拒否する。写した像が子の表と集合として一致し、
写し方が単射（像の本数 = 親の本数 = 子の本数）であることを確かめる。

`--multi`（2026-11-02、(10,7) 用）: 親の 1 本が子の複数本に写ることを許す（族 L₁ と記号の併合を同時に解いた表では、
同じ親の規則が通る時のタグによって別の色の規則になる）。各親の規則の像は並走で実際に使われた (読む, 書く) の組
すべて（並走で一度も使われない規則は、親の読み書きのままの候補か、ただ 1 つの候補）。像は重なってよい
（別の親の規則が同じ子の規則に写る）。検査は「像の集合 = 子の集合」。Lean には `chgSym` を `List (Sy × Sy)` で、
表を `(T.flatMap chg).eraseDups` で書く。単射でないので、像の本数（重複込み）・親の本数・子の本数を標準エラーに出す。
`--random N`: 並走の標本に乱択の CTSH（fewsym.random_ctsh、種 `--seed`）を N 件足す（記述ファイルの試験例だけでは
全部の規則がすべてのタグで通らないことがある）。

使い方:
  python3 gen_tagchain_lean.py [--multi] [--random N] [--seed S] PARENT CHILD STATEMAP_JSON PARENT_GEN_NAMES_JSON
    STATEMAP_JSON: 親の状態名 → 子の状態名（併合した状態だけ）
    PARENT_GEN_NAMES_JSON: {"states": {親の状態名: Lean の構成子}, "symbols": {記号名: Lean の構成子}}
出力: Lean の断片（標準出力）と、検査の結果（標準エラー）。子の記号名は親の記号名と同じであること（併合で吸収済み）。
"""
import json
import re
import sys

MV = {"-": -1, "+": 1, "0": 0}
DIRL = {"-": "L", "+": "R", "0": "Z"}


def load(path):
    txt = open(path, encoding="utf-8").read().replace("\r", "")
    rules = {}
    dups = []
    for ln in txt.splitlines():
        ln = ln.split("%")[0].strip().replace(" ", "")
        m = re.fullmatch(r"\[([^,\]]+),([^,\]]+),([^,\]]+),([-+0]),([^,\]]+)\]\.", ln)
        if m:
            p, s, t, d, q = m.groups()
            if (p, s) in rules:
                dups.append((p, s))
            rules[(p, s)] = (t, d, q)
    if dups:
        sys.exit(f"{path}: 同じ (状態, 読む記号) の規則が複数ある: {dups}")
    cases = []
    for m in re.finditer(r"initial_conf\(\[(\w+),(\d+),\[(.*?)\]\]\)", txt):
        cases.append((m.group(1), int(m.group(2)), m.group(3).replace(" ", "").split(",")))
    return rules, cases


def lockstep_use(P, C, mu, cases, rng_runs=200):
    """親の規則 → 子の規則（実際に並走で使われた対応）。"""
    used = {}
    runs = list(cases)
    for st, pos, tape in runs:
        tp, tc, sp, sc, p = list(tape), list(tape), st, mu.get(st, st), pos
        for _ in range(200000):
            while p >= len(tp):
                tp.append("b")
                tc.append("b")
            rp = P.get((sp, tp[p]))
            rc = C.get((sc, tc[p]))
            if rp is None or rc is None:
                break
            used.setdefault((sp, tp[p]), set()).add((tc[p], rc[0]))
            tp[p], tc[p] = rp[0], rc[0]
            p += MV[rp[1]]
            sp, sc = rp[2], rc[2]
            if sp in ("halt", "null"):
                break
    return used


def random_cases(parent_path, n, seed):
    """乱択の CTSH の初期配置（fewsym の符号化。親が Morita 型の (13,7) 系であること）。"""
    import os
    import random
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    import fewsym as FS
    T = FS.Base(parent_path)
    rng = random.Random(seed)
    out = []
    for i in range(n):
        C, w = FS.random_ctsh(rng, 8, 7, 9) if i % 2 else FS.random_ctsh(rng)
        out.append(FS.ctsh_tape(T, C, w))
    return out


def solve(P, C, mu, cases, multi, SY=None):
    """親の (状態, 読む記号) → 子の (読む記号, 書く記号) の組の列（multi でなければ高々 1 つ）。
    返り値: (chg, ok)。chg は親の規則ごとの組の列（親の読み書きのままの 1 本だけなら載せない）。
    「親の読み書きのまま」は Lean の構成子（SY）で比べる（子の記号名が親と違っても同じ構成子なら同じ）。"""

    def m(s):
        return mu.get(s, s)

    def same(a, b):
        return (SY or {}).get(a, a) == (SY or {}).get(b, b)

    def same_pair(x, y):
        return same(x[0], y[0]) and same(x[1], y[1])

    chg, ok = {}, True
    used = lockstep_use(P, C, mu, cases)
    for (p, s), (t, d, q) in sorted(P.items()):
        cand = [(s2, t2) for (p2, s2), (t2, d2, q2) in C.items() if p2 == m(p) and d2 == d and q2 == m(q)]
        u = used.get((p, s), set())
        if multi and u:
            if not u <= set(cand):
                print(f"並走で使われた組が候補に無い: {(p, s, t, d, q)} 候補 {cand} 並走 {sorted(u)}", file=sys.stderr)
                ok = False
                continue
            if not (len(u) == 1 and same_pair(next(iter(u)), (s, t))):
                chg[(p, s)] = sorted(u)
            continue
        if any(same_pair(x, (s, t)) for x in cand):
            continue
        if len(cand) == 1:
            chg[(p, s)] = [cand[0]]
            continue
        if len(u) != 1:
            print(f"未決: {(p, s, t, d, q)} 候補 {cand} 並走 {sorted(u)}", file=sys.stderr)
            ok = False
            continue
        chg[(p, s)] = [u.pop()]
    return chg, ok


def main():
    args = sys.argv[1:]
    multi, nrand, seed = False, 0, 1
    while args and args[0].startswith("--"):
        a = args.pop(0)
        if a == "--multi":
            multi = True
        elif a == "--random":
            nrand = int(args.pop(0))
        elif a == "--seed":
            seed = int(args.pop(0))
        else:
            sys.exit(f"unknown option {a}")
    P, cases = load(args[0])
    C, _ = load(args[1])
    mu = json.loads(args[2])
    names = json.loads(args[3])
    ST, SY = names["states"], names["symbols"]
    if nrand:
        cases = list(cases) + random_cases(args[0], nrand, seed)

    def m(s):
        return mu.get(s, s)

    chg, ok = solve(P, C, mu, cases, multi, SY)
    # 検査: 写した表が子の表と集合として一致するか（記号は Lean の構成子で比べる）
    def sy(x):
        return SY.get(x, x)

    img, nimg = set(), 0
    for (p, s), (t, d, q) in P.items():
        for s2, t2 in chg.get((p, s), [(s, t)]):
            img.add((m(p), sy(s2), sy(t2), d, m(q)))
            nimg += 1
    child = {(p, sy(s), sy(t), d, q) for (p, s), (t, d, q) in C.items()}
    if multi:
        print(f"親 {len(P)} 本、書き換え {len(chg)} 本（うち 2 本以上に写るもの {sum(1 for v in chg.values() if len(v) > 1)}）、"
              f"像 {nimg} 本（重複を除いて {len(img)} 本）、子 {len(child)} 本、一致 {img == child}", file=sys.stderr)
        ok &= img == child
    else:
        inj = len(img) == len(P) == len(child)
        print(f"親 {len(P)} 本、書き換え {len(chg)} 本、像 {len(img)} 本、子 {len(child)} 本、一致 {img == child}、単射 {inj}",
              file=sys.stderr)
        ok &= img == child and inj
    # Lean
    out = ["/-- 状態の併合（親の状態 → 子の状態）。 -/", "def mu : St → St"]
    for a, b in sorted(mu.items()):
        out.append(f"  | .{ST[a]} => .{ST[b]}")
    out.append("  | q => q")
    out += ["", "def muT : Tgt St Ps → Tgt St Ps", "  | .go q => .go (mu q)", "  | .halt h => .halt h", ""]
    if multi:
        out += ["/-- 書き換える規則（親の (状態, 読む記号) → 子の (読む記号, 書く記号) の列）。生成器 tools/gen_tagchain_lean.py --multi。 -/",
                "def chgSym (p : St) (s t : Sy) : List (Sy × Sy) :=", "  match p, s with"]
        for (p, s), prs in sorted(chg.items()):
            out.append(f"  | .{ST[p]}, .{SY[s]} => [" + ", ".join(f"(.{SY[s2]}, .{SY[t2]})" for s2, t2 in prs) + "]")
        out.append("  | _, _ => [(s, t)]")
        out += ["", "def chg (r : Rule St Ps Sy) : List (Rule St Ps Sy) :=",
                "  (chgSym r.p r.s r.t).map fun st => ⟨mu r.p, st.1, st.2, r.d, muT r.q⟩", "",
                "-- 子の表: (T.flatMap chg).eraseDups"]
    else:
        out += ["/-- 書き換える規則（親の (状態, 読む記号) → 子の (読む記号, 書く記号)）。生成器 tools/gen_tagchain_lean.py。 -/",
                "def chgSym (p : St) (s t : Sy) : Sy × Sy :=", "  match p, s with"]
        for (p, s), prs in sorted(chg.items()):
            (s2, t2), = prs
            out.append(f"  | .{ST[p]}, .{SY[s]} => (.{SY[s2]}, .{SY[t2]})")
        out.append("  | _, _ => (s, t)")
        out += ["", "def chg (r : Rule St Ps Sy) : Rule St Ps Sy :=",
                "  ⟨mu r.p, (chgSym r.p r.s r.t).1, (chgSym r.p r.s r.t).2, r.d, muT r.q⟩"]
    print("\n".join(out))
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
