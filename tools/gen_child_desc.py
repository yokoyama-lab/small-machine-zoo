#!/usr/bin/env python3
"""親の記述ファイルと Lean の `mu`・`chgSym` から、子（状態を併合した URTM）の記述ファイルを書く（2026-11-02）。

五つ組の表は zoo に置かない方針なので、URTM(11,7) の記述ファイル data/urtm/urtm11-7.txt（記号の併合の生成器
tools/gen_symmerge_lean.py が (4,40) の記録 urtm11-7.k4.r47.m40 を作るのに要る）は、Morita の配布物 data/urtm/urtm13-7.txt
（tools/fetch_data.sh）と、Lean の表 `T11 = T.map chg`（lean/URTM/CTSH11_7.lean の `mu`・`chgSym`）から作り直す。
出力は 2026-11-01 に艦隊で作った記述ファイルとバイト単位で一致しなければならない（spec の md5。一致しなければ出力を
<out>.mismatch に改名して rc=1。fail-closed）。tools/fetch_data.sh の末尾と tools/gen_all_lean.sh の先頭が呼ぶ。

    python3 tools/gen_child_desc.py results/chain-2026-11-01/urtm11-7.desc.json [DATA_DIR]   (default: data)

spec（JSON）: parent（data/urtm の親のファイル名）、child（書く名前）、lean（mu・chgSym を読む Lean ファイル）、
title（子の title 行の中身。もとの道具が中間ファイル名を書いたもので、再現には要る）、md5（期待値）。

子の形式（もとの道具 chain_merge.py の出力と同じ）: title / initial_state / final_states / blank / maxstep は親のもの、
states は併合後の名前を辞書順、symbols は空白を先頭にして残りを辞書順、試験例は親の `initial_conf` と直後の `%%` 行を
`% initial_conf(...)` の形で並べる（親の空行は落とす）、規則は (状態, 読む記号, …) の辞書順。改行は LF。
併合した状態の名前は `m_` に併合した親の状態名を辞書順につないだもの。

2026-11-03（T19）: URTM(10,7) の記述ファイル data/urtm/urtm10-7.txt を、(11,7) と Lean の `T10 = (T11.flatMap chg).eraseDups`
（lean/URTM/CTSH10_7.lean）から作るために、spec に次の任意の欄を足した（無ければ従来どおり）。
  index   : 親の desc spec のパス。Lean の番号 qI・sJ が親でなく祖先（(13,7)）の並びのとき。祖先の states・symbols と
            祖先 → 親の併合（その spec の Lean の mu）から、番号 → 親の名前を作る。
  naming  : "sorted"（既定、上の形）か "pair"（joint_merge.py の形 `m_<併合される側>_<代表>`）。
  rename  : 子の記号名の付け替え（joint_merge.py は色の代表の名前を記号名にする）。
  comments: 試験例の代わりに置く行（joint_merge.py の write_table の `% color` の行。作った道具の色分けの記録で、
            Lean には無い。title と同じく、艦隊の表とバイト単位で一致させるためだけに spec に持つ）。
  dedup   : chgSym の腕がリスト（1〜2 本の像）で、像の重なりを 1 本にまとめる（eraseDups）。無ければ重なりは誤り。
  rules   : 子の本数の期待値（違えば rc=1）。
"""
import hashlib
import json
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
RULE = re.compile(r"\[([^,\]]+),([^,\]]+),([^,\]]+),([-+0]),([^,\]]+)\]\.")
CASE = re.compile(r"initial_conf\(\[(\w+),(\d+),\[(.*?)\]\]\)")
FACT = re.compile(r"^(initial_state|final_states|blank|maxstep|states|symbols)\((.*)\)\.\s*$")


def parse_parent(text):
    """(facts, rules, cases)。facts は名前 → 括弧の中身。rules は (p,s,t,d,q) の列（ファイルの順）。
    cases は (initial_conf の行の中身, 直後の %% 行) の列。"""
    lines = [ln.replace("\r", "").rstrip() for ln in text.split("\n")]
    facts, rules, cases = {}, [], []
    for i, ln in enumerate(lines):
        m = FACT.match(ln.strip())
        if m and m.group(1) not in facts:
            facts[m.group(1)] = m.group(2).replace(" ", "")
        code = ln.split("%")[0].strip().replace(" ", "")
        m = RULE.fullmatch(code)
        if m:
            rules.append(m.groups())
        m = CASE.search(ln)
        if m:
            nxt = lines[i + 1].strip() if i + 1 < len(lines) else ""
            cases.append((f"initial_conf([{m.group(1)},{m.group(2)},[{m.group(3).replace(' ', '')}]])",
                          nxt if nxt.startswith("%%") else None))
    for k in ("initial_state", "final_states", "blank", "maxstep", "states", "symbols"):
        if k not in facts:
            raise SystemExit(f"parent: no {k}(...) line")
    return facts, rules, cases


def parse_lean(text):
    """`def mu` の腕 (i → j) と `def chgSym` の腕 ((i, s) → (s', t'))。番号は構成子 qI・sJ のもの。"""
    mu, chg, block = {}, {}, None
    for ln in text.split("\n"):
        if re.match(r"^def mu\b", ln):
            block = "mu"
            continue
        if re.match(r"^def chgSym\b", ln):
            block = "chg"
            continue
        if block and not ln.startswith(" "):
            block = None
        if block == "mu":
            m = re.match(r"^\s*\|\s*\.q(\d+)\s*=>\s*\.q(\d+)\s*$", ln)
            if m:
                mu[int(m.group(1))] = int(m.group(2))
        elif block == "chg":
            # 1 本に写る腕 `| .qI, .sJ => (.sA, .sB)` と、1〜2 本に写る腕 `| .qI, .sJ => [(.sA, .sB), (.sC, .sD)]`
            # （tools/gen_tagchain_lean.py --multi の出力）。どちらも像の列として持つ。
            m = re.match(r"^\s*\|\s*\.q(\d+),\s*\.s(\d+)\s*=>\s*(.*?)\s*$", ln)
            if m:
                rhs = m.group(3)
                pairs = [(int(a), int(b)) for a, b in re.findall(r"\(\.s(\d+),\s*\.s(\d+)\)", rhs)]
                single = re.fullmatch(r"\(\.s\d+,\s*\.s\d+\)", rhs)
                multi = re.fullmatch(r"\[\s*\(\.s\d+,\s*\.s\d+\)(\s*,\s*\(\.s\d+,\s*\.s\d+\))*\s*\]", rhs)
                if not (single or multi):
                    raise SystemExit(f"lean: chgSym arm not understood: {ln.strip()}")
                chg[(int(m.group(1)), int(m.group(2)))] = pairs
    if not mu:
        raise SystemExit("lean: no `def mu` arms `| .qI => .qJ`")
    return mu, chg


def merge_names(states, mu, naming="sorted"):
    """状態の併合 mu（番号 i → 代表の番号 j）の下での、親の状態名 → 子の状態名。
    naming="sorted": `m_` に類の親の名前を辞書順につなぐ（chain_merge.py の形）。
    naming="pair": 類は 2 つで、`m_<併合される側 i>_<代表 j>`（joint_merge.py の形、mu = {a: m_a_b, b: m_a_b}）。"""
    for i, j in mu.items():
        if not (0 <= i < len(states) and 0 <= j < len(states)):
            raise SystemExit(f"lean: mu refers to state q{i} or q{j} outside the {len(states)} indexed states")
    group = {q: {q} for q in states}
    for i, j in mu.items():
        group[states[j]] |= {states[i]}
    for q in list(group):
        for r in group[q]:
            group[r] = group[q]
    name = {}
    for q in states:
        if len(group[q]) == 1:
            name[q] = q
        elif naming == "sorted":
            name[q] = "m_" + "".join(sorted(group[q]))
        elif naming == "pairsorted":
            name[q] = "m_" + "_".join(sorted(group[q]))
        elif naming == "pair":
            src = [states[i] for i in mu if states[i] in group[q]]
            dst = [states[j] for j in mu.values() if states[j] in group[q]]
            if len(group[q]) != 2 or len(src) != 1 or len(set(dst)) != 1:
                raise SystemExit(f"naming=pair needs classes of exactly two states, got {sorted(group[q])}")
            name[q] = f"m_{src[0]}_{dst[0]}"
        else:
            raise SystemExit(f"unknown naming {naming!r}")
    return name


def build(parent_text, lean_text, title, **kw):
    """子の記述ファイルの本文（build_full の 1 つ目）。"""
    return build_full(parent_text, lean_text, title, **kw)[0]


def child_image(parent_text, lean_text, index=None, naming="sorted", rename=None, rules=None, csyms=None):
    """親の規則を Lean の mu・chgSym で写した像（build_full の前半）。
    (facts, cases, 親の規則の列, 像の列（重なり込み・親の規則の順。Lean の `T.map chg` / `T.flatMap chg` の並び）,
    cname（親の状態名 → 子の状態名）, pst（親の状態の列）, isy（番号順の記号名）, sy（番号 → 子の記号名）)。
    rules: 親の規則の列（名前の五つ組）を与えると、記述ファイルの並びでなくその並びで写す（`lean_order_rules`）。"""
    facts, prules, cases = parse_parent(parent_text)
    if rules is not None:
        prules = [tuple(r) for r in rules]
    states = facts["states"].strip("[]").split(",")
    symbols = facts["symbols"].strip("[]").split(",")
    mu, chg = parse_lean(lean_text)
    rename = rename or {}
    if index is None:
        ist, isy = list(states), list(symbols)
    else:
        bst, bsy, bmu, bnaming = index
        bname = merge_names(bst, bmu, bnaming)
        ist = [bname[q] if bmu.get(i, i) == i else None for i, q in enumerate(bst)]  # 代表でない番号は使わない
        isy = list(bsy)
        if sorted(q for q in ist if q is not None) != sorted(states):
            raise SystemExit("index: the ancestor's states merged by its mu are not the parent's states")
        if sorted(isy) != sorted(symbols):
            raise SystemExit("index: the ancestor's symbols are not the parent's symbols")
    # 子の併合（Lean の mu は番号で書かれる）を親の名前の上に写す
    for i, j in mu.items():
        if not (0 <= i < len(ist) and 0 <= j < len(ist)) or ist[i] is None or ist[j] is None:
            raise SystemExit(f"lean: mu refers to q{i} or q{j}, which is not a state of the parent")
    pst = [q for q in ist if q is not None]
    pid = {q: i for i, q in enumerate(ist) if q is not None}
    yid = {y: j for j, y in enumerate(isy)}
    cname = merge_names(pst, {pst.index(ist[i]): pst.index(ist[j]) for i, j in mu.items()}, naming)
    pseudo = set()

    def st(q):
        if q in cname:
            return cname[q]
        pseudo.add(q)
        return q

    if csyms is not None:                 # 子の記号名を番号ごとに与える（子の記号が親より多いとき。T28）
        if rename:
            raise SystemExit("symbols and rename are exclusive")
        if len(csyms) < len(isy) or len(set(csyms)) != len(csyms):
            raise SystemExit("symbols: the child's symbol list is shorter than the parent's, or has a repeated name")

    def sy(j):
        if csyms is not None:
            return csyms[j]
        return rename.get(isy[j], isy[j])

    image = []
    for (p, s, t, d, q) in prules:
        if p not in pid or s not in yid or t not in yid:
            raise SystemExit(f"parent rule {(p, s, t, d, q)} uses a name outside states/symbols")
        for (s2, t2) in chg.get((pid[p], yid[s]), [(yid[s], yid[t])]):
            image.append((st(p), sy(s2), sy(t2), d, st(q)))
    return facts, cases, prules, image, cname, pst, isy, sy


def build_full(parent_text, lean_text, title, index=None, naming="sorted", comments=None, rename=None, dedup=False,
               symbols=None):
    """(子の記述ファイルの本文, 親の本数, 像の本数（重なり込み）, 子の本数)。

    index: Lean の番号 qI・sJ が親の並びでなく祖先の並びのとき（(10,7) の Lean は (13,7) の番号で書かれ、親は (11,7)）、
      (祖先の states, 祖先の symbols, 祖先 → 親の併合 mu, その naming)。番号 i の状態の親での名前は、祖先の名前を
      併合で写したもの。親の併合した状態の番号は、その類の代表（祖先の mu で写されない側）。
    naming: 子の併合した状態の名前の付け方（merge_names）。
    comments: None なら親の試験例を写す（chain_merge.py の形）。行の列なら試験例の代わりにその行を置く
      （joint_merge.py の write_table の形。`% color` の行。表の情報ではなく、作った道具の色分けの記録）。
    rename: 子の記号名の付け替え（親の名前 → 子の名前）。joint_merge.py は色の代表の名前を記号名にする。
    dedup: chgSym の腕は 1 本か複数本の像（parse_lean）。True なら像の重なり（同じ五つ組）を 1 本にまとめる
      （Lean の `(T.flatMap chg).eraseDups`）。False（`T.map chg` の形）なら重なりは併合の誤りとして止める。
    """
    facts, cases, rules, image, cname, pst, isy, sy = child_image(parent_text, lean_text, index, naming, rename,
                                                                   csyms=symbols)
    rename = rename or {}
    out = sorted(set(image))  # 集合として Lean の eraseDups と同じ
    if not dedup and len(out) != len(image):
        raise SystemExit("two parent rules give the same child rule (the image is not injective; set dedup for eraseDups)")
    keys = [(r[0], r[1]) for r in out]
    if len(set(keys)) != len(keys):
        raise SystemExit("the child is not deterministic (same state and read symbol twice)")
    cstates = sorted({cname[q] for q in pst if any(r[0] == cname[q] for r in out)})
    if len(cstates) != len(set(cname.values())):
        raise SystemExit("a merged state has no rule")
    blank = facts["blank"]
    if blank in rename:
        raise SystemExit("rename: the blank keeps its name")
    allsyms = set(symbols) if symbols is not None else {sy(j) for j in range(len(isy))}
    if len(allsyms) != (len(symbols) if symbols is not None else len(isy)):
        raise SystemExit("rename: two symbols get the same name")
    if symbols is not None and (blank not in symbols or symbols.index(blank) != 0):
        raise SystemExit("symbols: the blank must be the symbol number 0")
    csyms = [blank] + sorted(allsyms - {blank})
    L = [f"title('{title}').", f"initial_state({facts['initial_state']}).", f"final_states({facts['final_states']}).",
         f"states([{','.join(cstates)}]).", f"symbols([{','.join(csyms)}]).", f"blank({blank}).",
         f"maxstep({facts['maxstep']}).", ""]
    if comments is None:
        for conf, note in cases:
            L.append(f"% {conf}.")
            if note is not None:
                L.append(note)
    else:
        L += list(comments)
    L.append("")
    L += [f"[{','.join(r)}]." for r in out]
    return "\n".join(L) + "\n", len(rules), len(image), len(out)


def lean_order_rules(spec_path, ddir=None):
    """子の規則を Lean の表の並びで返す（名前の五つ組の列。2026-11-04、T25）。Lean の表は親の規則の順に写した
    `T.map chg`（(11,7)）や `(T.flatMap chg).eraseDups`（(10,7)）なので、親の規則を Lean の順に並べ（spec に `index` が
    あれば親の spec で再帰的に求める。祖先の記述ファイル（Morita の配布物）は Lean の `T` と同じ順）、mu・chgSym の腕の順に
    写し、重なりは最初の 1 本を残す（`List.eraseDups`）。tools/gen_blocks_lean.py の `lean_order_spec` が使う。"""
    ddir = os.path.abspath(ddir) if ddir else os.path.join(ROOT, "data")
    spec = json.load(open(spec_path if os.path.isabs(spec_path) else os.path.join(ROOT, spec_path), encoding="utf-8"))
    ppath = os.path.join(ddir, "urtm", spec["parent"])
    if not os.path.exists(ppath):
        raise SystemExit(f"FAIL: {os.path.relpath(ppath, ROOT)} is missing (run tools/fetch_data.sh)")
    rules = lean_order_rules(spec["index"], ddir) if "index" in spec else None
    _f, _c, _p, image, *_ = child_image(open(ppath, encoding="utf-8", newline="").read(),
                                       open(os.path.join(ROOT, spec["lean"]), encoding="utf-8").read(),
                                       index=load_index(spec, ddir), naming=spec.get("naming", "sorted"),
                                       rename=spec.get("rename"), rules=rules, csyms=spec.get("symbols"))
    if not spec.get("dedup", False) and len(set(image)) != len(image):
        raise SystemExit("two parent rules give the same child rule (the image is not injective; set dedup for eraseDups)")
    return list(dict.fromkeys(image))


def number_names(spec, ddir):
    """spec の子の、Lean の番号ごとの名前 (ist, isy)。ist[i] は番号 i の状態の子での名前（併合で代表でない番号は None）、
    isy[j] は番号 j の記号の子での名前。spec に index が無ければ番号は親の記述ファイルの並び、あれば祖先の spec で
    再帰的に求める（T28、2026-11-05: (9,8) の Lean は (13,7) の番号で書かれ、親 (10,7) の spec も index を持つ）。"""
    spec = spec if isinstance(spec, dict) else json.load(open(os.path.join(ROOT, spec), encoding="utf-8"))
    mu, _chg = parse_lean(open(os.path.join(ROOT, spec["lean"]), encoding="utf-8").read())
    rename = spec.get("rename") or {}
    if "index" in spec:
        ist_p, isy_p = number_names(spec["index"], ddir)
    else:
        apath = os.path.join(ddir, "urtm", spec["parent"])
        if not os.path.exists(apath):
            raise SystemExit(f"FAIL: {os.path.relpath(apath, ROOT)} is missing (run tools/fetch_data.sh)")
        facts, _r, _c = parse_parent(open(apath, encoding="utf-8", newline="").read())
        ist_p = facts["states"].strip("[]").split(",")
        isy_p = facts["symbols"].strip("[]").split(",")
    for i, j in mu.items():
        if not (0 <= i < len(ist_p) and 0 <= j < len(ist_p)) or ist_p[i] is None or ist_p[j] is None:
            raise SystemExit(f"index: mu of {spec['lean']} refers to q{i} or q{j}, which is not a state of its parent")
    pst = [q for q in ist_p if q is not None]
    cname = merge_names(pst, {pst.index(ist_p[i]): pst.index(ist_p[j]) for i, j in mu.items()},
                        spec.get("naming", "sorted"))
    ist = [cname[q] if (q is not None and mu.get(i, i) == i) else None for i, q in enumerate(ist_p)]
    if "symbols" in spec:
        isy = list(spec["symbols"])
    else:
        isy = [rename.get(y, y) for y in isy_p]
    return ist, isy


def load_index(spec, ddir):
    """spec の index（親の desc spec のパス）から、Lean の番号ごとの親の名前（`number_names`。代表でない番号は None）と
    記号名を読む。child_image には「祖先の並び＝親の名前そのもの、併合なし」の形で渡す。"""
    if "index" not in spec:
        return None
    ist, isy = number_names(spec["index"], ddir)
    return (ist, isy, {}, "sorted")


def main():
    # 引数: SPEC [DATA_DIR]。DATA_DIR は fetch_data.sh の出力先（既定 data）。親を読み、子を書く場所は DATA_DIR/urtm。
    if len(sys.argv) not in (2, 3):
        raise SystemExit(__doc__)
    spec = json.load(open(sys.argv[1], encoding="utf-8"))
    ddir = os.path.abspath(sys.argv[2]) if len(sys.argv) == 3 else os.path.join(ROOT, "data")
    ppath = os.path.join(ddir, "urtm", spec["parent"])
    out = os.path.join(ddir, "urtm", spec["child"])
    if not os.path.exists(ppath):
        raise SystemExit(f"FAIL: {os.path.relpath(ppath, ROOT)} is missing (run tools/fetch_data.sh)")
    text, npar, nimg, nout = build_full(open(ppath, encoding="utf-8", newline="").read(),
                                   open(os.path.join(ROOT, spec["lean"]), encoding="utf-8").read(), spec["title"],
                                   index=load_index(spec, ddir), naming=spec.get("naming", "sorted"),
                                   comments=spec.get("comments"), rename=spec.get("rename"),
                                        dedup=spec.get("dedup", False), symbols=spec.get("symbols"))
    print(f"  {spec['child']}: parent {npar} rules -> image {nimg} -> child {nout} rules")
    if "rules" in spec and nout != spec["rules"]:
        print(f"FAIL: {spec['child']}: {nout} rules, the spec says {spec['rules']}")
        return 1
    got = hashlib.md5(text.encode("utf-8")).hexdigest()
    if got != spec["md5"]:
        bad = out + ".mismatch"
        with open(bad, "w", encoding="utf-8", newline="\n") as f:
            f.write(text)
        print(f"FAIL: {spec['child']}: md5 {got} differs from the recorded {spec['md5']} (written to {os.path.relpath(bad, ROOT)})")
        return 1
    if os.path.exists(out) and open(out, encoding="utf-8", newline="").read() == text:
        print(f"ok: {os.path.relpath(out, ROOT)} is already the recorded file (md5 {got})")
        return 0
    with open(out, "w", encoding="utf-8", newline="\n") as f:
        f.write(text)
    print(f"ok: wrote {os.path.relpath(out, ROOT)} from {spec['parent']} and {spec['lean']} (md5 {got})")
    return 0


if __name__ == "__main__":
    sys.exit(main())
