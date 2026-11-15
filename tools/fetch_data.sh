#!/usr/bin/env bash
# Morita 公開の URTM 記述ファイルを**原典から**取得する。
#
# このリポジトリは Morita のファイルを再配布しない。原典は広島大学学術情報リポジトリの
# オープンアクセス資料であり、記述ファイル 13 本はそのスライド PDF の
# **添付ファイル**として埋め込まれている（pdfdetach で取り出す）。
#
#   K. Morita, "Constructing small universal reversible Turing machines
#   (slides with figures of computer simulation)", 広島大学学術情報リポジトリ, 2015.
#   https://hiroshima.repo.nii.ac.jp/records/2000034
#
# 「無い状態から始めて再現できるか」を確かめる意味でも、CI は毎回ここから取る。
#
#   ./tools/fetch_data.sh [出力先ディレクトリ]   （既定: data）
#
# 必要なもの: curl, pdfdetach（poppler-utils）

set -euo pipefail

URL="https://hiroshima.repo.nii.ac.jp/record/2000034/files/Morita_URTM.pdf"
SHA256="e36b9edd31d80d52d6f4cdc7433510e4c1ff3d9cf0359386ae3d3bd63f4b9524"
OUT="${1:-data}"
PDF="$OUT/Morita_URTM_slides_2015.pdf"

command -v pdfdetach >/dev/null || { echo "pdfdetach が無い（poppler-utils を入れる）"; exit 127; }

mkdir -p "$OUT"
if [ ! -s "$PDF" ]; then
  echo "取得中: $URL"
  curl -sSL --retry 3 --max-time 600 -o "$PDF" "$URL"
fi

got="$(sha256sum "$PDF" | awk '{print $1}')"
if [ "$got" != "$SHA256" ]; then
  echo "⚠ PDF のハッシュが記録と違う（原典が更新された可能性）"
  echo "  期待: $SHA256"
  echo "  実際: $got"
  echo "  内容を確認したうえで、このスクリプトの SHA256 を更新すること。"
  exit 1
fi
echo "✓ 原典のハッシュ一致"

mkdir -p "$OUT/urtm"
pdfdetach -saveall -o "$OUT/urtm" "$PDF" >/dev/null
n=$(find "$OUT/urtm" -maxdepth 1 -name "urtm*.txt" ! -name "urtm11-7.txt" ! -name "urtm10-7.txt" ! -name "urtm9-8n.txt" | wc -l)   # the three files below are generated, not extracted
echo "✓ 添付ファイルを展開: URTM 記述ファイル $n 本 -> $OUT/urtm/"
[ "$n" -eq 9 ] || { echo "⚠ 9 本のはずが $n 本しか無い"; exit 1; }

# Description files that are not in Morita's distribution, rebuilt from it and the Lean definitions
# (the map mu and chgSym of the CTSH<m>_<n>.lean module). Each run stops if the md5 differs from the recorded one.
# URTM(11,7): two pairs of states of (13,7) merged (lean/URTM/CTSH11_7.lean).
python3 "$(dirname "$0")/gen_child_desc.py" "$(dirname "$0")/../results/chain-2026-11-01/urtm11-7.desc.json" "$OUT" || exit 1
# URTM(10,7): from (11,7), tags and symbol merging found together (lean/URTM/CTSH10_7.lean). Built after (11,7).
python3 "$(dirname "$0")/gen_child_desc.py" "$(dirname "$0")/../results/joint-2026-11-02/urtm10-7.desc.json" "$OUT" || exit 1
# URTM(9,8): from (10,7), in the same way (lean/URTM/CTSH9_8.lean). Built after (10,7).
python3 "$(dirname "$0")/gen_child_desc.py" "$(dirname "$0")/../results/joint-2026-11-04/urtm9-8n.desc.json" "$OUT" || exit 1
