#!/usr/bin/env bash
# 記述ファイルから Lean モジュールを一括生成し、ライブラリのルートも書き直す。
# 表を手で写さないための唯一の入口。CI もローカルもこれを使う。
set -euo pipefail
declare -A MODS=(
  [10-8]=M10_8 [13-7]=M13_7 [15-6]=M15_6 [17-5]=M17_5
  [24-4]=M24_4 [32-3]=M32_3 [138-2]=M138_2 [4-168]=M4_168
)
mods=()
for k in "${!MODS[@]}"; do
  python3 tools/gen_lean.py "data/urtm/urtm$k.txt" --module "${MODS[$k]}" > "lean/URTM/${MODS[$k]}.lean"
  mods+=("${MODS[$k]}")
done
# 定理 A（lean/URTM/KState.lean）を Morita の 6 台に適用するモジュール（tools/gen_kstate_lean.py）。
# 仮定の decide と、Lean の conv と kstate.py の生成表の一致（decide +kernel）を含む。
mkdir -p lean/URTM/Gen
kmods=()
for k in 10-8 13-7 15-6 17-5 24-4 32-3; do
  km="K${k/-/_}"
  python3 tools/gen_kstate_lean.py "data/urtm/urtm$k.txt" --module "$km" > "lean/URTM/Gen/$km.lean"
  kmods+=("Gen.$km")
done
# 定理 A の疎版（lean/URTM/KStateSparse.lean、tools/kstate_sparse_k4.py）: (13,7) → URTM(4,79)
python3 tools/gen_kstate_lean.py data/urtm/urtm13-7.txt --module KS13_7 --sparse K13_7 > lean/URTM/Gen/KS13_7.lean
kmods+=("Gen.KS13_7")
# ε 逆向きの 4 状態化（lean/URTM/KStateEps.lean、tools/kstate5.py の解 results/kstate5/*.json、docs/20）:
# (10,8) → URTM(4,48)
python3 tools/gen_eps_lean.py data/urtm/urtm10-8.txt results/kstate5/urtm10-8.k4.eps-.json --module KE10_8 --base K10_8 > lean/URTM/Gen/KE10_8.lean
kmods+=("Gen.KE10_8")
# ブロック分け × 役割の併合 × ε（lean/URTM/KStateBlocks.lean、tools/kstate_blocks.py の解 results/kstate_blocks/records/*.json、docs/22）:
# (10,8) → (4,46)・(4,48)（1 ブロックずつ、ε 逆向きの 4 状態化と同じ表）・(6,39)、(15,6) → (5,45)・(7,32)・(11,22)、(17,5) → (8,30)、(32,3) → (12,21)
for spec in 4-46:K10_8 4-48:K10_8 6-39:K10_8 5-45:K15_6 7-32:K15_6 11-22:K15_6 8-30:K17_5 12-21:K32_3; do
  n=${spec%%:*}; km="KB${n/-/_}"
  python3 tools/gen_blocks_lean.py "results/kstate_blocks/records/urtm$n.json" --module "$km" --base "${spec##*:}" > "lean/URTM/Gen/$km.lean"
  kmods+=("Gen.$km")
done
# 1 ブロック 3 状態の変換の疎版（lean/URTM/KStatePure.lean、tools/kstate_sparse_pure.py）:
# (10,8) → URTM(6,45)、(15,6) → URTM(9,37)。out/ の記述ファイルも書き、元機械との突き合わせが崩れたら止まる
mkdir -p out
python3 tools/kstate_sparse_pure.py data/urtm/urtm10-8.txt 1 1 out/urtm6-45.txt --lean lean/URTM/Gen/PS10_8.lean --module PS10_8 --base K10_8 > /dev/null
python3 tools/kstate_sparse_pure.py data/urtm/urtm15-6.txt 2 1 out/urtm9-37.txt --lean lean/URTM/Gen/PS15_6.lean --module PS15_6 --base K15_6 > /dev/null
kmods+=("Gen.PS10_8" "Gen.PS15_6")
# 定理 B（ブロック化、lean/URTM/KStateB.lean）: (17,5) を blocks (2,1)→(7,65)、(2,2)→(8,50)
for b in 2,1 2,2; do
  km="K17_5_b${b/,/}"
  python3 tools/gen_kstate_lean.py data/urtm/urtm17-5.txt --module "$km" --blocks "$b" > "lean/URTM/Gen/$km.lean"
  kmods+=("Gen.$km")
done
# CTSH の模倣（lean/URTM/CTSH10_8.lean、一般証明）の具体例: 記述ファイルの試験例を CTSH に読み戻して照合
python3 tools/gen_ctsh_lean.py data/urtm/urtm10-8.txt --module C10_8 > lean/URTM/Gen/C10_8.lean
kmods+=("Gen.C10_8")
# 同じく URTM(17,5)（lean/URTM/CTSH17_5.lean・CTSH17_5Main.lean）の具体例
python3 tools/gen_ctsh_lean.py data/urtm/urtm17-5.txt --module C17_5 --machine 17_5 > lean/URTM/Gen/C17_5.lean
kmods+=("Gen.C17_5")
# 同じく URTM(13,7)（lean/URTM/CTSH13_7.lean・CTSH13_7Main.lean）の具体例
python3 tools/gen_ctsh_lean.py data/urtm/urtm13-7.txt --module C13_7 --machine 13_7 > lean/URTM/Gen/C13_7.lean
kmods+=("Gen.C13_7")
# 同じく URTM(15,6)（lean/URTM/CTSH15_6.lean・CTSH15_6Main.lean）の具体例
python3 tools/gen_ctsh_lean.py data/urtm/urtm15-6.txt --module C15_6 --machine 15_6 > lean/URTM/Gen/C15_6.lean
kmods+=("Gen.C15_6")
# 同じく URTM(24,4)（lean/URTM/CTSH24_4.lean・CTSH24_4Main.lean）の具体例
python3 tools/gen_ctsh_lean.py data/urtm/urtm24-4.txt --module C24_4 --machine 24_4 > lean/URTM/Gen/C24_4.lean
kmods+=("Gen.C24_4")
# 同じく URTM(32,3)（lean/URTM/CTSH32_3.lean・CTSH32_3Main.lean）の具体例
python3 tools/gen_ctsh_lean.py data/urtm/urtm32-3.txt --module C32_3 --machine 32_3 > lean/URTM/Gen/C32_3.lean
kmods+=("Gen.C32_3")
# URTM(4,168)（Theorem 5.5 で U10_8 から変換、lean/URTM/Conv55.lean・CTSH4_168Main.lean）:
# 記述ファイルの表を構造化した記号で書き出し（F4_168）、試験例を照合する（C4_168）
python3 tools/gen_conv_lean.py table data/urtm/urtm4-168.txt data/urtm/urtm10-8.txt > lean/URTM/Gen/F4_168.lean
python3 tools/gen_conv_lean.py example data/urtm/urtm4-168.txt data/urtm/urtm10-8.txt > lean/URTM/Gen/C4_168.lean
kmods+=("Gen.F4_168" "Gen.C4_168")
# URTM(138,2)（Theorem 5.4 の 2 ビット版で U24_4 から変換、lean/URTM/Conv54.lean・CTSH138_2Main.lean）
python3 tools/gen_conv_lean.py table2 data/urtm/urtm138-2.txt data/urtm/urtm24-4.txt > lean/URTM/Gen/F138_2.lean
python3 tools/gen_conv_lean.py example2 data/urtm/urtm138-2.txt data/urtm/urtm24-4.txt > lean/URTM/Gen/C138_2.lean
kmods+=("Gen.F138_2" "Gen.C138_2")
# URTM(3,36654)（Lemma 5.9 → Lemma 5.10 で U32_3 から変換、lean/URTM/Conv59.lean・Conv510.lean・CTSH3_36654Main/Thm.lean）:
# 3.8 万本の表（F3_36654）、塊ごとの照合（V3_36654）、試験例（C3_36654）
D3=data/urtm/urtm3-36654_Be_careful.txt
python3 tools/gen_conv_lean.py table3 "$D3" data/urtm/urtm32-3.txt > lean/URTM/Gen/F3_36654.lean
python3 tools/gen_conv_lean.py verify3 "$D3" data/urtm/urtm32-3.txt > lean/URTM/Gen/V3_36654.lean
python3 tools/gen_conv_lean.py example3 "$D3" data/urtm/urtm32-3.txt > lean/URTM/Gen/C3_36654.lean
kmods+=("Gen.F3_36654" "Gen.V3_36654" "Gen.C3_36654")
# 同じく試験例 3 件の停止までのステップ数（lean/URTM/CTSH3_36654Steps.lean、docs/10 §8.6）: S3_36654Z・S3_36654P*・S3_36654。
# 区間の検査がカーネルで約 21 分（CPU）かかるので URTM.lean には入れない。`lake build URTMSteps` で建てる（lakefile.toml）
python3 tools/gen_steps36654_lean.py "$D3" data/urtm/urtm32-3.txt lean/URTM/Gen
# 同じステップ数を、表 T3（T†）を回さずに Lemma 5.9・5.10 の歩数の式と (32,3) の実行・T̂ の実行から（lean/URTM/CTSH3_36654Cost.lean、
# docs/10 §8.7）: W3_36654Z・W3_36654P*・W3_36654・W3_36654Same。URTMSteps に入れる（区間の検査がカーネルで約 5 分）
python3 tools/gen_cost36654_lean.py "$D3" data/urtm/urtm32-3.txt lean/URTM/Gen
# URTM(3,600)（改良版の 3 状態化の反転版で U32_3 から変換、lean/URTM/Conv1W.lean・Conv3P.lean・Conv3S.lean・
# CTSH3_600Main.lean、docs/09）: tools/threestate.py の表と Lean の変換の一致、仮定の有限検査
python3 tools/gen_threestate_lean.py data/urtm/urtm32-3.txt --module T3_600 --base K32_3 > lean/URTM/Gen/T3_600.lean
kmods+=("Gen.T3_600")
# 論文の表の途中の値（lean-univ/LeanUniv/FinalValues.lean）: 反転しない 3 状態化 (3,659) の表と仮定、
# Morita の 1WU 機械 T̂ に計数の刈り込みを当てたときの番号付けと need（1820）
python3 tools/gen_threestate_lean.py data/urtm/urtm32-3.txt --module T3_659 --base K32_3 --no-mirror > lean/URTM/Gen/T3_659.lean
python3 tools/gen_pair3_lean.py data/urtm/urtm32-3.txt --module P3_1820 > lean/URTM/Gen/P3_1820.lean
kmods+=("Gen.T3_659" "Gen.P3_1820")
# 記号削減（Thm 5.4 の改良＋状態の併合、lean/URTM/FewSym.lean・CTSH94_2Main.lean・CTSH92_2Main.lean、docs/23）:
# (24,4) → URTM(94,2)、(13,7) → URTM(92,2)。tools/fewsym_merge.py の表をそのまま写し、規則ごとの検査を decide
python3 tools/gen_fewsym_lean.py results/fewsym/records/urtm24-4.2.merge.json --module FS94_2 --base K24_4 > lean/URTM/Gen/FS94_2.lean
python3 tools/gen_fewsym_lean.py results/fewsym/records/urtm13-7.2.merge.json --module FS92_2 --base K13_7 > lean/URTM/Gen/FS92_2.lean
kmods+=("Gen.FS94_2" "Gen.FS92_2")
# 同じ記録の併合前の表（135 状態）と、併合後の表 FS92_2 がその像であること（lean-univ/LeanUniv/FinalValues.lean）
python3 tools/gen_fewsym_lean.py results/fewsym/records/urtm13-7.2.merge.json --module FS135_2 --base K13_7 \
  --unmerged --merged-module FS92_2 > lean/URTM/Gen/FS135_2.lean
kmods+=("Gen.FS135_2")
# autoresearch（枝 autoresearch/frontier）が見つけた記録（autoresearch/frontier/search_lib/records/）:
# ブロック族 (10,8) → (6,37)、(17,5) → (8,28)、(15,6) → (9,27)、記号削減 (13,7) → (85,2)
AR=autoresearch/frontier/search_lib/records
for spec in 10-8.6-37:KB6_37:K10_8 17-5.8-28:KB8_28:K17_5 15-6.9-27:KB9_27:K15_6; do
  IFS=: read -r rec km base <<< "$spec"
  python3 tools/gen_blocks_lean.py "$AR/kb_urtm$rec.json" --module "$km" --base "$base" > "lean/URTM/Gen/$km.lean"
  kmods+=("Gen.$km")
done
python3 tools/gen_fewsym_lean.py "$AR/urtm13-7.85.merge.json" --module FS85_2 --base K13_7 > lean/URTM/Gen/FS85_2.lean
kmods+=("Gen.FS85_2")
# 他の 5 台の記号削減の記録（2 記号化の LNS、docs/32 §3）: (10,8)・(24,4) → (92,2)、(15,6) → (108,2)、(17,5)・(32,3) → (115,2)。
# CTSH の模倣は CTSH<m>_2_<元>Main.lean、Def. 7.1 の万能性は lean-univ の U<m>_2_<元>.lean（共通部分は FewSymGen.lean）
for spec in 10-8.92:FS92_2_10_8:K10_8 24-4.92:FS92_2_24_4:K24_4 15-6.108:FS108_2_15_6:K15_6 \
    17-5.115:FS115_2_17_5:K17_5 32-3.115:FS115_2_32_3:K32_3; do
  IFS=: read -r rec km base <<< "$spec"
  python3 tools/gen_fewsym_lean.py "results/fewsym/records/urtm$rec.merge.json" --module "$km" --base "$base" > "lean/URTM/Gen/$km.lean"
  kmods+=("Gen.$km")
done
# 記号の併合（results/symmerge-2026-10-05、tools/gen_symmerge_lean.py）: 記録のブロック化の表の生成モジュール。
# CTSH<k>_<m>Main と URTM.SymMergeAll は同じ道具が書く追跡ファイル（lean-univ/tests/check.sh (2c) が照合する）
smods=$(python3 tools/gen_symmerge_lean.py kb)
for km in $smods; do kmods+=("Gen.$km"); done
printf 'import URTM.Basic\n' > lean/URTM.lean
echo 'Generated machine tables and trace certificates.'
