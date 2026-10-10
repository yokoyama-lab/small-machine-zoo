#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
bash tools/fetch_data.sh
bash tools/gen_all_lean.sh
for project in lean-univ legacy/small-urtm/lean-meta; do
  (cd "$project" && lake exe cache get)
done
