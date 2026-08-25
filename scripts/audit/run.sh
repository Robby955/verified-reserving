#!/bin/sh
# One-command reproduction: download the six CSVs (if absent), run the self-test
# against Mack (1993) and the RAA case study, audit every triangle, write
# certificates/, summary.json, tables.tex, aggregate_tables.md, AUDIT_RESULTS.md.
set -eu
HERE=$(cd "$(dirname "$0")" && pwd)
sh "$HERE/download.sh"
python3 "$HERE/audit.py"
