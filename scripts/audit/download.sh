#!/bin/sh
# Download the six CAS Schedule P loss reserving CSVs (Meyers and Shi) into data/.
# The landing page moved in 2026; the files are still served from /sites/default/files/2021-04/.
# Landing page (current): https://www.casact.org/publications-research/research/research-resources/loss-reserving-data-pulled-naic-schedule-p
# Landing page (as cited in the literature, now 404): https://www.casact.org/research-resources/research/loss-reserving-data
set -eu
HERE=$(cd "$(dirname "$0")" && pwd)
mkdir -p "$HERE/data"
BASE="https://www.casact.org/sites/default/files/2021-04"
for line in ppauto wkcomp comauto medmal prodliab othliab; do
  f="${line}_pos.csv"
  if [ ! -s "$HERE/data/$f" ]; then
    curl -fsSL -o "$HERE/data/$f" "$BASE/$f"
    echo "downloaded $f"
  else
    echo "have $f"
  fi
done
(cd "$HERE/data" && shasum -a 256 ppauto_pos.csv wkcomp_pos.csv comauto_pos.csv medmal_pos.csv prodliab_pos.csv othliab_pos.csv > SHA256SUMS)
cat "$HERE/data/SHA256SUMS"
