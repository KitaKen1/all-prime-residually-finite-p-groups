#!/usr/bin/env bash
set -euo pipefail
mkdir -p ../build-receipt
set +e
timeout --kill-after=120 300m python3 comparator/build-proof.py 2>&1 | tee ../build-receipt/build.log
APG_PIPE=("${PIPESTATUS[@]}")
set -e
test "${APG_PIPE[1]}" -eq 0
if [[ "${APG_PIPE[0]}" -eq 0 ]]; then
  printf 'ready=true\n' >> "$GITHUB_OUTPUT"
  printf 'PASS\n' > ../build-receipt/status.txt
elif [[ "${APG_PIPE[0]}" -eq 124 || "${APG_PIPE[0]}" -eq 137 ]]; then
  printf 'ready=false\n' >> "$GITHUB_OUTPUT"
  printf 'INCOMPLETE: rerun the same commit to resume its cached Lake traces\n' > ../build-receipt/status.txt
else
  printf 'FAIL: exit=%s\n' "${APG_PIPE[0]}" > ../build-receipt/status.txt
  exit "${APG_PIPE[0]}"
fi
