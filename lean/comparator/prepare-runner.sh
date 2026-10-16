#!/usr/bin/env bash
set -euo pipefail
test "${GITHUB_ACTIONS:-}" = true
test "${RUNNER_ENVIRONMENT:-}" = github-hosted
test "${RUNNER_OS:-}" = Linux
# Only the disposable GitHub-hosted runner is cleaned. Lean and the project are untouched.
sudo rm -rf /usr/share/dotnet /usr/local/lib/android /opt/ghc /usr/local/.ghcup \
  /opt/hostedtoolcache /usr/share/swift /usr/local/share/powershell /usr/lib/jvm \
  /usr/local/share/boost /opt/microsoft /opt/google /opt/az /usr/local/share/chromium
sudo docker system prune -af > /dev/null 2>&1 || true
sudo apt-get update -qq
sudo apt-get install -y -q time > /dev/null
curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -o "$RUNNER_TEMP/elan-init.sh"
sh "$RUNNER_TEMP/elan-init.sh" -y --default-toolchain none > /dev/null
echo "$HOME/.elan/bin" >> "$GITHUB_PATH"
{ nproc; free -h; df -h / /mnt 2>/dev/null || true; } | tee "$RUNNER_TEMP/runner.txt"
