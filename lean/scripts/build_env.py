"""Resolve the checked-in Lean toolchain and this project's pinned dependency artifacts."""
import os
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TOOLCHAIN = (ROOT / 'lean-toolchain').read_text().strip()
LEAN = Path(os.environ.get('ELAN_HOME', str(Path.home() / '.elan'))) / 'toolchains' / \
    TOOLCHAIN.replace('/', '--').replace(':', '---') / 'bin/lean'
if not LEAN.exists():
    raise SystemExit(f'Install the pinned toolchain first: elan toolchain install {TOOLCHAIN}')
OUT = ROOT / '.lake/build/lib/lean'
ENV = os.environ.copy()
ENV['LEAN_PATH'] = os.pathsep.join([str(OUT)] + [
    str(p / '.lake/build/lib/lean') for p in (ROOT / '.lake/packages').iterdir()
    if (p / '.lake/build/lib/lean').exists()])
ENV['LEAN_NUM_THREADS'] = '1'
