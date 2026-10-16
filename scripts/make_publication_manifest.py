#!/usr/bin/env python3
"""Refresh the publication inventory after reviewing changes and rerunning checks."""
from datetime import datetime, timezone
import json
from pathlib import Path

from check_publication import ROOT, MANIFEST, inventory, check_evidence, check_links
from ci_receipt import check_private_ci, check_public_ci


def main():
    evidence = check_evidence(ROOT)
    private_ci = check_private_ci(ROOT)
    if private_ci is not None:
        evidence["private_ci"] = private_ci
    public_ci = check_public_ci(ROOT)
    if public_ci is not None:
        evidence["public_ci"] = public_ci
    ci_passed = private_ci is not None or public_ci is not None
    check_links(ROOT, allow_missing_manifest=True)
    baseline = json.loads((ROOT / 'verification/baseline-full-build.json').read_text())
    current = {p.relative_to(ROOT / 'lean').with_suffix('').as_posix().replace('/', '.'):
               __import__('hashlib').sha256(p.read_bytes()).hexdigest()
               for p in [*(ROOT / 'lean/AllPrimeGroups').glob('*.lean'),
                         *(ROOT / 'lean/OAI').rglob('*.lean'),
                         *[ROOT / 'lean' / n for n in
                           ['AllPrimeGroups.lean', 'Audit.lean', 'UpstreamAudit.lean']]]}
    old = baseline['context']['sources']
    result = {'schema_version': 1, 'prepared_at_utc': datetime.now(timezone.utc).isoformat(),
              'title': 'Infinite finitely presented residually finite p-groups for every prime',
              'intended_repository': 'https://github.com/KitaKen1/all-prime-residually-finite-p-groups',
              'toolchain': (ROOT / 'lean/lean-toolchain').read_text().strip(),
              'evidence': evidence,
              'baseline_comparison': {
                  'baseline_sources': len(old), 'current_core_sources': len(current),
                  'unchanged_sources': sum(current.get(m) == h for m, h in old.items()),
                  'changed_sources': sorted(m for m in old if m in current and old[m] != current[m]),
                  'added_sources': sorted(set(current) - set(old))},
              'verification_limits': {
                  'latest_200_source_full_build_recorded': ci_passed,
                  'github_actions_run': ci_passed, 'lean_comparator_run': ci_passed,
                  'separate_fresh_lean_kernel_replay_run': ci_passed,
                  'external_kernel_run': False, 'public_ci_run': public_ci is not None,
                  'fc_proposal_frontend_compile_run': False,
                  'producer_records_are_not_recipient_builds': True},
              'files': inventory(ROOT)}
    (ROOT / MANIFEST).write_text(json.dumps(result, ensure_ascii=False, indent=2) + '\n')
    print(f'Wrote {MANIFEST}: {len(result["files"])} files.')


if __name__ == '__main__':
    main()
