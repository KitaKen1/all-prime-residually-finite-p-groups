#!/usr/bin/env python3
"""Check the FC proposal's main and both variants against their proved solutions.

This checks the expanded type with the proof project's Lean, not the FC utility
frontend. The proposal placeholder is replaced with the actual proved theorem
in a temporary check module; that module must pass warnings-as-errors and audit.
"""
import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import subprocess
import sys

from axiom_audit import audit_axioms
from build_env import ROOT, LEAN, ENV, OUT, TOOLCHAIN
from reproduce import inventory, sha256, resolved_dependencies

sys.path.insert(0, str(ROOT.parent / 'scripts'))
from fc_proposal import check_proposal, PROOF_URL


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--reproduction', help='completed full-project reproduction run name')
    args = parser.parse_args()
    statements = check_proposal(ROOT.parent)
    proposal = ROOT.parent / 'FClikelean/AllPrimeGroups.lean'
    hashes = {'proposal_sha256': sha256(proposal), 'challenge_sha256': sha256(ROOT / 'Challenge.lean'),
              'solution_sha256': sha256(ROOT / 'FCSolution.lean')}
    env = ENV.copy()
    out = OUT
    if args.reproduction:
        if Path(args.reproduction).name != args.reproduction:
            parser.error('The reproduction name must be a single path component.')
        state = json.loads((ROOT / 'reports/reproduce' / args.reproduction / 'state.json').read_text())
        if not (state.get('status') == 'passed' and state.get('complete')
                and state.get('closure_complete') and state.get('main_checked')):
            raise SystemExit('A completed full reproduction is required.')
        if {m: sha256(p) for m, p in inventory().items()} != state['context']['sources']:
            raise SystemExit('The reproduction core sources differ.')
        out = Path(state['output'])
        env['LEAN_PATH'] = state['lean_path']
    connection = json.loads((ROOT.parent / 'verification/fc-connection.json').read_text())
    if connection.get('status') != 'passed':
        raise SystemExit('Run check_fc.py first.')
    for module in ['Challenge', 'FCSolution', 'FCAudit']:
        record = connection['modules'][module]
        if (record['source_sha256'] != sha256(ROOT / (module + '.lean'))
                or record['olean_sha256'] != sha256(out / (module + '.olean'))):
            raise SystemExit(f'The checked connection artifact differs: {module}')
    names = [f'AllPrimeGroupsFCProposalCheck.{name}' for name in statements]
    source = ('import FCSolution\n\nnamespace AllPrimeGroupsFCProposalCheck\n\n' +
              ''.join(f'theorem {name} :\n{statement}\n :=\n'
                      f'  AllPrimeGroupsFC.{name}\n\n'
                      f'#print axioms AllPrimeGroupsFCProposalCheck.{name}\n\n'
                      for name, statement in statements.items()) +
              'end AllPrimeGroupsFCProposalCheck\n')
    folder = ROOT / '.lake/fc-proposal-check'
    folder.mkdir(parents=True, exist_ok=True)
    path = folder / 'FCProposalStatementCheck.lean'
    path.write_text(source)
    import os
    allowed = [Path(p).resolve() for p in env['LEAN_PATH'].split(os.pathsep)]
    allowed.append(Path(subprocess.check_output([str(LEAN), '--print-libdir'], env=env,
                                               text=True).strip()).resolve())
    resolved_dependencies(path, env, ROOT, allowed, out.resolve(), ['FCSolution'])
    run = subprocess.run([str(LEAN), '-j1', '-DautoImplicit=false', '-DwarningAsError=true',
                          str(path)], cwd=ROOT, env=env, text=True,
                         stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if run.returncode:
        raise SystemExit(run.stdout)
    audited = audit_axioms(source, run.stdout, names)
    if hashes != {'proposal_sha256': sha256(proposal), 'challenge_sha256': sha256(ROOT / 'Challenge.lean'),
                  'solution_sha256': sha256(ROOT / 'FCSolution.lean')}:
        raise SystemExit('A proposal or connection source changed during checking.')
    verification = ROOT.parent / 'verification'
    (verification / 'fc-proposal.log').write_text(run.stdout)
    result = {'status': 'statement_checked', 'checked_at_utc': datetime.now(timezone.utc).isoformat(),
              **hashes, 'proof_url': PROOF_URL, 'proof_url_is_commit_pinned': False,
              'toolchain': TOOLCHAIN, 'generated_check_source': source,
              'generated_check_sha256': hashlib.sha256(source.encode()).hexdigest(),
              'log_sha256': hashlib.sha256(run.stdout.encode()).hexdigest(), 'axioms': audited,
              'checked_theorems': list(statements),
              'proposal_has_statement_placeholder': True, 'fc_environment_compile_run': False,
              'fc_environment_lint_run': False,
              'verification_scope': ('Expanded main and both variants checked against their proved solutions '
                                     'using checked proof-project artifacts; FC frontend not compiled.')}
    (verification / 'fc-proposal.json').write_text(json.dumps(result, indent=2) + '\n')
    print('PASS: FC main and both variants match their independent references and proved solutions.')


if __name__ == '__main__':
    main()
