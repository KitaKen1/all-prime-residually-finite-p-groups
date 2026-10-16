#!/usr/bin/env python3
"""Reject missing audits or any axiom outside the foundational allowlist."""
import json,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT/'lean/scripts'))
from axiom_audit import audit_axioms,MAIN_THEOREM
kind,log,output=sys.argv[1:]
if kind=='core':source=ROOT/'lean/Audit.lean';expected=494;required=[MAIN_THEOREM]
elif kind=='fc':
    source=ROOT/'lean/FCAudit.lean';expected=5
    required=json.loads((ROOT/'lean/comparator/pins.json').read_text())['targets']
else:raise SystemExit('Unknown audit kind')
audited=audit_axioms(source.read_text(),Path(log).read_text(),required)
if len(audited)!=expected:raise SystemExit('Missing axiom audits')
Path(output).write_text(json.dumps({'status':'PASS','audited_targets':len(audited),'sorryAx':False,'new_axioms':False,'axioms':audited},indent=2)+'\n')
print('PASS:',len(audited),'exact axiom audits; no sorryAx or extra axioms.')
