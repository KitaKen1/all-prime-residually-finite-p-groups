# AllPrimeGroups Lean project

The public entry point is the [repository README](../README.md).
The core consists of 134 local modules, 63 unchanged upstream modules, a root
import and two audits (200 Lean sources). Three additional files provide the
independent reference statement and proof connections.

- [Main existence theorem](AllPrimeGroups/PrimeCharacterExtensions.lean)
- [The specified concrete groups](AllPrimeGroups/PrimeGroups.lean)
- [Independent reference](Challenge.lean) and [proof connection](FCSolution.lean)
- [Core audit](Audit.lean) and [connection audit](FCAudit.lean)
- [Mathematical proof map](../docs/PROOF-MAP.md)
- [Reproduction guide](../docs/VERIFICATION.md)
- [Manuscript correspondence](manuscript-correspondence.html)
- [Provenance and licenses](upstream/)

From the repository root, run `python3 scripts/check_publication.py` for source
integrity. For proof verification with locked dependencies, follow the
reproduction guide. Producer `.olean` artifacts and package caches are excluded.

The original manuscript generator sources are under `manuscript/`. They are
included for the 41-claim correspondence inventory; reproducing the original
PDF uses ReportLab and macOS fonts. Lean proof verification needs neither.

The producer recorded 494 core axiom audits and a complete fresh-output build
of the earlier 195-source baseline. The latest core has 200 sources; its full
fresh-output build and GitHub CI execution have not been recorded. See the
[verification records](../verification/README.md) for the exact scopes.
