# Verification records

These records cover local checks and separate public and private GitHub-hosted Linux runs.
They do not replace a new build on the recipient's machine.

| Record | What it establishes |
|---|---|
| [public-ci-verification.json](public-ci-verification.json), [archive](public-ci-38865696145-attempt1/) | Successful public Linux 204-module build, three-target Comparator with builtin kernel replay, 494 core and five connection axiom audits, and separate fresh Lean kernel replay. Original ZIP hashes match API digests. |
| [private-ci-verification.json](private-ci-verification.json), [archive](private-ci-38856485805-attempt1/) | Successful private Linux 204-module build, three-target Comparator with builtin kernel replay, 494 core and five connection axiom audits, and separate fresh Lean kernel replay. Original ZIP hashes match API digests; this earlier private test is preserved separately. |
| [publication-preparation.json](publication-preparation.json) | Source-copy identity checks, three connection modules, regression tests and workflow/citation YAML syntax checks. |
| [baseline-full-build.json](baseline-full-build.json) | A successful 195-source baseline fresh-output build on the same macOS host. Contains source, artifact and log hashes, completion flags and 446 core theorem audits. Absolute machine paths were omitted from this public summary; the original state hash is retained. |
| [core local checks](../lean/reports/local-checks.json) | Compilation source/artifact/log hashes for all 134 current local modules, the root import and Audit. |
| [core axiom map](../lean/reports/local-axioms.json), [audit log](../lean/reports/Audit.log) | The exact 494 requested declarations use only the standard three axioms or a subset. |
| [portable-check.json](portable-check.json) | A five-module fresh-output check from an extracted development archive, including 20 generic nil-unit audits and 23 regression tests. The archive is identified by hash; it is not this publication package. |
| [fc-connection.json](fc-connection.json), [log](fc-connection.log) | Compilation and audits for main `finitely_presented_burnside_problem`, variant 1 `variants.finitely_presented_burnside_problem_residually_finite`, variant 2 `variants.finitely_presented_burnside_problem_all_primes`, its existing descriptive name, and the concrete groups. The record states whether existing artifacts or a completed fresh reproduction were used. |
| [fc-proposal.json](fc-proposal.json), [log](fc-proposal.log) | All three expanded FC statements, `finitely_presented_burnside_problem`, `variants.finitely_presented_burnside_problem_residually_finite` and `variants.finitely_presented_burnside_problem_all_primes`, are checked separately against Challenge and proved by their existing solutions. This checks their types with the proof project's Lean; FC utility compilation and linting have not been run. |
| [manuscript correspondence](../lean/reports/manuscript-correspondence.json) | Complete 41-claim inventory and references to 68 audited declarations. Mathematical classifications are manual. |
| [PUBLICATION-MANIFEST.json](../PUBLICATION-MANIFEST.json) | Inventory and SHA-256 hashes of this publication, including the unchanged PDF and timestamp file. |

The core has 200 Lean sources. `Challenge`, `FCSolution` and `FCAudit` add
three files, and `ComparatorChallenge` adds one: 204 sources in CI.
`FClikelean` adds one separate proposed FC problem file with three
theorems: main `finitely_presented_burnside_problem`, the residually finite periodic
variant `variants.finitely_presented_burnside_problem_residually_finite`, and the all-prime
variant `variants.finitely_presented_burnside_problem_all_primes`.
Each has classification attributes, a formal-proof reference and a statement
placeholder; the proposal is outside the audited proof closure.
No project artifacts or dependency caches are distributed.

The finished baseline build checked 195 sources on 2026-10-15, with pinned
toolchain and package caches. The later five added local modules and updated
root import/audit were checked incrementally; they have not been represented
as a successful single macOS full build of all 200 current core sources.

The later [private Linux CI](https://github.com/KitaKen1/ci-test-sandbox/actions/runs/38856485805) builds all 204 current project sources,
including the independent Comparator challenge. It passed all three Comparator
targets, 499 axiom audits and a separate fresh Lean kernel replay. The older
macOS producer records above retain their original scope. The later [public main run](https://github.com/KitaKen1/all-prime-residually-finite-p-groups/actions/runs/38865696145) independently passed the same complete pipeline; its receipts are archived above.
