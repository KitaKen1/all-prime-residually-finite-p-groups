# Comparator and fresh kernel replay

The [workflow](../../.github/workflows/comparator.yml) follows the successful
Entropic Rogers–Shephard layout: build, independently prepared Comparator job,
and a separate fresh Lean kernel replay. A final job requires all three to pass.
The three mathematical targets are listed in [TARGET-CORRESPONDENCE.md](TARGET-CORRESPONDENCE.md).

The proof uses Lean 4.34.1 and its locked Mathlib revision. Comparator and
Lean4export are fixed to their upstream 4.34.0 revisions in [pins.json](pins.json).
Only their `lean-toolchain` declarations are changed to 4.34.1; their Lean source
code is unchanged. Landrun is pinned as well. The workflow uses actual Linux
sandboxing under an unprivileged account, with the reference workflow's systemd
restrictions. The two replay checks use Lean's kernel; Nanoda is not configured.

The build checks all 200 core sources, the three reference/connection/audit
sources, and the independent Comparator challenge: 204 sources. Modules are
built sequentially to limit peak memory, and same-commit caches allow a timed-out
build to resume. Incomplete builds cannot pass the final verification job.
The Comparator job first compiles its Mathlib-only challenge before restoring
the solution cache, compares all three target theorems, requires its builtin
kernel replay, and checks 494 core plus five connection axiom audits.
The replay job runs `lake env leanchecker --fresh FCSolution` separately.

Reports are retained for 90 days. Archive original artifact ZIPs, complete job
logs, API metadata and SHA-256 hashes with `archive-run.py`; it checks the exact
run attempt, tested commit, three targets, tool versions, audits and replay.
Private CI results establish private test status; a later public run needs its
own record. No successful CI run is claimed until its receipts are saved.

The workflow and tool scripts were adapted from
[KitaKen1/entropic-rogers-shephard](https://github.com/KitaKen1/entropic-rogers-shephard/tree/8f34cf8cde22aeca2ac0ae3300592548e212a6b3/lean/comparator).
