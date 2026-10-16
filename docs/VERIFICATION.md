# Verification guide

The publication uses Lean `leanprover/lean4:v4.34.1` and Mathlib commit
`d13f23b723b8a846827a245b89c10fc7d3f11612`. All nine Lake dependency revisions
are fixed in [lake-manifest.json](../lean/lake-manifest.json).
The scripts require Linux or macOS, Python 3.10 or later, Git and elan.

## 1. Inspect the source package

From the repository root:

```sh
python3 scripts/check_publication.py
python3 -m unittest discover -s scripts -p 'test_*.py'
```

This needs neither Lean nor a network connection. It checks the exact publication
inventory and SHA-256 hashes, the 63 unchanged vendored sources, the recorded
494-declaration audit, source hashes in the producer compilation records,
the independent references, all three FC proposal statements and their local Lean checks,
and local Markdown links.
It does not compile Lean or turn producer records into a recipient proof check.

## 2. Prepare locked dependencies

```sh
cd lean
elan toolchain install leanprover/lean4:v4.34.1
lake exe cache get
```

Use the checked-in lock file. A dependency update changes the verification inputs.
The Lean installation and package artifacts, including Mathlib, are reused;
the project sources themselves are rebuilt below.

## 3. Full fresh-output reproduction

```sh
python3 scripts/test_verification.py
python3 scripts/test_release.py
python3 scripts/reproduce.py --name full-publication
python3 scripts/check_fc.py --reproduction full-publication
python3 scripts/check_fc_proposal.py --reproduction full-publication
```

The first build covers **200 core sources**: 134 local modules, 63 unchanged
OpenAI modules, the root import, `Audit.lean` and `UpstreamAudit.lean`.
The second command builds **three additional files**: `Challenge.lean`,
`FCSolution.lean` and `FCAudit.lean`. `FClikelean` is a separate FC problem file
with main (`finitely_presented_burnside_problem`), variant 1
(`variants.finitely_presented_burnside_problem_residually_finite`) and variant 2
(`variants.finitely_presented_burnside_problem_all_primes`). Variant 1 states
residually finite periodic-group existence without a prime parameter; variant 2
is the all-prime residually finite p-group result. All three carry classification
attributes, a proof reference and the customary `by sorry` statement placeholder.
The proposal is excluded from the proof's compilation and axiom audits.
`check_fc_proposal.py` extracts all three expanded statements and proves them separately
with their existing solutions in a temporary check module, with warnings treated as errors.
It does not compile `FormalConjecturesUtil` or run the FC linters.

`reproduce.py` copies core sources into `.lake/reproduce/full-publication/sources`
and emits new project artifacts in that run's `lib` directory. Lean's `--deps`
checks the actual resolved paths against this output and the pinned package
caches. The old `.lake/build/lib/lean` is excluded. The script checks package
commits and tracked-source cleanliness, source provenance, input hashes,
dependency/artifact/log hashes and the exact requested audit declarations.

A full core success requires all of the following in
`reports/reproduce/full-publication/state.json`:

```json
{
  "status": "passed",
  "complete": true,
  "closure_complete": true,
  "main_checked": true
}
```

The subsequent connection check requires those flags and unchanged core source
hashes, resolves its imports against the same fresh output, then audits
`AllPrimeGroupsFC.finitely_presented_burnside_problem`,
`AllPrimeGroupsFC.variants.finitely_presented_burnside_problem_residually_finite`,
`AllPrimeGroupsFC.variants.finitely_presented_burnside_problem_all_primes`, the existing descriptive
name `AllPrimeGroupsFC.all_prime_groups`, and `AllPrimeGroupsFC.concrete_groups`.
Its report is written to `verification/fc-connection.json` at the repository root.
The three-statement proposal check follows that connection check and writes
`verification/fc-proposal.json` and its axiom log. It requires matching source
and artifact hashes for the checked reference/connection files.

The historical baseline took about 105 minutes on the producer's machine.
Other machines and load conditions may take several hours. Run sequentially;
many upstream sources import all of Mathlib.

If interrupted, keep the inputs unchanged and resume:

```sh
python3 scripts/reproduce.py --name full-publication --resume
```

Resume verifies cached outputs against source, dependency, artifact and log
hashes. Changed inputs require a new run name. Two processes must not use the
same run name concurrently. A partial `--target` build never sets `complete`.

## 4. Incremental development checks

For a normal development build, the existing scripts remain available:

```sh
python3 scripts/build_upstream.py
python3 scripts/verify.py
python3 scripts/check_fc.py
python3 scripts/check_fc_proposal.py
python3 scripts/manuscript_correspondence.py --check-build --render
```

These use `.lake/build/lib/lean`. `verify.py` treats local warnings as errors,
audits the exact 494 declarations and checks the main theorem's expanded type.
Its `--audit-only` mode verifies recorded source, artifact and audit-log hashes.
The default connection check explicitly records incremental verification.

The included producer records alone are insufficient for `--audit-only` in a
fresh checkout: no project `.olean` files are distributed.

## 5. GitHub Actions

[source-checks.yml](../.github/workflows/source-checks.yml) checks source integrity
and publication tests on pushes and pull requests.
[lean-verification.yml](../.github/workflows/lean-verification.yml) is a manually
dispatched full build: it installs the pinned toolchain, obtains locked package
caches, builds the entire core into fresh outputs, audits the FC connection and
checks main and both expanded FC variants against their proved theorems.
The workflows have read-only repository permissions and upload verification
reports. The [public Comparator CI](https://github.com/KitaKen1/all-prime-residually-finite-p-groups/actions/runs/38865696145) passed; its source and
checker identities are recorded in [the public CI record](../verification/public-ci-verification.json).
The earlier [private CI record](../verification/private-ci-verification.json) is retained separately.

The reference repository's results remain separate from this proof. This
publication has its own pinned tooling, successful public and private runs, and archived
receipts. The
[Comparator CI appendix](../README.md#appendix-verification-by-lean-comparator-on-github-ci-runner)
summarizes the CI and archive status.

## 6. Lean Comparator certification

The independent proposition definitions are in [Challenge.lean](../lean/Challenge.lean).
[ComparatorChallenge.lean](../lean/ComparatorChallenge.lean) states the reference
theorems, and [FCSolution.lean](../lean/FCSolution.lean) supplies their proofs.
The comparison targets are
`AllPrimeGroupsFC.finitely_presented_burnside_problem` for main,
`AllPrimeGroupsFC.variants.finitely_presented_burnside_problem_residually_finite` for the
residually finite periodic variant, and
`AllPrimeGroupsFC.variants.finitely_presented_burnside_problem_all_primes` for the all-prime strengthening.
`AllPrimeGroupsFC.concrete_groups` supplies the four properties of the specified
finite-rank kernels, and `AllPrimeGroupsFC.all_prime_groups` preserves the existing
descriptive name for the variant.
Their existing local [connection report](../verification/fc-connection.json) and
[axiom output](../verification/fc-connection.log) establish the producer check.

The separate [Comparator workflow](../.github/workflows/comparator.yml) now runs
the three expanded FC targets against a Mathlib-only
[ComparatorChallenge.lean](../lean/ComparatorChallenge.lean), with pinned
4.34-compatible checker sources built on Lean 4.34.1. It builds all 204 project
modules, compares the three theorems, checks 494 core and five connection axiom
audits, and runs `leanchecker --fresh FCSolution` in a separate job. Both replay
checks use Lean's kernel; Nanoda is not configured. Both the private test and
[public main run](https://github.com/KitaKen1/all-prime-residually-finite-p-groups/actions/runs/38865696145) passed. The
[public record](../verification/public-ci-verification.json) covers all three
targets, the full build, axiom audits and separate fresh replay.
See [the configuration guide](../lean/comparator/README.md) for input pins,
the independently compiled challenge and the four required CI jobs.

Before GitHub's retention period expires, preserve the complete job logs,
original artifact ZIPs, run metadata, extracted receipts and SHA-256 checksums.
Archive provenance should fix the tested source commit, run and attempt and
record the tool revisions. Check the original ZIP hashes against the GitHub
API digests. The [public-run archive](../verification/public-ci-38865696145-attempt1/)
preserves this evidence, alongside the earlier [private-run archive](../verification/private-ci-38856485805-attempt1/).

Use [scripts/archive_ci.py](../scripts/archive_ci.py) to archive a completed run.
It parses axiom logs independently of line wrapping. The original
`lean/comparator/archive-run.py` is retained unchanged as a pinned input of the
tested CI snapshot.

```sh
python3 scripts/archive_ci.py --repo KitaKen1/all-prime-residually-finite-p-groups \
  --run 38865696145 --attempt 1 \
  --expected-commit c1ce611712e5a7804ed5056ad60600ffc941186a \
  --output verification/public-ci-archive --public-success-only
```

The output directory must be new. `--public-success-only` requires a successful
run on public `main`. For another run, use its run, attempt and tested commit.
