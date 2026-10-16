# Proposed Formal Conjectures statements

[AllPrimeGroups.lean](AllPrimeGroups.lean) follows the Formal Conjectures problem-file
format: `FormalConjecturesUtil`, an exposed public section, three theorem declarations,
`category research solved`, `AMS 20`, and a `formal_proof using lean4 at` reference.
All three declarations use Mathlib's standard group predicates directly.

| Declaration | Role | Statement |
|---|---|---|
| `AllPrimeGroupsFC.finitely_presented_burnside_problem` | Main: original OpenAI problem | There exists an infinite finitely presented periodic group. |
| `AllPrimeGroupsFC.variants.finitely_presented_burnside_problem_residually_finite` | Variant 1: residual finiteness | There exists an infinite finitely presented periodic residually finite group. |
| `AllPrimeGroupsFC.variants.finitely_presented_burnside_problem_all_primes` | Variant 2: every prime | For every prime p, there exists an infinite finitely presented residually finite p-group. |

`finitely_presented_burnside_problem` is the abstract-group `BurnsideStatement`
from OpenAI's
[PeriodicGroup challenge](https://github.com/openai/math/blob/main/lean/ComparatorChallenges/PeriodicGroup.lean),
written with its periodicity condition expanded. The upstream challenge also
contains a concrete Steinberg-group witness; the FC main statement expresses
the underlying existence problem. Its proof reuses `OAI.SourceBurnside.thm_main.2`.

Variant 1 retains periodicity and adds residual finiteness; it does not quantify
over a prime or require a p-group. Its proof specializes this repository's
all-prime theorem to p = 2 and chooses m = 2^k for each element. Variant 2 is the
all-prime result itself. Thus variant 2 implies variant 1, which implies main.
The same group supplies every property in each existence statement.

Each `by sorry` is the conventional placeholder for a proposed problem statement.
The actual three theorems are proved in
[FCSolution.lean](../lean/FCSolution.lean), and
[FCAudit.lean](../lean/FCAudit.lean) audits them together with the existing
`all_prime_groups` name for variant 2 and the concrete-group theorem: five audits.
These proved files contain no placeholders.

[Challenge.lean](../lean/Challenge.lean) remains a separate Mathlib-only reference
for all three statements. Each expanded proposal statement is checked separately
against its reference and proved theorem by
[check_fc_proposal.py](../lean/scripts/check_fc_proposal.py).
See the [statement-check record](../verification/fc-proposal.json).

The proof project uses Lean 4.34.1. The official
[Formal Conjectures environment](https://github.com/google-deepmind/formal-conjectures/blob/main/lean-toolchain)
inspected for this proposal uses Lean 4.33.1; full FC-environment compilation and
linting have not been run. The local check establishes all three mathematical
statements' connections to the proofs under the proof project's pinned dependencies.

The `formal_proof` URL points to the intended publication path on `main`. Once
the proof is published and verified, replace that branch reference with the
tested commit before submitting the proposal to Formal Conjectures.
