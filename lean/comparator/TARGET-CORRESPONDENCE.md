# Comparator target correspondence

All targets use the standard Mathlib group predicates. The reference imports
only Mathlib, never the proposed proof or its locally defined groups.

| Role | Target under `AllPrimeGroupsFC` | Reference and conclusion |
|---|---|---|
| Main | `finitely_presented_burnside_problem` | An infinite finitely presented periodic group exists. |
| Variant 1 | `variants.finitely_presented_burnside_problem_residually_finite` | The same existence statement with residual finiteness. |
| Variant 2 | `variants.finitely_presented_burnside_problem_all_primes` | For every prime p, an infinite finitely presented residually finite p-group exists. |

[`ComparatorChallenge.lean`](../ComparatorChallenge.lean) independently states the
expanded types in [`FClikelean`](../../FClikelean/AllPrimeGroups.lean).
[`FCSolution.lean`](../FCSolution.lean) supplies the three proofs.
[`check-inputs.py`](check-inputs.py) rejects changes to these statements and to
the pinned proof and verification inputs. The original `Challenge.lean` remains
a separate Mathlib-only collection of proposition definitions.
