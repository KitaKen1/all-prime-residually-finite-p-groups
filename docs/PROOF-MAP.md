# Mathematical statements and proof map

The all-prime variant uses standard Mathlib predicates. The same witness must be
infinite, finitely presented, residually finite and an elementwise torsion
$p$-group. Neither a uniform exponent nor a pro-$p$ presentation is required.

| Result | Declaration | Source |
|---|---|---|
| Original finitely presented Burnside problem (OpenAI) | `AllPrimeGroupsFC.finitely_presented_burnside_problem` | [FCSolution](../lean/FCSolution.lean), using `OAI.SourceBurnside.thm_main.2` |
| Residually finite periodic variant (variant 1) | `AllPrimeGroupsFC.variants.finitely_presented_burnside_problem_residually_finite` | [FCSolution](../lean/FCSolution.lean), taking p = 2 and deriving periodicity |
| Existence for every prime | `AllPrimeGroups.all_prime_groups` | [PrimeCharacterExtensions](../lean/AllPrimeGroups/PrimeCharacterExtensions.lean) |
| Independent main and variant references | `AllPrimeGroupsChallenge.MainStatement`, `AllPrimeGroupsChallenge.ResiduallyFinitePeriodicStatement`, `AllPrimeGroupsChallenge.Statement` | [Challenge](../lean/Challenge.lean) |
| All-prime variant and its descriptive name | `AllPrimeGroupsFC.variants.finitely_presented_burnside_problem_all_primes`, `AllPrimeGroupsFC.all_prime_groups` | [FCSolution](../lean/FCSolution.lean) |
| Actual fixed-rank kernel and its four properties, $n\ge7$ | `PrimeGroups.G`, `PrimeGroups.properties` | [PrimeGroups](../lean/AllPrimeGroups/PrimeGroups.lean) |
| Infinite coefficient algebra, characteristic $p$, matrix nilpotence, finite presentation | `PrimeAlgebra.infinite`, `charP`, `matrix_nil`, `steinberg_finitelyPresented` | [PrimeAlgebra](../lean/AllPrimeGroups/PrimeAlgebra.lean) |
| Finite-rank injection into the stable group, $n\ge7$ | `PrimeAlgebra.stabilization_injective` | [PrimeCharacterExtensions](../lean/AllPrimeGroups/PrimeCharacterExtensions.lean) |
| Stable separation by finite coefficient quotients | `Phases.separation`, `Phases.separation_obligation` | [PrimeSeparation](../lean/AllPrimeGroups/PrimeSeparation.lean) |
| Relative $p$-power torsion in the central matrix kernel | `Stable.relative_torsion` | [RelativeTorsion](../lean/AllPrimeGroups/RelativeTorsion.lean) |
| Finite Steinberg groups over the relevant finite rings, $n\ge6$ | `Steinberg.finite_of_local_augmentation`, `finite_of_finite_field` | [FiniteLocal](../lean/AllPrimeGroups/FiniteLocal.lean) |
| Finite-index subgroups inherit finite presentation | `isFinitelyPresented_of_finiteIndex` | [FiniteIndexPresentation](../lean/AllPrimeGroups/FiniteIndexPresentation.lean) |
| Finite $p$-group quotients and finite-set separation | `FinitePQuotients.separate_finset`, `unbounded_quotients` | [FinitePQuotients](../lean/AllPrimeGroups/FinitePQuotients.lean) |
| Concrete finite quotient consequences | `PrimeGroups.finite_p_quotient_injective_on`, `finite_p_quotients_unbounded` | [PrimePQuotients](../lean/AllPrimeGroups/PrimePQuotients.lean) |
| The set bijection $a\mapsto1+a$ and exact finite-dimensional cardinality | `NilCongruence.kernelEquiv`, `card_eq_prime_pow_finrank` | [NilCongruence](../lean/AllPrimeGroups/NilCongruence.lean) |
| Matrix-unit cardinality $p^{n^2\dim\ker\varepsilon}$ | `NilCongruence.matrix_card_eq_prime_pow_finrank` | [NilMatrixCongruence](../lean/AllPrimeGroups/NilMatrixCongruence.lean) |
| Infinite residually finite $p$-groups of units over $R(p)$ | `PrimeAlgebra.congruenceUnits_properties`, `matrixCongruenceUnits_properties` | [PrimeNilUnits](../lean/AllPrimeGroups/PrimeNilUnits.lean) |

## Finite-rank stability route

The proof uses the actual multi-row frame stabilizers and their face maps.
The main stages are [FrameBlockMatrices](../lean/AllPrimeGroups/FrameBlockMatrices.lean),
[BlockFaceMaps](../lean/AllPrimeGroups/BlockFaceMaps.lean),
[FrameActionStabilizers](../lean/AllPrimeGroups/FrameActionStabilizers.lean),
[FrameShapiro](../lean/AllPrimeGroups/FrameShapiro.lean),
[FrameH2Lift](../lean/AllPrimeGroups/FrameH2Lift.lean) and
[PrimeCharacterRealization](../lean/AllPrimeGroups/PrimeCharacterRealization.lean).
Character extensions of the rational circle then give stabilization injectivity.
The argument does not assume that injectivity in its hypotheses.

## Manuscript scope

The manuscript specifies $n\ge12$; the formal proof gives the same kernel's four
properties already for $n\ge7$. It avoids identifying the earlier stable-image
candidate with the finite-rank reduction kernel: a subgroup inclusion is enough
to transfer residual finiteness and the $p$-group property.

The machine-readable [inventory](../lean/manuscript-claims.json) contains all
41 numbered claims. The [rendered correspondence](../lean/manuscript-correspondence.html) links
68 audited declarations. It records 19 proved claims, 5 needed specializations,
4 replacements, 12 partial correspondences and 1 unregistered independent claim.

In particular, the stronger stability statement for general augmented algebras,
the full homology-isomorphism argument, and the general graded-algebra-to-finite-
truncation construction are not represented as completely formalized. The
non-finitely-generated counterexample is an unregistered independent claim.
These distinctions do not leave an extra hypothesis in the all-prime existence theorem.

The inventory and source references are checked by a script. The mathematical
scope classifications remain manual; they do not constitute an automated proof
that a paper sentence is equivalent to a Lean statement.
