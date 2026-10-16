# Attribution and dependency provenance

This repository is distributed under [Apache-2.0](../LICENSE). Existing third-party
copyright notices and licenses are retained. [NOTICE](../NOTICE) identifies the
contributors and AI assistance.

| Source | Fixed revision | Use |
|---|---|---|
| [OpenAI math](https://github.com/openai/math/tree/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/PeriodicGroups) | `1581d4cbdd69a0faf34b2089614fe2a814316a6a` | 63 unchanged word-machine and periodic-group modules, vendored under `lean/OAI/`. |
| [Mathlib](https://github.com/leanprover-community/mathlib4/tree/d13f23b723b8a846827a245b89c10fc7d3f11612) | `d13f23b723b8a846827a245b89c10fc7d3f11612` | Standard predicates, group cohomology, linear algebra and algebraic infrastructure; fetched as a dependency. |
| [Tau Ceti](https://github.com/TauCetiProject/TauCeti/tree/4f1a681d10b8371c56bc49158b0481d18bd949f5) | `4f1a681d10b8371c56bc49158b0481d18bd949f5` | Adapted group extensions, projective comparisons and explicit Shapiro formulas. |
| [Tau Ceti conjugation](https://github.com/TauCetiProject/TauCeti/tree/d5a37097e93f6289425d25632df6c8bf00d749c0) | `d5a37097e93f6289425d25632df6c8bf00d749c0` | Degree-two algebraic cocycle conjugation calculation, recorded separately from the earlier pin. |
| [Lean Pool](https://github.com/Vilin97/lean-pool/tree/01db1d7049cf9668bda1e9e106875ee1278b43e6) | `01db1d7049cf9668bda1e9e106875ee1278b43e6` | Adapted multiplicative cocycle product calculation. |

The FC `finitely_presented_burnside_problem` theorem directly reuses the abstract periodic-group conclusion of
OpenAI's `OAI.SourceBurnside.thm_main`. That conclusion does not supply residual
finiteness or prescribed $p$-power order. The FC `variants.finitely_presented_burnside_problem_all_primes` is the present
all-prime result, which adds characteristic-$p$ matrix nilpotence,
stable separation, finite-rank injectivity and the final assembly.
The FC `variants.finitely_presented_burnside_problem_residually_finite` theorem is a
corollary of this all-prime result: it specializes to p = 2 and retains residual
finiteness while deriving periodicity. It does not claim a separate construction.

The original hashes, URLs and retained licenses are in
[lean/upstream/](../lean/upstream/). Adapted files describe their changes locally.
The adapted code uses this repository's pinned Mathlib rather than the source
projects' full dependency environments.

The development also inspected lean-eval and PNT+ material for proof organization.
Neither is a dependency or a theorem used in the proof. No analytic-number-theory
result or unfinished proof hole from those projects is used.

The layout of this publication is inspired by
[KitaKen1/entropic-rogers-shephard](https://github.com/KitaKen1/entropic-rogers-shephard).
Its theorem, CI, Comparator and kernel-replay results are distinct from this work.
