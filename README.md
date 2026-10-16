# Lean proof of infinite finitely presented residually finite p-groups for every prime

OpenAI solved the following finitely presented Burnside problem
([OAI26, Theorem 1.1](https://github.com/openai/math/tree/main/preprints/An-infinite-finitely-presented-periodic-group-September-23-2026)).

> **Main: finitely presented Burnside problem.** Does there exist an infinite
> finitely presented periodic group, that is, a group in which every element
> has finite order?

This repository considers the following two stronger variants, in the same order
as [FClikelean/AllPrimeGroups.lean](FClikelean/AllPrimeGroups.lean).

> **Variant 1: residual finiteness.** Does there exist an infinite finitely
> presented periodic residually finite group?

> **Variant 2: every prime.** For every prime $`p`$, does there exist an infinite
> finitely presented residually finite abstract $`p`$-group?

This repository solves **variants 1 and 2**.
Note that solving variant 2 solves variant 1, which in turn solves main.

| Condition | main | variant 1 | variant 2 |
|---|---|---|---|
| Infinite | ✓ | ✓ | ✓ |
| Finitely presented | ✓ | ✓ | ✓ |
| Periodic | ✓ | ✓ | From the $`p`$-group condition |
| Residually finite | — | ✓ | ✓ |
| $`p`$-group | — | — | Every prime $`p`$ |

✓ = required; — = not required.

OpenAI also proved the residually finite $`2`$-group case in
[5 October 2026](https://github.com/openai/math/tree/main/preprints/An-infinite-finitely-presented-residually-finite-2-group-October-5-2026).
That result also implies variant 1. The all-prime variant supplies such groups
for every prime; the [problem-relation appendix](#appendix-problem-relation)
separates these statements and their sources.

The two main components are:

1. **Formal Conjectures style statements.**
   [FClikelean/](FClikelean/) contains main,
   `finitely_presented_burnside_problem`, and two declarations in `variants`:
   `finitely_presented_burnside_problem_residually_finite` (variant 1) and
   `finitely_presented_burnside_problem_all_primes` (variant 2). Each has an FC
   classification, a docstring and a formal-proof reference.
2. **The full Lean proof.**
   [PrimeCharacterExtensions.lean](lean/AllPrimeGroups/PrimeCharacterExtensions.lean)
   proves `AllPrimeGroups.all_prime_groups : AllPrimeGroups.Target`.
   [PrimeGroups.lean](lean/AllPrimeGroups/PrimeGroups.lean) proves the four
   properties of the specified finite-rank reduction kernels.
   [FCSolution.lean](lean/FCSolution.lean) connects all three FC statements to
   their proofs.

## Formal Conjectures like targets

The proposed problem file is
[FClikelean/AllPrimeGroups.lean](FClikelean/AllPrimeGroups.lean). It imports
`FormalConjecturesUtil` and declares the following three theorems with
`category research solved`, `AMS 20`, and a `formal_proof using lean4 at` link.
The Lean declarations below are copied from that file. Their `by sorry` endings
are statement placeholders; the actual proofs are in
[FCSolution.lean](lean/FCSolution.lean).

### Main: the finitely presented Burnside problem

**Statement.** An infinite finitely presented periodic group exists
[OAI26, Theorem 1.1]. The same group must satisfy all three conditions.

```lean
theorem finitely_presented_burnside_problem :
    ∃ (G : Type) (inst : Group G),
      Infinite G ∧ @Group.IsFinitelyPresented G inst ∧
        (∀ g : G, ∃ m : ℕ, 0 < m ∧ g ^ m = 1) := by
  sorry
```

The declaration is in `namespace AllPrimeGroupsFC`. It expresses the
abstract-group `BurnsideStatement` from OpenAI's
[PeriodicGroup challenge](https://github.com/openai/math/blob/main/lean/ComparatorChallenges/PeriodicGroup.lean),
with periodicity expanded as `∀ g, ∃ m : ℕ, 0 < m ∧ g ^ m = 1`.
The positive integer `m` may depend on `g`; a common exponent is not required.
Its proof in this repository is `OAI.SourceBurnside.thm_main.2`.

### Variant 1: a residually finite periodic group

**Statement.** An infinite finitely presented periodic residually finite group
exists. The answer is yes, as a consequence of [Ki26].

```lean
theorem finitely_presented_burnside_problem_residually_finite :
    ∃ (G : Type) (inst : Group G),
      Infinite G ∧ @Group.IsFinitelyPresented G inst ∧
        (∀ g : G, ∃ m : ℕ, 0 < m ∧ g ^ m = 1) ∧
        @Group.ResiduallyFinite G inst := by
  sorry
```

This declaration is in `namespace AllPrimeGroupsFC.variants`. It keeps main's
periodicity condition and adds residual finiteness of the same group. There is
no prime parameter and no $`p`$-group requirement in its statement.

Its proof takes the $`p=2`$ group from the all-prime theorem. For any element
`g`, the $`2`$-group property supplies `k` with `g ^ (2 ^ k) = 1`; choosing
`m = 2 ^ k > 0` gives periodicity. The existing infinitude, finite-presentation
and residual-finiteness proofs are retained.

### Variant 2: a residually finite p-group for every prime

**Statement.** For every prime $`p`$, an infinite finitely presented residually
finite $`p`$-group exists. The answer is yes [Ki26].

```lean
theorem finitely_presented_burnside_problem_all_primes :
    ∀ p : ℕ, p.Prime →
      ∃ (G : Type) (inst : Group G),
        Infinite G ∧ @Group.IsFinitelyPresented G inst ∧
          @Group.ResiduallyFinite G inst ∧ @IsPGroup p G inst := by
  sorry
```

This declaration is also in `namespace AllPrimeGroupsFC.variants`. Its
quantifiers choose the prime before the group: the group may depend on `p`.
`IsPGroup p G` means that for every `g : G` there is a natural number `k` with
`g ^ (p ^ k) = 1`. Since a prime is positive, `p ^ k > 0`, so periodicity
follows even though it is not written as a separate conjunct.
The proof is `AllPrimeGroups.all_prime_groups`.

### Reference statements and proof connections

[Challenge.lean](lean/Challenge.lean) defines the three propositions independently
of their proofs, using Mathlib's standard predicates. The following names are
used by [FCSolution.lean](lean/FCSolution.lean); all declarations are under
`AllPrimeGroupsFC`.

| FC declaration | Independent reference in `AllPrimeGroupsChallenge` | Proof connection |
|---|---|---|
| `finitely_presented_burnside_problem` | `MainStatement` | Reuses `OAI.SourceBurnside.thm_main.2`. |
| `variants.finitely_presented_burnside_problem_residually_finite` | `ResiduallyFinitePeriodicStatement` | Specializes the all-prime theorem at 2 and derives periodicity. |
| `variants.finitely_presented_burnside_problem_all_primes` | `Statement` | Uses `AllPrimeGroups.all_prime_groups` directly. |

Mathematically, variant 2 implies variant 1, which implies main. The current
main proof uses OpenAI's theorem directly; it does not call the variant 1 proof.
`FCSolution.lean` also preserves `AllPrimeGroupsFC.all_prime_groups` as a
descriptive name for variant 2 and supplies `AllPrimeGroupsFC.concrete_groups`
for the actual groups in the construction.
[FCAudit.lean](lean/FCAudit.lean) audits all five theorems and checks the expanded
statements. The [proof map](docs/PROOF-MAP.md) links the mathematical claims to
their declarations.

All three expanded proposal statements have been checked against the independent
references and their proved solutions under the proof project's Lean 4.34.1
dependencies, without using the proposal placeholders. See the
[statement-check record](verification/fc-proposal.json) and the
[proof-connection record](verification/fc-connection.json).
FC-environment compilation and linting have not been run. The `formal_proof`
links target the intended publication path on `main`; they should be pinned to
the tested commit before an FC submission.

## Mathematical explanation (AI generated)

**1. Construct the coefficient algebra.** A finite hierarchy of homogeneous word
rules gives an infinite algebra $`R(p)`$ over $`\mathbb F_p`$, with an augmentation
$`\varepsilon:R(p)\to\mathbb F_p`$. Its positive ideal is matrix-nil: every finite
matrix over $`\ker\varepsilon`$ is nilpotent. The word-machine construction reuses
63 unchanged modules from a fixed revision of OpenAI's `math` repository; the
characteristic-$`p`$ argument is developed here.

**2. Separate stable elements.** Compatible cyclic phases on long surviving words
and finite word-length truncations give

```math
\bigcap_d\ker\!\left[
\operatorname{St}(R(p))\longrightarrow
\operatorname{St}(R(p)/I_{\ge d})
\right]=\{1\}.
```

The final step kills the same element by a $`p`$-power and an exponent coprime to
$`p`$. Their greatest common divisor is one, so the element is the identity.

**3. Prove finite-rank injectivity.** The complex of ordered frames, its multi-row
stabilizers and their face maps supply a low-degree cochain argument. Explicit
Shapiro maps and central-extension characters then give

```math
\operatorname{St}_n(R(p))\hookrightarrow\operatorname{St}(R(p)),\qquad n\ge7.
```

This uses adapted extension and Shapiro code from Tau Ceti, its algebraic
conjugation calculation, and a cocycle product calculation from Lean Pool.
The source revisions and adaptation details are recorded in
[lean/upstream/](lean/upstream/).

**4. Obtain a finite-index kernel.** Define

```math
G(p,n)=\ker\!\left[
\operatorname{St}_n(R(p))\longrightarrow\operatorname{St}_n(\mathbb F_p)
\right].
```

The target is a finite Steinberg group. Hence the kernel has finite index.
The coefficient algebra's finite presentation and finite-index rewriting give
an ordinary finite presentation of $`G(p,n)`$.

**5. Assemble the four properties.** The infinite coefficient algebra gives
infinitude of the kernel. Matrix nilpotence and relative central torsion kill a
$`p`$-power of each element, and finite-rank injectivity returns this identity to
$`G(p,n)`$. Stable separation detects each nonidentity element in a finite
truncated Steinberg group. Thus the same group has all four properties for every
$`n\ge7`$, including the manuscript's choice $`n=12`$.

The [proof manuscript](PDF/all-prime-residually-finite-p-groups.pdf) gives the paper
argument. Its existing [timestamp receipt](PDF/all-prime-residually-finite-p-groups.pdf.ots)
is preserved. The [manuscript correspondence](lean/manuscript-correspondence.html)
records which intermediate statements are proved, specialized or still partial.

## Files

| Directory | Lean version | Purpose |
|---|---|---|
| [lean/](lean/) | `v4.34.1` | Canonical proof, pinned dependencies, Challenge, FCSolution and audits. |
| [FClikelean/](FClikelean/) | — | FC problem file with main, the residually finite periodic variant, and the all-prime p-group variant; all three expanded statements are checked against their proved solutions. |
| [lean/upstream/](lean/upstream/) | — | Original source hashes, commit pins and third-party licenses. |
| [verification/](verification/) | — | Compilation records, axiom audits and verification summaries. |
| [.github/workflows/](.github/workflows/) | GitHub-hosted Linux | Source checks, full build, three-target Comparator and separate fresh kernel replay. |
| [PDF/](PDF/) | — | Paper manuscript and its existing timestamp receipt. |

The core contains 134 local modules, 63 unchanged upstream modules, the root
import and two audits: 200 Lean sources. Three additional files supply the
reference, proof connection and connection audit. The independent
Comparator challenge adds one more source, for 204 project sources in CI.
[PUBLICATION-MANIFEST.json](PUBLICATION-MANIFEST.json) records the publication
inventory and SHA-256 hashes.

## Verification

### Lean execution results

The current local proof passes 134 module checks and 494 core axiom audits.
All audited declarations use only `[propext, Classical.choice, Quot.sound]`, or a
subset. [Audit.lean](lean/Audit.lean) also checks the expanded all-prime statement.
The three reference/connection files compile, and their five theorem audits pass.
The [FC proposal statement check](verification/fc-proposal.json) also passes:
all three expanded types are proved by their existing solutions without using the
proposal placeholders.

A separate fresh-output build of the earlier 195-source baseline passed,
including the main theorem. The later five added modules and updated root
import/audit were checked incrementally. The extracted-source portability check
rebuilt five modules and audited 20 generic nil-unit declarations. These checks
used the same macOS host and pinned package caches. See the
[verification records](verification/README.md) for their exact scopes.

[Private Linux CI](https://github.com/KitaKen1/ci-test-sandbox/actions/runs/38856485805) passed on Lean 4.34.1: all **204 project modules**
built, Comparator accepted **main, variant 1 and variant 2**, the **494 core and
five connection axiom audits** passed, and a separate
`leanchecker --fresh FCSolution` replay succeeded. Both replay checks use Lean's
kernel. See the [CI record](verification/private-ci-verification.json) and the
[Comparator CI appendix](#appendix-verification-by-lean-comparator-on-github-ci-runner).
Public CI has not yet been run.

### Reproduce the verification

With elan, Python 3.10 or later and Git installed, run:

```sh
python3 scripts/check_publication.py
cd lean
lake exe cache get
python3 scripts/test_verification.py
python3 scripts/test_release.py
python3 scripts/reproduce.py --name full-publication
python3 scripts/check_fc.py --reproduction full-publication
python3 scripts/check_fc_proposal.py --reproduction full-publication
```

This builds all core sources into fresh project outputs, then checks the
reference connection and expanded FC proposal against those outputs. The locked toolchain and package
caches are reused. For the Linux workflow, resume instructions and completion
flags, see the [verification guide](docs/VERIFICATION.md).

## Scope and citation

The existence theorem and the specified concrete kernels are proved. Stronger
general stability and homology statements in the manuscript retain the scope
qualifications documented in the [proof map](docs/PROOF-MAP.md).

See [NOTICE](NOTICE), [attribution](docs/ATTRIBUTION.md), [LICENSE](LICENSE)
and [CITATION.cff](CITATION.cff).

## Sources

- **[OAI26]** OpenAI,
  [*An infinite finitely presented periodic group* (23 September 2026)](https://github.com/openai/math/tree/main/preprints/An-infinite-finitely-presented-periodic-group-September-23-2026),
  Theorem 1.1; the main existence problem in FClikelean. See also its
  [PeriodicGroup challenge](https://github.com/openai/math/blob/main/lean/ComparatorChallenges/PeriodicGroup.lean).
- **[Ki26]** Kenta Kitamura,
  [*Infinite finitely presented residually finite p-groups for every prime*](https://github.com/KitaKen1/all-prime-residually-finite-p-groups)
  (GitHub repository, 2026); the all-prime result (variant 2) and the residually
  finite periodic consequence (variant 1).
- [Mathlib](https://github.com/leanprover-community/mathlib4/tree/d13f23b723b8a846827a245b89c10fc7d3f11612):
  standard group predicates, group cohomology, linear algebra and algebraic infrastructure.
  The dependency revision is fixed in [lake-manifest.json](lean/lake-manifest.json).
- [OpenAI math](https://github.com/openai/math/tree/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/PeriodicGroups):
  63 unchanged word-machine and periodic-group modules. Their original hashes are
  recorded in [provenance.json](lean/upstream/provenance.json).
- [Tau Ceti](https://github.com/TauCetiProject/TauCeti/tree/4f1a681d10b8371c56bc49158b0481d18bd949f5):
  adapted group extensions, projective comparisons and explicit Shapiro formulas.
  The algebraic conjugation calculation uses a
  [separate fixed revision](https://github.com/TauCetiProject/TauCeti/tree/d5a37097e93f6289425d25632df6c8bf00d749c0).
- [Lean Pool](https://github.com/Vilin97/lean-pool/tree/01db1d7049cf9668bda1e9e106875ee1278b43e6):
  an adapted multiplicative cocycle product calculation.

Original source hashes, adaptation details and licenses are retained in
[lean/upstream/](lean/upstream/). See [attribution](docs/ATTRIBUTION.md) for the
scope of reuse.

## AI usage disclosure

This formalization, mathematical exploration, proof development, and documentation were produced by Kenta Kitamura with assistance from ChatGPT and OpenAI Codex using GPT-6 Astra and GPT-6.1 sol, and Claude Code using Claude Opus 5.5.

## Appendix: problem relation

The answers in this table refer to the statements below. Finite generation
requires finitely many generators; ordinary finite presentation also requires
finitely many defining relators.

| Problem | Generation / presentation | Element-order condition | Residual finiteness | Answer and solver |
|---|---|---|---|---|
| [Burnside question](#burnside-question) | Finitely generated | Every element has finite order | Not required | No — Golod (1964) |
| [Bounded Burnside question](#bounded-burnside-question) | Finitely generated | One common finite exponent | Not required | No in general — Novikov and Adian (1968) |
| [Restricted Burnside problem](#restricted-burnside-problem) | Finite groups with a fixed generator bound | One fixed exponent | Automatic for finite groups | Yes, a uniform order bound — Zelmanov (1990–1991) |
| [Finitely presented Burnside question](#finitely-presented-burnside-question) | Finitely presented | Every element has finite order | Not required | Yes — OpenAI (23 September 2026) |
| [Residually finite periodic variant](#residually-finite-periodic-variant) | Finitely presented | Every element has finite order | Required | Yes — a corollary of this repository's all-prime theorem |
| [Residually finite 2-group question](#residually-finite-2-group-question) | Finitely presented | Every element has 2-power order | Required | Yes — OpenAI (5 October 2026) |
| [All-prime variant](#all-prime-variant) | Finitely presented | Every element has p-power order, for every prime p | Required | Yes — Kenta Kitamura, this repository (2026) |

### Burnside question

**Statement.** Must every finitely generated group in which every element has
finite order be finite?

**Answer and solver.** No. [Golod (1964)](https://www.mathnet.ru/eng/im2956)
constructed infinite finitely generated residually finite $`p`$-groups for every
prime $`p`$, using the Golod–Shafarevich method.

**Relation.** These examples settle the general finite-generation question.
Ordinary finite presentation is the additional requirement in the later
questions considered here.

### Bounded Burnside question

**Statement.** Must a finitely generated group be finite if there is a positive
integer $`e`$ such that $`g^e=1`$ for every group element $`g`$?

**Answer and solver.** No in general.
[Novikov and Adian (1968)](https://www.mathnet.ru/eng/im2699) constructed infinite
finitely generated groups of sufficiently large odd exponent.

**Relation.** This imposes one common exponent on all elements. The negative
answer supplies counterexamples for suitable exponents; it does not assert
that infinite examples exist for every exponent.

### Restricted Burnside problem

**Statement.** For fixed positive integers $`d`$ and $`e`$, is there a bound
$`B(d,e)`$ on the orders of all finite groups generated by at most $`d`$ elements
and satisfying $`g^e=1`$ for every element?

**Answer and solver.** Yes. Zelmanov's work in 1990–1991 established the required
bounds, completing the restricted Burnside problem; see the papers on
[odd exponents](https://www.mathnet.ru/eng/im1104) and
[2-groups](https://www.mathnet.ru/eng/sm1311).

**Relation.** It follows that a finitely generated residually finite group of
finite exponent is finite. Consequently the infinite residually finite groups
in this repository have unbounded element orders. The exponent in their
elementwise $`p`$-power torsion statement may depend on the element.

### Finitely presented Burnside question

**Statement.** Does there exist an infinite group with an ordinary finite
presentation in which every element has finite order?

**Answer and solver.** Yes — OpenAI, in
[An infinite finitely presented periodic group (23 September 2026)](https://github.com/openai/math/tree/main/preprints/An-infinite-finitely-presented-periodic-group-September-23-2026).

**Relation.** This requires finite presentation as well as periodicity.
It is the original problem expressed by `AllPrimeGroupsFC.finitely_presented_burnside_problem` in
[FClikelean](FClikelean/AllPrimeGroups.lean); its proof connection reuses
OpenAI's abstract-group theorem in [FCSolution.lean](lean/FCSolution.lean).

### Residually finite periodic variant

**Statement.** Does there exist an infinite finitely presented periodic
residually finite group?

**Answer and proof.** Yes, as a corollary of
[this repository's all-prime theorem (Ki26)](https://github.com/KitaKen1/all-prime-residually-finite-p-groups).
The proof takes the p = 2 group, retains residual finiteness and derives
periodicity by choosing m = 2^k for each element. It is connected to
`AllPrimeGroupsFC.variants.finitely_presented_burnside_problem_residually_finite` in
[FCSolution.lean](lean/FCSolution.lean).

**Relation.** This is variant 1. It adds residual finiteness to main without
specifying a prime. The residually finite 2-group result below also implies
this existence statement; the intermediate statement is presented as a corollary,
not a separate construction.

### Residually finite 2-group question

**Statement.** Does there exist an infinite finitely presented residually finite
abstract group in which every element has finite 2-power order?

**Answer and solver.** Yes — OpenAI, in
[An infinite finitely presented residually finite 2-group (5 October 2026)](https://github.com/openai/math/tree/main/preprints/An-infinite-finitely-presented-residually-finite-2-group-October-5-2026).

**Relation.** This adds residual finiteness and restricts all element orders to
powers of the same prime, $`p=2`$. It supplies the 2-group case of the next
existence question.

### All-prime variant

**Statement.** For every prime $`p`$, does there exist an infinite finitely
presented residually finite abstract $`p`$-group?

**Answer and solver.** Yes — Kenta Kitamura,
[this repository (Ki26)](https://github.com/KitaKen1/all-prime-residually-finite-p-groups).
The Lean proof is connected to `AllPrimeGroupsFC.variants.finitely_presented_burnside_problem_all_primes` in
[FCSolution.lean](lean/FCSolution.lean), using the standard Mathlib predicates.

**Relation.** The group may depend on the chosen prime. Specializing to $`p=2`$
gives the preceding existence statement; retaining only infinitude, finite
presentation and periodicity gives an affirmative answer to the finitely
presented Burnside question. The fixed-prime existence question was already
recorded as a longstanding open problem by
[Minasyan, Corollary 1.8 and the following paragraph](https://www.personal.soton.ac.uk/am4x07/rs/subdir.pdf#page=5).

## Appendix: timeline (AI generated)

| Date | Contributor | Contribution |
|---|---|---|
| 1902 | William Burnside | **Question.** Asked whether a finitely generated group whose elements all have finite order must be finite ([historical correspondence and publication](https://arxiv.org/abs/0712.4296)). |
| 1964 | E. S. Golod | **Solved the general Burnside question negatively.** Constructed infinite finitely generated residually finite $`p`$-groups; ordinary finite presentation remained a further question ([paper](https://www.mathnet.ru/eng/im2956)). |
| 2016 | Ashot Minasyan | **Recorded the fixed-prime open problem.** Asked whether an infinite finitely presented residually finite $`p`$-group exists, and gave an equivalent formulation (Corollary 1.8 and the following paragraph, [paper](https://www.personal.soton.ac.uk/am4x07/rs/subdir.pdf#page=5)). |
| 23 September 2026 | OpenAI, family 247 | **Solved the finitely presented Burnside question in a preprint.** Constructed an infinite finitely presented periodic group ([paper](https://github.com/openai/math/blob/main/preprints/An-infinite-finitely-presented-periodic-group-September-23-2026/paper.pdf)). |
| 5 October 2026 | OpenAI, family 247 | **Strengthened the result to $`p=2`$.** Constructed an infinite finitely presented residually finite 2-group ([paper](https://github.com/openai/math/blob/main/preprints/An-infinite-finitely-presented-residually-finite-2-group-October-5-2026/residually-finite-torsion.pdf)). |
| October 2026 | This repository | **Extended to every prime and formalized in Lean.** Proves the existence of an infinite finitely presented residually finite $`p`$-group for every prime $`p`$, reusing OpenAI's word-machine modules ([proof](lean/FCSolution.lean), [reuse](docs/ATTRIBUTION.md)). |

## Appendix: Further results

### Simultaneous separation by finite p-group quotients

For every prime $`p`$, every $`n\ge7`$ and every finite subset $`S\subseteq G(p,n)`$,
there is a finite $`p`$-group $`H`$ and a surjective homomorphism
$`f:G(p,n)\to H`$ whose restriction to $`S`$ is injective. Thus a single finite
quotient can distinguish all elements of any prescribed finite subset at once.

This is proved as `AllPrimeGroups.PrimeGroups.finite_p_quotient_injective_on` in
[PrimePQuotients.lean](lean/AllPrimeGroups/PrimePQuotients.lean).
The general result for residually finite $`p`$-groups is
`AllPrimeGroups.FinitePQuotients.separate_finset` in
[FinitePQuotients.lean](lean/AllPrimeGroups/FinitePQuotients.lean).

### Finite p-group quotients of unbounded order

For the same groups $`G(p,n)`$, every bound $`B\in\mathbb N`$ admits a finite
$`p`$-group quotient $`H`$ with $`|H|\ge B`$. In particular, there is no upper
bound on the orders of their finite $`p`$-group quotients. The proof chooses
$`B`$ distinct elements and applies simultaneous separation to that finite set.

This is proved as `AllPrimeGroups.PrimeGroups.finite_p_quotients_unbounded` in
[PrimePQuotients.lean](lean/AllPrimeGroups/PrimePQuotients.lean), using
`AllPrimeGroups.FinitePQuotients.unbounded_quotients` in
[FinitePQuotients.lean](lean/AllPrimeGroups/FinitePQuotients.lean).

### Infinite residually finite p-groups of augmentation units

Let $`I=\ker\varepsilon`$ be the augmentation ideal of the constructed algebra
$`R(p)`$. For every positive matrix rank $`r`$, the group $`1+M_r(I)`$ is infinite,
residually finite and a $`p`$-group. Its elements are all matrices $`1_r+A`$ with
$`A\in M_r(I)`$; matrix nilpotence ensures that these matrices are invertible.
The scalar case gives the same three properties for $`1+I`$.

These statements are proved as
`AllPrimeGroups.PrimeAlgebra.matrixCongruenceUnits_properties` and
`AllPrimeGroups.PrimeAlgebra.congruenceUnits_properties` in
[PrimeNilUnits.lean](lean/AllPrimeGroups/PrimeNilUnits.lean).
Finite presentation is not asserted for these full unit groups.

### Exact orders of finite augmentation unit groups

More generally, let $`\varepsilon:R\to\mathbb F_p`$ be an algebra augmentation
with finite-dimensional kernel $`I`$, and put $`d=\dim_{\mathbb F_p}I`$.
If every element of $`I`$ is nilpotent, then $`|1+I|=p^d`$.
If every $`r\times r`$ matrix over $`I`$ is nilpotent, the corresponding matrix
group has the exact order

$$|1+M_r(I)|=p^{r^2d}.$$

The counting uses the set bijection $`A\mapsto1+A`$ and the
$`r^2d`$ coordinates of $`M_r(I)`$ over $`\mathbb F_p`$.
The scalar formula is proved as
`AllPrimeGroups.NilCongruence.card_eq_prime_pow_finrank` in
[NilCongruence.lean](lean/AllPrimeGroups/NilCongruence.lean), and the matrix formula as
`AllPrimeGroups.NilCongruence.matrix_card_eq_prime_pow_finrank` in
[NilMatrixCongruence.lean](lean/AllPrimeGroups/NilMatrixCongruence.lean).

## Appendix: Verification by Lean Comparator on GitHub CI runner

Lean Comparator checks theorem statements and dependent definitions against a reference,
audits permitted axioms and replays the solution in Lean's builtin kernel.
Full certification also includes a separate fresh replay of the complete proof environment.

### Certification Within 90 days: CI results

[Private Linux CI](https://github.com/KitaKen1/ci-test-sandbox/actions/runs/38856485805) passed for commit
`986a797c4c4e59b0e489f4f3bfb7a8b4017e6d9d` on Lean 4.34.1: the 204-source build, all three Comparator targets,
499 axiom audits and separate fresh kernel replay succeeded.
The [workflow](.github/workflows/comparator.yml) retains reports for 90 days.
The [verification record](verification/private-ci-verification.json) fixes the
tested commit, run and attempt. Public CI is pending.

### Certification After 90 days: archive

The private run is archived under [verification/private-ci-38856485805-attempt1/](verification/private-ci-38856485805-attempt1/):
the original artifact ZIPs, complete job logs, API metadata, extracted receipts
and SHA-256 checksums. [Provenance](verification/private-ci-38856485805-attempt1/provenance.json) fixes the tested
commit, run and attempt. Original ZIP hashes match the GitHub API digests.
A later public CI run will require its own verification record and archive.

### Reproduce the verification

Build with `cd lean && lake exe cache get`, then
`lake build FCSolution Audit UpstreamAudit ComparatorChallenge`.
To reproduce the available build and axiom checks on Linux, run the
[Comparator workflow](.github/workflows/comparator.yml) in a repository you control.
See [the verification guide](docs/VERIFICATION.md) for the reference targets,
fresh-output checks and [Comparator configuration](lean/comparator/README.md).
