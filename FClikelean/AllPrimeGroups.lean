module

public import FormalConjecturesUtil

/-!
# The finitely presented Burnside problem

Does there exist an infinite finitely presented periodic group? OpenAI gives
a positive answer in [OAI26, Theorem 1.1]. A group is periodic if every element
has finite order. Finite presentation means an ordinary presentation with
finitely many generators and relators.

*References:*
- [OAI26] OpenAI, *An infinite finitely presented periodic group*
  (23 September 2026), Theorem 1.1.
  https://github.com/openai/math/tree/main/preprints/An-infinite-finitely-presented-periodic-group-September-23-2026
- OpenAI, `PeriodicGroup` challenge, `OAI.SourceBurnside.BurnsideStatement`.
  https://github.com/openai/math/blob/main/lean/ComparatorChallenges/PeriodicGroup.lean
- [Ki26] Kenta Kitamura, *Infinite finitely presented residually finite p-groups
  for every prime*, GitHub repository (2026).
  https://github.com/KitaKen1/all-prime-residually-finite-p-groups
-/

@[expose] public section

namespace AllPrimeGroupsFC

/-- There exists an infinite finitely presented periodic group
[OAI26, Theorem 1.1]. -/
@[category research solved, AMS 20,
    formal_proof using lean4 at "https://github.com/KitaKen1/all-prime-residually-finite-p-groups/blob/main/lean/FCSolution.lean"]
theorem finitely_presented_burnside_problem :
    ∃ (G : Type) (inst : Group G),
      Infinite G ∧ @Group.IsFinitelyPresented G inst ∧
        (∀ g : G, ∃ m : ℕ, 0 < m ∧ g ^ m = 1) := by
  sorry

namespace variants

/-- Variant 1 adds residual finiteness to the periodic-group existence problem.
The answer is yes, as a consequence of [Ki26]. -/
@[category research solved, AMS 20,
    formal_proof using lean4 at "https://github.com/KitaKen1/all-prime-residually-finite-p-groups/blob/main/lean/FCSolution.lean"]
theorem finitely_presented_burnside_problem_residually_finite :
    ∃ (G : Type) (inst : Group G),
      Infinite G ∧ @Group.IsFinitelyPresented G inst ∧
        (∀ g : G, ∃ m : ℕ, 0 < m ∧ g ^ m = 1) ∧
        @Group.ResiduallyFinite G inst := by
  sorry

/-- Variant 2 asks for an infinite finitely presented residually finite
$p$-group for every prime $p$. The answer is yes [Ki26]. -/
@[category research solved, AMS 20,
    formal_proof using lean4 at "https://github.com/KitaKen1/all-prime-residually-finite-p-groups/blob/main/lean/FCSolution.lean"]
theorem finitely_presented_burnside_problem_all_primes :
    ∀ p : ℕ, p.Prime →
      ∃ (G : Type) (inst : Group G),
        Infinite G ∧ @Group.IsFinitelyPresented G inst ∧
          @Group.ResiduallyFinite G inst ∧ @IsPGroup p G inst := by
  sorry

end variants

end AllPrimeGroupsFC
