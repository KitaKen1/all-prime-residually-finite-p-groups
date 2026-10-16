import FCSolution

#print axioms AllPrimeGroupsFC.finitely_presented_burnside_problem
#print axioms AllPrimeGroupsFC.variants.finitely_presented_burnside_problem_residually_finite
#print axioms AllPrimeGroupsFC.variants.finitely_presented_burnside_problem_all_primes
#print axioms AllPrimeGroupsFC.all_prime_groups
#print axioms AllPrimeGroupsFC.concrete_groups

#check (AllPrimeGroupsFC.finitely_presented_burnside_problem :
  ∃ (G : Type) (inst : Group G),
    Infinite G ∧ @Group.IsFinitelyPresented G inst ∧
      (∀ g : G, ∃ m : ℕ, 0 < m ∧ g ^ m = 1))

#check (AllPrimeGroupsFC.variants.finitely_presented_burnside_problem_residually_finite :
  ∃ (G : Type) (inst : Group G),
    Infinite G ∧ @Group.IsFinitelyPresented G inst ∧
      (∀ g : G, ∃ m : ℕ, 0 < m ∧ g ^ m = 1) ∧
      @Group.ResiduallyFinite G inst)

#check (AllPrimeGroupsFC.variants.finitely_presented_burnside_problem_all_primes :
  ∀ p : ℕ, p.Prime → ∃ (G : Type) (inst : Group G),
    Infinite G ∧ @Group.IsFinitelyPresented G inst ∧
      @Group.ResiduallyFinite G inst ∧ @IsPGroup p G inst)

#check (AllPrimeGroupsFC.all_prime_groups :
  ∀ p : ℕ, p.Prime → ∃ (G : Type) (inst : Group G),
    Infinite G ∧ @Group.IsFinitelyPresented G inst ∧
      @Group.ResiduallyFinite G inst ∧ @IsPGroup p G inst)
