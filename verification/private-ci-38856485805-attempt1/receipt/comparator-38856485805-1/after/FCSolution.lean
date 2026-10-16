import Challenge
import AllPrimeGroups.PrimeGroups
import OAI.GroupTheory.PeriodicGroups.Main

/-! Proof connections for the original Burnside problem and its two variants. -/

namespace AllPrimeGroupsFC

/-- The original problem, reusing OpenAI's proved abstract-group conclusion. -/
theorem finitely_presented_burnside_problem : AllPrimeGroupsChallenge.MainStatement :=
  OAI.SourceBurnside.thm_main.2

namespace variants

/-- Variant 1, obtained from the all-prime theorem at the prime two. -/
theorem finitely_presented_burnside_problem_residually_finite :
    AllPrimeGroupsChallenge.ResiduallyFinitePeriodicStatement := by
  obtain ⟨G, inst, hInfinite, hFP, hRF, hP⟩ :=
    AllPrimeGroups.all_prime_groups 2 Nat.prime_two
  let : Group G := inst
  refine ⟨G, inst, hInfinite, hFP, ?_, hRF⟩
  intro g
  obtain ⟨k, hk⟩ := hP g
  exact ⟨2 ^ k, pow_pos (by decide : 0 < (2 : ℕ)) k, hk⟩

/-- Variant 2, the stronger all-prime result proved by this repository. -/
theorem finitely_presented_burnside_problem_all_primes : AllPrimeGroupsChallenge.Statement :=
  AllPrimeGroups.all_prime_groups

end variants

/-- The existing descriptive name for the all-prime variant. -/
theorem all_prime_groups : AllPrimeGroupsChallenge.Statement :=
  variants.finitely_presented_burnside_problem_all_primes

theorem concrete_groups (p : ℕ) (hp : p.Prime) {n : ℕ} (hn : 7 ≤ n) :
    Infinite (AllPrimeGroups.PrimeGroups.G p hp n) ∧
      Group.IsFinitelyPresented (AllPrimeGroups.PrimeGroups.G p hp n) ∧
      Group.ResiduallyFinite (AllPrimeGroups.PrimeGroups.G p hp n) ∧
      IsPGroup p (AllPrimeGroups.PrimeGroups.G p hp n) :=
  AllPrimeGroups.PrimeGroups.properties p hp hn

end AllPrimeGroupsFC
