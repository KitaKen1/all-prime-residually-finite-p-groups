import Challenge

/-! Independent Comparator reference for the three expanded FC statements.
The shared proposition definitions in Challenge import only Mathlib.
The proposed solution is not part of this reference. The aliases ensure that
the reference and solution have identical types, including constant names.
The three `sorry` placeholders occur only in this trusted challenge file. -/

namespace AllPrimeGroupsFC

theorem finitely_presented_burnside_problem :
    AllPrimeGroupsChallenge.MainStatement := by
  sorry

namespace variants

theorem finitely_presented_burnside_problem_residually_finite :
    AllPrimeGroupsChallenge.ResiduallyFinitePeriodicStatement := by
  sorry

theorem finitely_presented_burnside_problem_all_primes :
    AllPrimeGroupsChallenge.Statement := by
  sorry

end variants

end AllPrimeGroupsFC
