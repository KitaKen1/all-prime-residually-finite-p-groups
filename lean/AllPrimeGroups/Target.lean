import Mathlib.GroupTheory.FinitelyPresentedGroup
import Mathlib.GroupTheory.ResiduallyFinite
import Mathlib.GroupTheory.PGroup

/-! The intended theorem, stated using the standard mathlib predicates.
This file defines the goal; it does not claim to prove it. -/

namespace AllPrimeGroups

def Target : Prop :=
  ∀ p : ℕ, p.Prime →
    ∃ (G : Type) (inst : Group G),
      Infinite G ∧ @Group.IsFinitelyPresented G inst ∧
        @Group.ResiduallyFinite G inst ∧ @IsPGroup p G inst

end AllPrimeGroups
