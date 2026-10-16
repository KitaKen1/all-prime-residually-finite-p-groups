import Mathlib.GroupTheory.FinitelyPresentedGroup
import Mathlib.GroupTheory.ResiduallyFinite
import Mathlib.GroupTheory.PGroup

/-! Independent reference statements for the original Burnside problem and two variants.
The original problem is the abstract-group conclusion of OpenAI's `PeriodicGroup`
challenge. The all-prime variant uses Mathlib's standard group predicates.
This file does not import the proposed proof or define substitute predicates. -/

namespace AllPrimeGroupsChallenge

/-- The original finitely presented Burnside problem, in abstract-group form. -/
def MainStatement : Prop :=
  ∃ (G : Type) (inst : Group G),
    Infinite G ∧ @Group.IsFinitelyPresented G inst ∧
      (∀ g : G, ∃ m : ℕ, 0 < m ∧ g ^ m = 1)

/-- Variant 1: an infinite finitely presented residually finite periodic group exists. -/
def ResiduallyFinitePeriodicStatement : Prop :=
  ∃ (G : Type) (inst : Group G),
    Infinite G ∧ @Group.IsFinitelyPresented G inst ∧
      (∀ g : G, ∃ m : ℕ, 0 < m ∧ g ^ m = 1) ∧
      @Group.ResiduallyFinite G inst

/-- Variant 2: the all-prime residually finite p-group existence statement. -/
def Statement : Prop :=
  ∀ p : ℕ, p.Prime →
    ∃ (G : Type) (inst : Group G),
      Infinite G ∧ @Group.IsFinitelyPresented G inst ∧
        @Group.ResiduallyFinite G inst ∧ @IsPGroup p G inst

end AllPrimeGroupsChallenge
