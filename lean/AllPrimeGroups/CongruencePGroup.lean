import Mathlib.Algebra.CharP.Lemmas
import Mathlib.GroupTheory.PGroup
import Mathlib.RingTheory.Nilpotent.Basic

namespace AllPrimeGroups

theorem one_add_nilpotent_pow_prime {p : ℕ} (hp : p.Prime)
    {A : Type*} [Ring A] [CharP A p] {a : A} (ha : IsNilpotent a) :
    ∃ k : ℕ, (1 + a) ^ (p ^ k) = 1 := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨r, hr⟩ := ha
  have hbound : r ≤ p ^ r :=
    (Nat.lt_two_pow_self (n := r)).le.trans (Nat.pow_le_pow_left hp.two_le r)
  refine ⟨r, ?_⟩
  rw [add_pow_char_pow_of_commute p r (Commute.one_left a), one_pow,
    pow_eq_zero_of_le hbound hr, add_zero]

/-- The matrix part of the desired congruence subgroup is already a p-group.
The additional Steinberg kernel must still be treated separately. -/
theorem units_congruence_isPGroup {p : ℕ} (hp : p.Prime)
    {A B : Type*} [Ring A] [Ring B] [CharP A p] (ε : A →+* B)
    (hnil : ∀ a : A, ε a = 0 → IsNilpotent a) :
    IsPGroup p (Units.map ε.toMonoidHom).ker := by
  intro g
  have hg : ε (g.val.val) = 1 := congrArg Units.val g.property
  have ha : IsNilpotent (g.val.val - 1) := hnil _ (by rw [map_sub, hg, map_one, sub_self])
  obtain ⟨k, hk⟩ := one_add_nilpotent_pow_prime hp ha
  refine ⟨k, Subtype.ext (Units.ext ?_)⟩
  change g.val.val ^ (p ^ k) = 1
  rw [add_comm 1, sub_add_cancel] at hk
  exact hk

end AllPrimeGroups
