import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.ResiduallyFinite

namespace AllPrimeGroups

/-- The final arithmetic step of stable separation. -/
theorem eq_one_of_coprime_powers {G : Type*} [Group G] (g : G) {a b : ℕ}
    (h : a.Coprime b) (ha : g ^ a = 1) (hb : g ^ b = 1) : g = 1 := by
  apply orderOf_eq_one_iff.mp
  apply Nat.dvd_one.mp
  have hd := Nat.dvd_gcd (orderOf_dvd_iff_pow_eq_one.mpr ha)
    (orderOf_dvd_iff_pow_eq_one.mpr hb)
  simpa only [h.gcd_eq_one] using hd

/-- Reduces separation to the two power identities for the SAME group element.
This theorem does not establish either identity for the constructed Steinberg group. -/
theorem separated_of_prime_power_and_cyclic_detection
    {G : Type*} [Group G] (p : ℕ) (g : G)
    (htorsion : ∃ a : ℕ, g ^ (p ^ a) = 1)
    (hphase : ∃ ℓ : ℕ, ℓ.Coprime p ∧ g ^ ℓ = 1) : g = 1 := by
  obtain ⟨a, ha⟩ := htorsion
  obtain ⟨ℓ, hℓ, hgℓ⟩ := hphase
  exact eq_one_of_coprime_powers g (hℓ.symm.pow_left a) ha hgℓ

/-- Converts an already proved separating family of finite quotients to mathlib's standard
residual-finiteness predicate. The separation hypothesis is explicit. -/
theorem residuallyFinite_of_separating_family {G : Type*} [Group G]
    {ι : Type*} {Q : ι → Type*} [∀ i, Group (Q i)] [∀ i, Finite (Q i)]
    (q : ∀ i, G →* Q i)
    (hseparate : ∀ g, (∀ i, q i g = 1) → g = 1) : Group.ResiduallyFinite G := by
  classical
  apply Group.residuallyFinite_of_forall_exists_finite_monoidHom
  intro g hg
  have hex : ∃ i, q i g ≠ 1 := by
    by_contra h
    exact hg (hseparate g (by simpa using h))
  obtain ⟨i, hi⟩ := hex
  exact ⟨Q i, inferInstance, inferInstance, q i, hi⟩

end AllPrimeGroups
