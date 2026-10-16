import Mathlib.Algebra.Algebra.Hom
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.RingTheory.LocalRing.Defs

namespace AllPrimeGroups

variable {K R : Type*} [Field K] [Ring R] [Algebra K R]

/-- The unit criterion for a field-augmented algebra with nil augmentation kernel.
The coefficient algebra need not be commutative. -/
theorem isUnit_iff_augmentation_ne_zero (ε : R →ₐ[K] K)
    (hnil : ∀ a : R, ε a = 0 → IsNilpotent a) (a : R) :
    IsUnit a ↔ ε a ≠ 0 := by
  constructor
  · intro h
    exact (h.map ε.toRingHom).ne_zero
  · intro ha
    let u := algebraMap K R (ε a)⁻¹
    have hu : IsUnit u := (isUnit_iff_ne_zero.mpr (inv_ne_zero ha)).map (algebraMap K R)
    have hn : IsNilpotent (u * a - 1) := hnil _ (by
      simp [u, map_sub, map_mul, AlgHom.commutes, ha])
    have hua : IsUnit (u * a) := by simpa only [sub_add_cancel] using hn.isUnit_add_one
    obtain ⟨U, hU⟩ := hu
    exact (Units.isUnit_units_mul U a).mp (by simpa only [hU] using hua)

/-- The same hypotheses make the algebra a local ring in mathlib's noncommutative sense. -/
theorem isLocalRing_of_nil_augmentation (ε : R →ₐ[K] K)
    (hnil : ∀ a : R, ε a = 0 → IsNilpotent a) : IsLocalRing R := by
  let : Nontrivial R := ε.toRingHom.domain_nontrivial
  refine { isUnit_or_isUnit_of_add_one := ?_ }
  intro a b hab
  by_cases ha : ε a = 0
  · right
    apply (isUnit_iff_augmentation_ne_zero ε hnil b).mpr
    have hb : ε b = 1 := by
      have h := congrArg ε hab
      simpa only [map_add, ha, zero_add, map_one] using h
    rw [hb]
    exact one_ne_zero
  · exact Or.inl ((isUnit_iff_augmentation_ne_zero ε hnil a).mpr ha)

/-- A strong form of right stable range one: every right-unimodular pair
can be reduced to a unit. This is an input condition, not K₂ stability itself. -/
def UnitStableRangeOne (R : Type*) [Ring R] : Prop :=
  ∀ a b x y : R, a * x + b * y = 1 → ∃ t : R, IsUnit (a + b * t)

theorem unitStableRangeOne_of_nil_augmentation (ε : R →ₐ[K] K)
    (hnil : ∀ a : R, ε a = 0 → IsNilpotent a) : UnitStableRangeOne R := by
  intro a b x y hxy
  by_cases ha : ε a = 0
  · have hb : ε b ≠ 0 := by
      intro hb
      have h := congrArg ε hxy
      simp [map_add, map_mul, ha, hb] at h
    refine ⟨1, (isUnit_iff_augmentation_ne_zero ε hnil _).mpr ?_⟩
    simpa [map_add, map_mul, ha] using hb
  · exact ⟨0, by simpa using (isUnit_iff_augmentation_ne_zero ε hnil a).mpr ha⟩

end AllPrimeGroups
