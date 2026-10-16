import AllPrimeGroups.FrameShapiro
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree

/-! The degree-one vanishing input for the frame double complex.

Mathlib identifies H¹ with homomorphisms for trivial coefficients. The image of a perfect
group is perfect, and a commutative perfect group is trivial; no separate cocycle calculation
or divisibility hypothesis on the coefficients is needed. -/

namespace AllPrimeGroups
noncomputable section

/-- Every homomorphism from a perfect group to a commutative group is trivial. -/
theorem perfect_hom_eq_one {G A : Type*} [Group G] [CommGroup A] [Group.IsPerfect G]
    (f : G →* A) : f = 1 := by
  have : Group.IsPerfect f.range := Group.IsPerfect.range f
  ext g
  exact congrArg Subtype.val (Subsingleton.elim (⟨f g, ⟨g, rfl⟩⟩ : f.range) 1)

theorem perfect_addHom_eq_zero {G M : Type*} [Group G] [AddCommGroup M] [Group.IsPerfect G]
    (f : Additive G →+ M) : f = 0 := by
  apply AddMonoidHom.toMultiplicativeRight.injective
  exact perfect_hom_eq_one _

/-- Trivial coefficient H¹ vanishes on any perfect group. -/
theorem perfect_H1_subsingleton {G M : Type} [Group G] [AddCommGroup M] [Group.IsPerfect G] :
    Subsingleton (groupCohomology.H1 (Rep.trivial ℤ G M)) := by
  have : Subsingleton (Additive G →+ M) :=
    ⟨fun f g => (perfect_addHom_eq_zero f).trans (perfect_addHom_eq_zero g).symm⟩
  exact (groupCohomology.H1IsoOfIsTrivial (Rep.trivial ℤ G M)).toLinearEquiv.injective.subsingleton

namespace Frames
variable {B K M : Type} [Ring B] [Field K] [AddCommGroup M]
  (ε : B →+* K) {m l : ℕ} (hunit : ∀ b : B, ε b ≠ 0 → IsUnit b)

include hunit

/-- H¹ of each standard multi-column stabilizer is zero once its free rank is at least five. -/
theorem standardFrameStabilizer_H1_subsingleton (hm : 5 ≤ m) :
    Subsingleton (groupCohomology.H1 (Rep.trivial ℤ (standardFrameStabilizer ε m l) M)) := by
  have := standardFrameStabilizer_isPerfect ε hunit (l := l) hm
  exact perfect_H1_subsingleton

/-- Shapiro transfers the vanishing to the coefficient columns of the frame double complex. -/
theorem frameCoefficient_H1_subsingleton (σ : K →+* B) (hs : ε.comp σ = RingHom.id K)
    (hnil : ∀ A : Matrix (Fin (m + l)) (Fin (m + l)) B,
      ε.mapMatrix A = 0 → IsNilpotent A) (hm : 5 ≤ m) :
    Subsingleton (groupCohomology (frameCoefficients ε M (m + l) l) 1) := by
  have := standardFrameStabilizer_H1_subsingleton (M := M) ε hunit (l := l) hm
  exact (frameShapiroIso (M := M) ε σ hs hnil hunit (by omega) 1).toLinearEquiv.injective.subsingleton

end Frames
end
end AllPrimeGroups
