import AllPrimeGroups.FrameCharacterCocycle
import AllPrimeGroups.PrimeFrameShapiro

/-! The signed second face and the initial character-valued horizontal H² cycle for R(p). -/

namespace AllPrimeGroups
namespace PrimeAlgebra
noncomputable section
open CategoryTheory Frames

variable (p : ℕ) (hp : p.Prime) [Fact p.Prime]

/-- The signed second face has the required H² Shapiro naturality for the concrete algebra. -/
theorem secondFrameFaceShapiro_naturality (M : Type) [AddCommGroup M] {m : ℕ}
    (hm : 5 ≤ m) :
    groupCohomology.map (MonoidHom.id (K1.E (m + 2) (R p hp)))
        (frameFacePullback (augmentation p hp) M (n := m + 2) (1 : Fin 2)) 2 ≫
        (frameCoefficientShapiroIso p hp M (m := m) (l := 2) (by omega) 2).hom =
      (frameCoefficientShapiroIso p hp M (m := m + 1) (l := 1) (by omega) 2).hom ≫
        groupCohomology.map
          (signedActionFace (augmentation p hp) (unit_of_augmentation_ne_zero p hp) hm)
          (Homogeneous.trivialRestriction (k := ℤ) (M := M)
            (signedActionFace (augmentation p hp) (unit_of_augmentation_ne_zero p hp) hm)) 2 :=
  signedSecondFaceShapiro_naturality (augmentation p hp) (algebraMap (ZMod p) (R p hp))
    (augmentation_split p hp) (matrix_nil p hp (m + 2)) (unit_of_augmentation_ne_zero p hp) hm

/-- A character of the one-column-cover kernel gives an ambient frame-coefficient H² class. -/
def frameCharacterCycle (M : Type) [CommGroup M] {m : ℕ} (hm : 6 ≤ m)
    (χ : (Elementary.representation (n := m + 1) (R := R p hp)).ker →* M) :
    groupCohomology (frameCoefficients (augmentation p hp) (Additive M) (m + 2) 1) 2 :=
  frameCharacterPreclass (augmentation p hp) (algebraMap (ZMod p) (R p hp))
    (augmentation_split p hp) (matrix_nil p hp (m + 2)) (unit_of_augmentation_ne_zero p hp) hm χ

/-- The first and second coefficient faces agree on the concrete character class. -/
theorem frameCharacterCycle_faces (M : Type) [CommGroup M] {m : ℕ} (hm : 6 ≤ m)
    (χ : (Elementary.representation (n := m + 1) (R := R p hp)).ker →* M) :
    groupCohomology.map (MonoidHom.id (K1.E (m + 2) (R p hp)))
        (frameFacePullback (augmentation p hp) (Additive M) (n := m + 2) (0 : Fin 2)) 2
        (frameCharacterCycle p hp M hm χ) =
      groupCohomology.map (MonoidHom.id (K1.E (m + 2) (R p hp)))
        (frameFacePullback (augmentation p hp) (Additive M) (n := m + 2) (1 : Fin 2)) 2
        (frameCharacterCycle p hp M hm χ) :=
  frameCharacterPreclass_faces (augmentation p hp) (algebraMap (ZMod p) (R p hp))
    (augmentation_split p hp) (matrix_nil p hp (m + 2)) (unit_of_augmentation_ne_zero p hp) hm χ

end
end PrimeAlgebra
end AllPrimeGroups
