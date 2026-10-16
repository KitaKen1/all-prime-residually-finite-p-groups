import AllPrimeGroups.FrameShapiro
import AllPrimeGroups.FrameLowDegree
import AllPrimeGroups.PrimeFrameTransitivity

/-! Shapiro for the all-prime algebras, with all ring-theoretic hypotheses discharged. -/

namespace AllPrimeGroups
namespace PrimeAlgebra
noncomputable section
open CategoryTheory Frames

variable (p : ℕ) (hp : p.Prime) [Fact p.Prime]

/-- Frame-function cohomology is stabilizer cohomology for every short frame length. -/
def frameCoefficientShapiroIso (M : Type) [AddCommGroup M] {m l : ℕ}
    (hm : 0 < m) (q : ℕ) :
    groupCohomology (frameCoefficients (augmentation p hp) M (m + l) l) q ≅
      groupCohomology (Rep.trivial ℤ (standardFrameStabilizer (augmentation p hp) m l) M) q :=
  frameShapiroIso (augmentation p hp) (algebraMap (ZMod p) (R p hp))
    (augmentation_split p hp) (matrix_nil p hp (m + l)) (unit_of_augmentation_ne_zero p hp) hm q

theorem frameCoefficientShapiroIso_hom (M : Type) [AddCommGroup M] {m l : ℕ}
    (hm : 0 < m) (q : ℕ) :
    (frameCoefficientShapiroIso p hp M (m := m) (l := l) hm q).hom =
      groupCohomology.map (standardFrameStabilizer (augmentation p hp) m l).subtype
        (standardEvaluation (M := M) (augmentation p hp)) q :=
  frameShapiroIso_hom (augmentation p hp) (algebraMap (ZMod p) (R p hp))
    (augmentation_split p hp) (matrix_nil p hp (m + l)) (unit_of_augmentation_ne_zero p hp) hm q

/-- In R(p), the first cohomological face is the descended block-cover face. -/
theorem firstFrameFaceShapiro_naturality (M : Type) [AddCommGroup M] {m : ℕ}
    (hm : 5 ≤ m) (q : ℕ) :
    groupCohomology.map (MonoidHom.id (K1.E (m + 2) (R p hp)))
        (frameFacePullback (augmentation p hp) M (n := m + 2) (0 : Fin 2)) q ≫
        (frameCoefficientShapiroIso p hp M (m := m) (l := 2) (by omega) q).hom =
      (frameCoefficientShapiroIso p hp M (m := m + 1) (l := 1) (by omega) q).hom ≫
        groupCohomology.map
          (firstActionFace (augmentation p hp) (unit_of_augmentation_ne_zero p hp) hm)
          (Homogeneous.trivialRestriction (k := ℤ) (M := M)
            (firstActionFace (augmentation p hp) (unit_of_augmentation_ne_zero p hp) hm)) q :=
  firstActionFaceShapiro_naturality (augmentation p hp) (algebraMap (ZMod p) (R p hp))
    (augmentation_split p hp) (unit_of_augmentation_ne_zero p hp) (matrix_nil p hp (m + 2)) hm q

/-- The H¹ column needed in the low-degree chase vanishes for the concrete coefficient ring. -/
theorem frameCoefficient_H1_subsingleton (M : Type) [AddCommGroup M] {m l : ℕ}
    (hm : 5 ≤ m) :
    Subsingleton (groupCohomology (frameCoefficients (augmentation p hp) M (m + l) l) 1) :=
  Frames.frameCoefficient_H1_subsingleton (augmentation p hp) (unit_of_augmentation_ne_zero p hp)
    (algebraMap (ZMod p) (R p hp)) (augmentation_split p hp) (matrix_nil p hp (m + l)) hm

end
end PrimeAlgebra
end AllPrimeGroups
