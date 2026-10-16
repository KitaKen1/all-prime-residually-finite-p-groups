import AllPrimeGroups.FrameShapiro
import AllPrimeGroups.CohomologyConjugation

/-! The second ordered-pair face under Shapiro in degree two.

The signed swap moves its standard vertex to the chosen standard vertex. Its group conjugation
and coefficient action are retained together, then the explicit H² inner-conjugation homotopy
removes them. The normalized point map itself need not be equivariant. -/

namespace AllPrimeGroups
namespace Frames
noncomputable section
open CategoryTheory CohomologyConjugation FrameFaces

variable {B K M : Type} [Ring B] [Field K] [AddCommGroup M]
  (ε : B →+* K) {m : ℕ}

theorem signedSecondLengthFace_standardFrame :
    pairNormalizer m B • lengthFace ε (1 : Fin 2) (standardLengthFrame ε m 2) =
      standardLengthFrame ε (m + 1) 1 :=
  Subtype.ext (signedSecondFace_standardFrame ε)

variable (σ : K →+* B) (hs : ε.comp σ = RingHom.id K)
  (hnil : ∀ A : Matrix (Fin (m + 2)) (Fin (m + 2)) B, ε.mapMatrix A = 0 → IsNilpotent A)
  (hunit : ∀ b : B, ε b ≠ 0 → IsUnit b)

/-- The second face becomes restriction along the signed, descended block-cover face in H². -/
theorem signedSecondFaceShapiro_naturality (hm : 5 ≤ m) :
    groupCohomology.map (MonoidHom.id (K1.E (m + 2) B))
        (frameFacePullback ε M (n := m + 2) (1 : Fin 2)) 2 ≫
        (frameShapiroIso ε σ hs hnil hunit (by omega) 2).hom =
      (frameShapiroIso ε σ hs hnil hunit (m := m + 1) (l := 1) (by omega) 2).hom ≫
        groupCohomology.map (signedActionFace ε hunit hm)
          (Homogeneous.trivialRestriction (k := ℤ) (M := M) (signedActionFace ε hunit hm)) 2 := by
  rw [frameShapiroIso_hom, frameShapiroIso_hom, ← groupCohomology.map_comp,
    ← groupCohomology.map_comp]
  let φ : Rep.res (standardFrameStabilizer ε m 2).subtype
      (frameCoefficients ε M (m + 2) 1) ⟶ Rep.trivial ℤ (standardFrameStabilizer ε m 2) M :=
    (Rep.resFunctor (standardFrameStabilizer ε m 2).subtype).map
      (frameFacePullback ε M (n := m + 2) (1 : Fin 2)) ≫ standardEvaluation ε
  have hc := conjugate_map_H2 (frameCoefficients ε M (m + 2) 1)
    (standardFrameStabilizer ε m 2).subtype φ (pairNormalizer m B)⁻¹
  change groupCohomology.map (standardFrameStabilizer ε m 2).subtype φ 2 = _
  rw [← hc]
  apply groupCohomology.map_congr
  · apply MonoidHom.ext
    intro s
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    change pairNormalizer m B * s.val * (pairNormalizer m B)⁻¹ = (signedActionFace ε hunit hm s).val
    exact (signedActionFace_conjugation ε hunit hm s).symm
  · ext f
    change f ((pairNormalizer m B)⁻¹⁻¹ •
      lengthFace ε (1 : Fin 2) (standardLengthFrame ε m 2)) =
        f (standardLengthFrame ε (m + 1) 1)
    rw [inv_inv, signedSecondLengthFace_standardFrame]

end
end Frames
end AllPrimeGroups
