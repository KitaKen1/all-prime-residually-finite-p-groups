import AllPrimeGroups.FrameCochains
import AllPrimeGroups.HomogeneousShapiro

/-! Shapiro for frame coefficient functions and the first face of an ordered pair. -/

namespace AllPrimeGroups
namespace Frames
noncomputable section
open CategoryTheory QuotientGroup

variable {B K M : Type} [Ring B] [Field K] [AddCommGroup M]
  (ε : B →+* K) {m l : ℕ}

/-- The standard frame is fixed by its actual stabilizer, so evaluation is equivariant. -/
def standardEvaluation :
    Rep.res (standardFrameStabilizer ε m l).subtype (frameCoefficients ε M (m + l) l) ⟶
      Rep.trivial ℤ (standardFrameStabilizer ε m l) M :=
  Rep.ofHom ⟨LinearMap.proj (standardLengthFrame ε m l), fun g => by
    ext f
    change f (g.val⁻¹ • standardLengthFrame ε m l) = f (standardLengthFrame ε m l)
    apply congrArg f
    apply Subtype.ext
    exact MulAction.mem_stabilizer_iff.mp (g⁻¹).property⟩

@[simp] theorem standardEvaluation_apply (f : LengthFrame ε (m + l) l → M) :
    (standardEvaluation (M := M) ε).hom f = f (standardLengthFrame ε m l) := rfl

variable (σ : K →+* B) (hs : ε.comp σ = RingHom.id K)
  (hnil : ∀ A : Matrix (Fin (m + l)) (Fin (m + l)) B, ε.mapMatrix A = 0 → IsNilpotent A)
  (hunit : ∀ b : B, ε b ≠ 0 → IsUnit b)

/-- All-degree Shapiro with the actual standard frame stabilizer. -/
def frameShapiroIso (hm : 0 < m) (q : ℕ) :
    groupCohomology (frameCoefficients ε M (m + l) l) q ≅
      groupCohomology (Rep.trivial ℤ (standardFrameStabilizer ε m l) M) q :=
  Homogeneous.orbitShapiroIso _ (frameQuotientEquiv ε σ hs hnil hunit hm)
    (frameQuotientEquiv_equivariant ε σ hs hnil hunit hm) q

theorem frameShapiroIso_hom (hm : 0 < m) (q : ℕ) :
    (frameShapiroIso (M := M) ε σ hs hnil hunit hm q).hom =
      groupCohomology.map (standardFrameStabilizer ε m l).subtype (standardEvaluation ε) q := by
  rw [frameShapiroIso, Homogeneous.orbitShapiroIso_hom]
  apply groupCohomology.map_congr rfl
  ext f
  change f (frameQuotientEquiv ε σ hs hnil hunit hm (QuotientGroup.mk (1 : K1.E (m + l) B)⁻¹)) =
    f (standardLengthFrame ε m l)
  rw [inv_one, frameQuotientEquiv_mk, one_smul]

/-- Forgetting the first vector includes the pair stabilizer in the last-vector stabilizer. -/
theorem firstFaceStabilizer_le :
    standardFrameStabilizer ε m 2 ≤ standardFrameStabilizer ε (m + 1) 1 := by
  intro g hg
  apply MulAction.mem_stabilizer_iff.mpr
  rw [← firstFace_standardFrame, ← face_elementaryFrame_smul,
    MulAction.mem_stabilizer_iff.mp hg]

theorem firstActionFace_eq_inclusion (hm : 5 ≤ m) :
    firstActionFace ε hunit hm = Subgroup.inclusion (firstFaceStabilizer_le ε) := by
  apply MonoidHom.ext
  intro g
  exact Subtype.ext (firstActionFace_inclusion ε hunit hm g)

/-- On frame coefficients the first face becomes the actual inclusion of stabilizers. -/
theorem firstFaceShapiro_naturality
    (hnilPair : ∀ A : Matrix (Fin (m + 2)) (Fin (m + 2)) B,
      ε.mapMatrix A = 0 → IsNilpotent A) (hm : 0 < m) (q : ℕ) :
    groupCohomology.map (MonoidHom.id (K1.E (m + 2) B))
        (frameFacePullback ε M (n := m + 2) (0 : Fin 2)) q ≫
        (frameShapiroIso ε σ hs hnilPair hunit hm q).hom =
      (frameShapiroIso ε σ hs hnilPair hunit (m := m + 1) (l := 1) (by omega) q).hom ≫
        groupCohomology.map (Subgroup.inclusion (firstFaceStabilizer_le ε))
          (Homogeneous.trivialRestriction (k := ℤ) (M := M)
            (Subgroup.inclusion (firstFaceStabilizer_le ε))) q := by
  rw [frameShapiroIso_hom, frameShapiroIso_hom, ← groupCohomology.map_comp,
    ← groupCohomology.map_comp]
  apply groupCohomology.map_congr rfl
  ext f
  change f (lengthFace ε (0 : Fin 2) (standardLengthFrame ε m 2)) =
    f (standardLengthFrame ε (m + 1) 1)
  exact congrArg f (Subtype.ext (firstFace_standardFrame ε))

/-- The same formula uses the previously constructed block-cover face after descent. -/
theorem firstActionFaceShapiro_naturality
    (hnilPair : ∀ A : Matrix (Fin (m + 2)) (Fin (m + 2)) B,
      ε.mapMatrix A = 0 → IsNilpotent A) (hm : 5 ≤ m) (q : ℕ) :
    groupCohomology.map (MonoidHom.id (K1.E (m + 2) B))
        (frameFacePullback ε M (n := m + 2) (0 : Fin 2)) q ≫
        (frameShapiroIso ε σ hs hnilPair hunit (by omega) q).hom =
      (frameShapiroIso ε σ hs hnilPair hunit (m := m + 1) (l := 1) (by omega) q).hom ≫
        groupCohomology.map (firstActionFace ε hunit hm)
          (Homogeneous.trivialRestriction (k := ℤ) (M := M) (firstActionFace ε hunit hm)) q := by
  rw [firstActionFace_eq_inclusion ε hunit hm]
  exact firstFaceShapiro_naturality (M := M) ε σ hs hunit hnilPair (by omega) q

end
end Frames
end AllPrimeGroups
