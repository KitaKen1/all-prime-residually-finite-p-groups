import AllPrimeGroups.CentralExtensionCharacters
import AllPrimeGroups.SignedFrameShapiro

/-! Character-valued H² classes on frame stabilizers and their two equal face restrictions. -/

namespace AllPrimeGroups
namespace Frames
noncomputable section
open CategoryTheory FrameBlocks FrameStabilizer FrameFaces

local instance (G A : Type*) [Group G] [Group A] : MulDistribMulAction G A :=
  CentralCocycles.trivialAction G A

variable {B K : Type} [Ring B] [Field K] (ε : B →+* K) {m l : ℕ}
  (hunit : ∀ b : B, ε b ≠ 0 → IsUnit b)

theorem standardFrameExtension_projection (hm : 5 ≤ m) (x : BlockCover (Fin l) m B) :
    (standardFrameExtension ε hunit hm).rightHom x =
      blockFrameStabilizerEquiv ε hunit hm (blockProjection x) := rfl

theorem standardFrameExtension_central (hm : 6 ≤ m) :
    (standardFrameExtension ε hunit (show 5 ≤ m by omega)).inl.range ≤
      Subgroup.center (BlockCover (Fin l) m B) := by
  intro x hx
  obtain ⟨z, rfl⟩ := hx
  apply blockKernel_central ε hunit hm
  apply MonoidHom.mem_ker.mp
  rw [← range_blockKernelInclusion]
  exact ⟨z, rfl⟩

theorem standard_firstCover_projection (hm : 5 ≤ m) (x : BlockCover (Fin 2) m B) :
    (standardFrameExtension ε hunit (show 5 ≤ m + 1 by omega)).rightHom (faceCover (0 : Fin 2) x) =
      firstActionFace ε hunit hm ((standardFrameExtension ε hunit hm).rightHom x) := by
  change frameStabilizerEquiv ε (toStabilizer (blockProjection (faceCover (0 : Fin 2) x))) =
    frameStabilizerEquiv ε (actualFace ε hunit hm (0 : Fin 2)
      ((frameStabilizerEquiv ε).symm (frameStabilizerEquiv ε (toStabilizer (blockProjection x)))))
  rw [MulEquiv.symm_apply_apply, actualFace_projection]

theorem standard_signedCover_projection (hm : 5 ≤ m) (x : BlockCover (Fin 2) m B) :
    (standardFrameExtension ε hunit (show 5 ≤ m + 1 by omega)).rightHom (signedPairCover x) =
      signedActionFace ε hunit hm ((standardFrameExtension ε hunit hm).rightHom x) := by
  change frameStabilizerEquiv ε (toStabilizer (blockProjection (signedPairCover x))) =
    frameStabilizerEquiv ε (actualSignedPair ε hunit hm
      ((frameStabilizerEquiv ε).symm (frameStabilizerEquiv ε (toStabilizer (blockProjection x)))))
  rw [MulEquiv.symm_apply_apply, actualSignedPair_projection]

theorem standard_face_lifts_agree_on_kernel (hm : 5 ≤ m) (x : BlockCover (Fin 2) m B)
    (hx : (standardFrameExtension ε hunit hm).rightHom x = 1) :
    faceCover (0 : Fin 2) x = signedPairCover x := by
  have hx' : x ∈ (standardFrameExtension ε hunit hm).inl.range := by
    rw [(standardFrameExtension ε hunit hm).range_inl_eq_ker_rightHom, MonoidHom.mem_ker]
    exact hx
  obtain ⟨z, rfl⟩ := hx'
  exact (signedPair_agrees_on_kernel z).symm

/-- The character pushforward of the standard multi-column extension. -/
def frameCharacterData (M : Type) [CommGroup M] (hm : 6 ≤ m)
    (χ : (Elementary.representation (n := m) (R := B)).ker →* M) :
    CentralCocycles.CharacterData
      (standardFrameExtension ε hunit (m := m) (l := l) (by omega)) χ :=
  CentralCocycles.characterData _ (standardFrameExtension_central ε hunit hm) χ
    (GroupExtension.normalizeSection (standardFrameExtension ε hunit (by omega)).surjInvRightHom)
    (GroupExtension.normalizeSection_one _)

def frameCharacterClass (M : Type) [CommGroup M] (hm : 6 ≤ m)
    (χ : (Elementary.representation (n := m) (R := B)).ker →* M) :
    groupCohomology (Rep.trivial ℤ (standardFrameStabilizer ε m l) (Additive M)) 2 :=
  (frameCharacterData ε hunit M hm χ).cocycle.cohomologyClass

/-- The first and normalized second faces pull a vertex character class to the same H² class. -/
theorem frameCharacterClass_faces (M : Type) [CommGroup M] (hm : 6 ≤ m)
    (χ : (Elementary.representation (n := m + 1) (R := B)).ker →* M) :
    groupCohomology.map (firstActionFace ε hunit (by omega))
        (Homogeneous.trivialRestriction (k := ℤ) (M := Additive M)
          (firstActionFace ε hunit (by omega))) 2
        (frameCharacterClass ε hunit M (m := m + 1) (l := 1) (by omega) χ) =
      groupCohomology.map (signedActionFace ε hunit (by omega))
        (Homogeneous.trivialRestriction (k := ℤ) (M := Additive M)
          (signedActionFace ε hunit (by omega))) 2
        (frameCharacterClass ε hunit M (m := m + 1) (l := 1) (by omega) χ) := by
  let S := standardFrameExtension ε hunit (m := m) (l := 2) (show 5 ≤ m by omega)
  let T := standardFrameExtension ε hunit (m := m + 1) (l := 1) (show 5 ≤ m + 1 by omega)
  let D := frameCharacterData ε hunit M (m := m + 1) (l := 1) (show 6 ≤ m + 1 by omega) χ
  exact D.pullback_class_eq T χ S.rightHom S.rightHom_surjective
    (firstActionFace ε hunit (by omega)) (signedActionFace ε hunit (by omega))
    (faceCover (0 : Fin 2)) signedPairCover
    (MonoidHom.ext (standard_firstCover_projection ε hunit (by omega)))
    (MonoidHom.ext (standard_signedCover_projection ε hunit (by omega)))
    (standard_face_lifts_agree_on_kernel ε hunit (by omega))

end
end Frames
end AllPrimeGroups
