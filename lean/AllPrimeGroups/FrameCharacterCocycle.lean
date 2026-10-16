import AllPrimeGroups.FrameCharacterClasses

/-! The initial horizontal H² cycle for the low-degree frame argument.

A character of the vertex-cover kernel determines a vertex-stabilizer H² class. Pulling it
back through Shapiro gives a frame-coefficient class. Its two face images agree by the actual
cover lifts and the signed second-face conjugation calculation. No extension to the ambient
group has yet been constructed. -/

namespace AllPrimeGroups
namespace Frames
noncomputable section
open CategoryTheory

/-- Transport equality across two commuting squares of module isomorphisms. -/
theorem equal_preimages_of_squares {R : Type*} [Ring R] {A B C D : ModuleCat R}
    (e : A ≅ C) (f : B ≅ D) (u v : A ⟶ B) (r s : C ⟶ D)
    (hu : u ≫ f.hom = e.hom ≫ r) (hv : v ≫ f.hom = e.hom ≫ s)
    (x : C) (hx : r x = s x) : u (e.inv x) = v (e.inv x) := by
  apply f.toLinearEquiv.injective
  have h₀ := congrArg (fun q => q.hom (e.inv x)) hu
  have h₁ := congrArg (fun q => q.hom (e.inv x)) hv
  have he : e.hom (e.inv x) = x := e.toLinearEquiv.apply_symm_apply x
  change f.hom (u (e.inv x)) = r (e.hom (e.inv x)) at h₀
  change f.hom (v (e.inv x)) = s (e.hom (e.inv x)) at h₁
  rw [he] at h₀ h₁
  exact h₀.trans (hx.trans h₁.symm)

variable {B K M : Type} [Ring B] [Field K] [CommGroup M]
  (ε : B →+* K) {m : ℕ} (σ : K →+* B) (hs : ε.comp σ = RingHom.id K)
  (hnil : ∀ A : Matrix (Fin (m + 2)) (Fin (m + 2)) B, ε.mapMatrix A = 0 → IsNilpotent A)
  (hunit : ∀ b : B, ε b ≠ 0 → IsUnit b)

/-- The character class read on all vertex coefficient functions. -/
def frameCharacterPreclass (hm : 6 ≤ m)
    (χ : (Elementary.representation (n := m + 1) (R := B)).ker →* M) :
    groupCohomology (frameCoefficients ε (Additive M) (m + 2) 1) 2 :=
  (frameShapiroIso ε σ hs hnil hunit (m := m + 1) (l := 1) (by omega) 2).inv
    (frameCharacterClass ε hunit M (m := m + 1) (l := 1) (by omega) χ)

set_option backward.isDefEq.respectTransparency false in
/-- The character class is a horizontal cycle in H² of the frame coefficient complex. -/
theorem frameCharacterPreclass_faces (hm : 6 ≤ m)
    (χ : (Elementary.representation (n := m + 1) (R := B)).ker →* M) :
    groupCohomology.map (MonoidHom.id (K1.E (m + 2) B))
        (frameFacePullback ε (Additive M) (n := m + 2) (0 : Fin 2)) 2
        (frameCharacterPreclass ε σ hs hnil hunit hm χ) =
      groupCohomology.map (MonoidHom.id (K1.E (m + 2) B))
        (frameFacePullback ε (Additive M) (n := m + 2) (1 : Fin 2)) 2
        (frameCharacterPreclass ε σ hs hnil hunit hm χ) := by
  exact equal_preimages_of_squares
    (frameShapiroIso ε σ hs hnil hunit (m := m + 1) (l := 1) (by omega) 2)
    (frameShapiroIso ε σ hs hnil hunit (m := m) (l := 2) (by omega) 2)
    _ _ _ _
    (firstActionFaceShapiro_naturality (M := Additive M) ε σ hs hunit hnil (by omega) 2)
    (signedSecondFaceShapiro_naturality (M := Additive M) ε σ hs hnil hunit (by omega))
    (frameCharacterClass ε hunit M (m := m + 1) (l := 1) (by omega) χ)
    (frameCharacterClass_faces ε hunit M hm χ)

end
end Frames
end AllPrimeGroups
