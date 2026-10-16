import AllPrimeGroups.FrameH2Lift
import AllPrimeGroups.PrimeFrameCharacterClasses

/-! Constant-coefficient lifts of the character classes for R(p).
All horizontal exactness, orbit, H¹ and sign-sum inputs of the low-degree argument are discharged. -/

namespace AllPrimeGroups
noncomputable section
open CategoryTheory

set_option backward.isDefEq.respectTransparency false in
theorem cohomology_map_sub {k G : Type} [CommRing k] [Group G] {A D : Rep k G}
    (u v : A ⟶ D) (q : ℕ) :
    groupCohomology.map (MonoidHom.id G) (u - v) q =
      groupCohomology.map (MonoidHom.id G) u q - groupCohomology.map (MonoidHom.id G) v q := by
  change _root_.HomologicalComplex.homologyMap ((groupCohomology.cochainsFunctor k G).map (u - v)) q = _
  rw [Functor.map_sub, _root_.HomologicalComplex.homologyMap_sub]
  rfl

namespace Frames
variable {B K : Type} [Ring B] [Field K] (ε : B →+* K) {n : ℕ}

theorem frameCoboundary_one (M : Type) [AddCommGroup M] (n : ℕ) :
    frameCoboundary ε M n 1 =
      frameFacePullback ε M (n := n) (0 : Fin 2) - frameFacePullback ε M (n := n) (1 : Fin 2) := by
  simp [frameCoboundary, Fin.sum_univ_two, sub_eq_add_neg]

set_option backward.isDefEq.respectTransparency false in
/-- Equal images under the two vertex faces give a cycle for the alternating differential. -/
theorem frameH2_cycle_of_faces (M : Type) [AddCommGroup M]
    (x : groupCohomology (frameCoefficients ε M n 1) 2)
    (hx : groupCohomology.map (MonoidHom.id (K1.E n B)) (frameFacePullback ε M (0 : Fin 2)) 2 x =
      groupCohomology.map (MonoidHom.id (K1.E n B)) (frameFacePullback ε M (1 : Fin 2)) 2 x) :
    groupCohomology.map (MonoidHom.id (K1.E n B)) (frameCoboundary ε M n 1) 2 x = 0 := by
  rw [frameCoboundary_one, cohomology_map_sub]
  change (groupCohomology.map (MonoidHom.id (K1.E n B)) (frameFacePullback ε M (0 : Fin 2)) 2).hom x -
    (groupCohomology.map (MonoidHom.id (K1.E n B)) (frameFacePullback ε M (1 : Fin 2)) 2).hom x = 0
  exact sub_eq_zero.mpr hx

end Frames

namespace PrimeAlgebra
open Frames
variable (p : ℕ) (hp : p.Prime) [Fact p.Prime]

set_option backward.isDefEq.respectTransparency false in
theorem frameAugmentationShapiro_naturality (M : Type) [AddCommGroup M]
    {m : ℕ} (hm : 0 < m) (q : ℕ) :
    groupCohomology.map (MonoidHom.id (K1.E (m + 1) (R p hp)))
        (frameAugmentation (augmentation p hp) M (m + 1)) q ≫
        (frameCoefficientShapiroIso p hp M (m := m) (l := 1) hm q).hom =
      groupCohomology.map (standardFrameStabilizer (augmentation p hp) m 1).subtype
        (Homogeneous.trivialRestriction (k := ℤ) (M := M)
          (standardFrameStabilizer (augmentation p hp) m 1).subtype) q := by
  rw [frameCoefficientShapiroIso_hom, ← groupCohomology.map_comp]
  apply groupCohomology.map_congr rfl
  apply LinearMap.ext
  intro a
  exact frameAugmentation_apply (augmentation p hp) M a
    (standardLengthFrame (augmentation p hp) m 1)

set_option backward.isDefEq.respectTransparency false in
/-- Every vertex character class constructed above lifts to constant coefficients on the ambient E. -/
theorem frameCharacterCycle_lift (M : Type) [CommGroup M] [DivisibleBy (Additive M) ℤ]
    {m : ℕ} (hm : 6 ≤ m)
    (χ : (Elementary.representation (n := m + 1) (R := R p hp)).ker →* M) :
    ∃ y : groupCohomology (Rep.trivial ℤ (K1.E (m + 2) (R p hp)) (Additive M)) 2,
      groupCohomology.map (MonoidHom.id (K1.E (m + 2) (R p hp)))
        (frameAugmentation (augmentation p hp) (Additive M) (m + 2)) 2 y =
          frameCharacterCycle p hp M hm χ := by
  have := frame_isPretransitive_of_lt p hp (m + 2) 4 (by omega)
  have hv := frameCoefficient_H1_subsingleton p hp (Additive M) (m := m - 1) (l := 3) (by omega)
  rw [show m - 1 + 3 = m + 2 by omega] at hv
  have L : LengthFrame (augmentation p hp) (m + 2) 5 := by
    rw [← show m - 3 + 5 = m + 2 by omega]
    exact standardLengthFrame (augmentation p hp) (m - 3) 5
  exact frameH2_lift (augmentation p hp) (Additive M) (by omega) L _
    (frameH2_cycle_of_faces (augmentation p hp) (Additive M) _ (frameCharacterCycle_faces p hp M hm χ))

set_option backward.isDefEq.respectTransparency false in
/-- The ambient constant-coefficient class restricts to the original vertex character class. -/
theorem frameCharacterClass_restriction_lift (M : Type) [CommGroup M] [DivisibleBy (Additive M) ℤ]
    {m : ℕ} (hm : 6 ≤ m)
    (χ : (Elementary.representation (n := m + 1) (R := R p hp)).ker →* M) :
    ∃ y : groupCohomology (Rep.trivial ℤ (K1.E (m + 2) (R p hp)) (Additive M)) 2,
      groupCohomology.map (standardFrameStabilizer (augmentation p hp) (m + 1) 1).subtype
        (Homogeneous.trivialRestriction (k := ℤ) (M := Additive M)
          (standardFrameStabilizer (augmentation p hp) (m + 1) 1).subtype) 2 y =
      frameCharacterClass (augmentation p hp) (unit_of_augmentation_ne_zero p hp) M
        (m := m + 1) (l := 1) (by omega) χ := by
  obtain ⟨y, hy⟩ := frameCharacterCycle_lift p hp M hm χ
  let e := frameCoefficientShapiroIso p hp (Additive M) (m := m + 1) (l := 1) (by omega) 2
  refine ⟨y, ?_⟩
  have hnat := congrArg (fun t => t y)
    (frameAugmentationShapiro_naturality p hp (Additive M) (m := m + 1) (by omega) 2)
  change e.hom (groupCohomology.map (MonoidHom.id (K1.E (m + 2) (R p hp)))
    (frameAugmentation (augmentation p hp) (Additive M) (m + 2)) 2 y) = _ at hnat
  rw [← hnat, hy]
  exact e.toLinearEquiv.apply_symm_apply _

set_option backward.isDefEq.respectTransparency false in
/-- In particular, the torsion-detecting rational-circle characters have ambient H² lifts. -/
theorem rationalCircle_frameCharacterClass_lift {m : ℕ} (hm : 6 ≤ m)
    (χ : (Elementary.representation (n := m + 1) (R := R p hp)).ker →*
      Multiplicative (AddCircle (1 : ℚ))) :
    ∃ y : groupCohomology (Rep.trivial ℤ (K1.E (m + 2) (R p hp))
        (Additive (Multiplicative (AddCircle (1 : ℚ))))) 2,
      groupCohomology.map (standardFrameStabilizer (augmentation p hp) (m + 1) 1).subtype
        (Homogeneous.trivialRestriction (k := ℤ)
          (M := Additive (Multiplicative (AddCircle (1 : ℚ))))
          (standardFrameStabilizer (augmentation p hp) (m + 1) 1).subtype) 2 y =
      frameCharacterClass (augmentation p hp) (unit_of_augmentation_ne_zero p hp)
        (Multiplicative (AddCircle (1 : ℚ))) (m := m + 1) (l := 1) (by omega) χ := by
  let : DivisibleBy (Additive (Multiplicative (AddCircle (1 : ℚ)))) ℤ :=
    Function.Surjective.divisibleBy
      (fun a : AddCircle (1 : ℚ) => Additive.ofMul (Multiplicative.ofAdd a))
      (fun a => ⟨a.toMul.toAdd, rfl⟩) (fun _ _ => rfl)
  exact frameCharacterClass_restriction_lift p hp _ hm χ

end PrimeAlgebra
end
end AllPrimeGroups
