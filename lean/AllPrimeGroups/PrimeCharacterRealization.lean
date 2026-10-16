import AllPrimeGroups.PrimeFrameH2Lift
import AllPrimeGroups.CentralClassLifts
import AllPrimeGroups.OneRowFrameCover

/-! Realization of the ambient character classes as central group extensions, with a
compatible map from the original one-row cover and the prescribed values on its matrix kernel. -/

namespace AllPrimeGroups
namespace PrimeAlgebra
noncomputable section
open Frames FrameStabilizer CategoryTheory

local instance (G A : Type*) [Group G] [Group A] : MulDistribMulAction G A :=
  CentralCocycles.trivialAction G A

variable (p : ℕ) (hp : p.Prime) [Fact p.Prime]

set_option backward.isDefEq.respectTransparency false in
theorem block_character_realization (M : Type) [CommGroup M] [DivisibleBy (Additive M) ℤ]
    {m : ℕ} (hm : 6 ≤ m)
    (χ : (Elementary.representation (n := m + 1) (R := R p hp)).ker →* M) :
    ∃ (α : FactorSet (K1.E (m + 2) (R p hp)) M)
      (ψ : BlockCover (Fin 1) (m + 1) (R p hp) →* α.Extension),
      α.rightHom.comp ψ = (standardFrameStabilizer (augmentation p hp) (m + 1) 1).subtype.comp
        (standardFrameExtension (augmentation p hp) (unit_of_augmentation_ne_zero p hp)
          (m := m + 1) (l := 1) (by omega)).rightHom ∧
      ∀ j, ψ (blockKernelInclusion j) = α.inl (χ j) := by
  obtain ⟨y, hy⟩ := frameCharacterClass_restriction_lift p hp M hm χ
  obtain ⟨α, hα⟩ := FactorSet.exists_cohomologyClass_eq y
  let S := standardFrameExtension (augmentation p hp) (unit_of_augmentation_ne_zero p hp)
    (m := m + 1) (l := 1) (show 5 ≤ m + 1 by omega)
  let D := frameCharacterData (augmentation p hp) (unit_of_augmentation_ne_zero p hp) M
    (m := m + 1) (l := 1) (show 6 ≤ m + 1 by omega) χ
  have hclass : groupCohomology.map (standardFrameStabilizer (augmentation p hp) (m + 1) 1).subtype
      (Homogeneous.trivialRestriction (k := ℤ) (M := Additive M)
        (standardFrameStabilizer (augmentation p hp) (m + 1) 1).subtype) 2
        α.cohomologyClass = D.cocycle.cohomologyClass := by
    rw [hα]
    exact hy
  obtain ⟨ψ, hψ, hker⟩ := D.exists_lift S χ α
    (standardFrameStabilizer (augmentation p hp) (m + 1) 1).subtype hclass
  exact ⟨α, ψ, hψ, hker⟩

set_option backward.isDefEq.respectTransparency false in
/-- Every rational-circle character of the smaller matrix kernel is realized on the one-row cover. -/
theorem kernel_character_realization {m : ℕ} (hm : 7 ≤ m)
    (χ : (Elementary.representation (n := m) (R := R p hp)).ker →*
      Multiplicative (AddCircle (1 : ℚ))) :
    ∃ (V : Type) (_ : Group V)
      (π : V →* (Matrix (Fin (m + 1)) (Fin (m + 1)) (R p hp))ˣ)
      (i : Multiplicative (AddCircle (1 : ℚ)) →* V) (ψ : Cover m (R p hp) →* V),
      Function.Injective i ∧ Elementary.representation.range ≤ π.range ∧
      (∀ v, π v = 1 → v ∈ Subgroup.center V) ∧
      π.comp ψ = Elementary.representation.comp (toSteinberg (m := m) (B := R p hp)) ∧
      ∀ j, ψ (kernelInclusion j) = i (χ j) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  let : DivisibleBy (Additive (Multiplicative (AddCircle (1 : ℚ)))) ℤ :=
    Function.Surjective.divisibleBy
      (fun a : AddCircle (1 : ℚ) => Additive.ofMul (Multiplicative.ofAdd a))
      (fun a => ⟨a.toMul.toAdd, rfl⟩) (fun _ _ => rfl)
  obtain ⟨α, φ, hφ, hχ⟩ := block_character_realization p hp _ (m := k) (by omega) χ
  let π := (K1.E (k + 2) (R p hp)).subtype.comp α.rightHom
  let ψ := φ.comp (rowInclusion (0 : Fin 1))
  refine ⟨α.Extension, inferInstance, π, α.inl, ψ, α.inl_injective, ?_, ?_, ?_, ?_⟩
  · intro A hA
    obtain ⟨z, rfl⟩ := hA
    let e : K1.E (k + 2) (R p hp) := ⟨Elementary.representation z, ⟨z, rfl⟩⟩
    obtain ⟨v, hv⟩ := α.rightHom_surjective e
    exact ⟨v, congrArg Subtype.val hv⟩
  · intro v hv
    have hright : α.rightHom v = 1 := Subtype.ext hv
    apply α.inl_range_le_center (fun _ _ => rfl)
    rw [α.range_inl_eq_ker_rightHom, MonoidHom.mem_ker]
    exact hright
  · apply MonoidHom.ext
    intro x
    have h := DFunLike.congr_fun hφ (rowInclusion (0 : Fin 1) x)
    change α.rightHom (φ (rowInclusion (0 : Fin 1) x)) =
      ((standardFrameExtension (augmentation p hp) (unit_of_augmentation_ne_zero p hp)
        (m := k + 1) (l := 1) (by omega)).rightHom (rowInclusion (0 : Fin 1) x)).val at h
    change (α.rightHom (φ (rowInclusion (0 : Fin 1) x))).val =
      Elementary.representation (toSteinberg x)
    have hrep : Elementary.representation (toSteinberg x) = toMatrix x :=
      DFunLike.congr_fun (representation_toSteinberg (m := k + 1) (B := R p hp)) x
    exact (congrArg Subtype.val h).trans
      ((rowInclusion_standard_projection (augmentation p hp) (unit_of_augmentation_ne_zero p hp)
        (by omega) x).trans hrep.symm)
  · intro j
    change φ (rowInclusion (0 : Fin 1) (kernelInclusion j)) = α.inl (χ j)
    rw [rowInclusion_kernel]
    exact hχ j

end
end PrimeAlgebra
end AllPrimeGroups
