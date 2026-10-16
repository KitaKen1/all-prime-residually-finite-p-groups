/-
The degree-two cocycle calculation is adapted from TauCetiProject/TauCeti,
TauCeti/RepresentationTheory/Homological/ContCohomology/Conjugation.lean at
d5a37097e93f6289425d25632df6c8bf00d749c0. See the source hash and URL in
upstream/TauCeti-Conjugation-provenance.json. Only the algebraic argument is retained,
expressed directly for Mathlib's representations and H²; no topology is used.
-/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Mathlib.Tactic.Abel

namespace AllPrimeGroups
namespace CohomologyConjugation
noncomputable section
open CategoryTheory groupCohomology

universe u
variable {k G : Type u} [CommRing k] [Group G] (A : Rep.{u} k G)

/-- The coefficient action that accompanies inverse conjugation of the group. -/
def innerCoefficient (g : G) : Rep.res (MulAut.conj g⁻¹).toMonoidHom A ⟶ A :=
  Rep.ofHom ⟨A.ρ g, fun h => by
    ext v
    change A.ρ g (A.ρ ((MulAut.conj g⁻¹) h) v) = A.ρ h (A.ρ g v)
    simp only [MulAut.conj_apply, inv_inv]
    simp only [← Module.End.mul_apply]
    rw [← map_mul, ← map_mul]
    congr 1
    simp [mul_assoc]⟩

/-- The degree-two part of the inverse-conjugation homotopy. -/
def innerHomotopy₂ (g : G) (c : G × G → A) : G → A :=
  fun h => c (g, g⁻¹ * h * g) - c (h, g)

/-- Conjugation changes a two-cocycle by the coboundary of an explicit one-cochain. -/
theorem innerCocycle_difference (g : G) (c : cocycles₂ A) :
    (mapCocycles₂ (MulAut.conj g⁻¹).toMonoidHom (innerCoefficient A g) c : G × G → A) - c =
      d₁₂ A (innerHomotopy₂ A g c) := by
  funext p
  rcases p with ⟨n, h⟩
  change A.ρ g (c ((MulAut.conj g⁻¹) n, (MulAut.conj g⁻¹) h)) - c (n, h) =
    A.ρ n (c (g, g⁻¹ * h * g) - c (h, g)) -
      (c (g, g⁻¹ * (n * h) * g) - c (n * h, g)) +
      (c (g, g⁻¹ * n * g) - c (n, g))
  simp only [MulAut.conj_apply, inv_inv]
  have hc := (mem_cocycles₂_iff c).mp c.property
  have hmul : g * (g⁻¹ * n * g) = n * g := by simp [mul_assoc]
  have hmul' : g * (g⁻¹ * h * g) = h * g := by simp [mul_assoc]
  have hconjmul : (g⁻¹ * n * g) * (g⁻¹ * h * g) = g⁻¹ * (n * h) * g := by
    simp [mul_assoc]
  have h₁ := hc g (g⁻¹ * n * g) (g⁻¹ * h * g)
  have h₂ := hc n g (g⁻¹ * h * g)
  have h₃ := hc n h g
  simp only [hmul, hmul', hconjmul] at h₁ h₂ h₃
  have h₁' : A.ρ g (c (g⁻¹ * n * g, g⁻¹ * h * g)) =
      c (n * g, g⁻¹ * h * g) + c (g, g⁻¹ * n * g) - c (g, g⁻¹ * (n * h) * g) := by
    apply (eq_sub_iff_add_eq).mpr
    simpa [add_comm] using h₁.symm
  have h₂' : A.ρ n (c (g, g⁻¹ * h * g)) =
      c (n * g, g⁻¹ * h * g) + c (n, g) - c (n, h * g) := by
    apply (eq_sub_iff_add_eq).mpr
    simpa [add_comm] using h₂.symm
  have h₃' : A.ρ n (c (h, g)) = c (n * h, g) + c (n, h) - c (n, h * g) := by
    apply (eq_sub_iff_add_eq).mpr
    simpa [add_comm] using h₃.symm
  rw [h₁', map_sub, h₂', h₃']
  abel

/-- In degree two, inverse conjugation together with the coefficient action is the identity. -/
theorem inner_map_H2 (g : G) :
    groupCohomology.map (MulAut.conj g⁻¹).toMonoidHom (innerCoefficient A g) 2 =
      𝟙 (groupCohomology A 2) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  induction x using H2_induction_on with
  | h c =>
    have h := H2π_comp_map (MulAut.conj g⁻¹).toMonoidHom (innerCoefficient A g)
    have he : groupCohomology.map (MulAut.conj g⁻¹).toMonoidHom (innerCoefficient A g) 2
        (H2π A c) = H2π A (mapCocycles₂ (MulAut.conj g⁻¹).toMonoidHom
          (innerCoefficient A g) c) := congrArg (fun f => f.hom c) h
    change groupCohomology.map _ _ 2 (H2π A c) = H2π A c
    rw [he, H2π_eq_iff, innerCocycle_difference]
    exact ⟨innerHomotopy₂ A g c, rfl⟩

/-- A compatible restriction is unchanged if conjugated in the ambient group and coefficients. -/
theorem conjugate_map_H2 {H : Type u} [Group H] {B : Rep.{u} k H}
    (r : H →* G) (φ : Rep.res r A ⟶ B) (g : G) :
    groupCohomology.map ((MulAut.conj g⁻¹).toMonoidHom.comp r)
        ((Rep.resFunctor r).map (innerCoefficient A g) ≫ φ) 2 =
      groupCohomology.map r φ 2 := by
  rw [groupCohomology.map_comp, inner_map_H2, Category.id_comp]

end
end CohomologyConjugation
end AllPrimeGroups
