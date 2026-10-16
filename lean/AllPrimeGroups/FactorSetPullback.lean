import AllPrimeGroups.ExtensionCohomology
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Mathlib.Tactic.Abel

/-! Equal restrictions of central-extension classes from maps agreeing on the source kernel.

The source kernel need not be commutative or centrally embedded. A set-theoretic section of
its surjective projection and the left coordinates of the two lifts give the required
coboundary explicitly. No injectivity of the projection or stabilization is assumed. -/

namespace AllPrimeGroups
namespace FactorSet
noncomputable section
open CategoryTheory groupCohomology

variable {G H E M : Type} [Group G] [Group H] [Group E] [CommGroup M]
  [MulDistribMulAction H M]

/-- Restriction of trivial multiplicative coefficients, in the additive H² interface. -/
def centralRestriction (f : G →* H) (htriv : ∀ (h : H) (a : M), h • a = a) :
    Rep.res f (Rep.ofMulDistribMulAction H M) ⟶ Rep.trivial ℤ G (Additive M) :=
  Rep.ofHom ⟨LinearMap.id, fun g => by
    ext a
    exact congrArg Additive.ofMul (htriv (f g) a.toMul)⟩

/-- Two lifts agreeing on the kernel pull back a central-extension class to the same H² class. -/
theorem cohomologyClass_comp_eq_of_lifts (α : FactorSet H M)
    (htriv : ∀ (h : H) (a : M), h • a = a)
    (p : E →* G) (hp : Function.Surjective p) (f₀ f₁ : G →* H)
    (φ₀ φ₁ : E →* α.Extension)
    (h₀ : α.rightHom.comp φ₀ = f₀.comp p) (h₁ : α.rightHom.comp φ₁ = f₁.comp p)
    (hker : ∀ e, p e = 1 → φ₀ e = φ₁ e) :
    groupCohomology.map f₀ (centralRestriction f₀ htriv) 2 α.cohomologyClass =
      groupCohomology.map f₁ (centralRestriction f₁ htriv) 2 α.cohomologyClass := by
  let s : G → E := Function.surjInv hp
  have hs : ∀ g, p (s g) = g := Function.surjInv_eq hp
  have hr (φ : E →* α.Extension) (f : G →* H)
      (hφ : α.rightHom.comp φ = f.comp p) (g : G) : (φ (s g)).right = f g := by
    have h := DFunLike.congr_fun hφ (s g)
    change (φ (s g)).right = f (p (s g)) at h
    rw [hs] at h
    exact h
  let a₀ : G → Additive M := fun g => Additive.ofMul (φ₀ (s g)).left
  let a₁ : G → Additive M := fun g => Additive.ofMul (φ₁ (s g)).left
  have heq (g h : G) :
      a₀ g + a₀ h + Additive.ofMul (α (f₀ g, f₀ h)) - a₀ (g * h) =
        a₁ g + a₁ h + Additive.ofMul (α (f₁ g, f₁ h)) - a₁ (g * h) := by
    let z := s g * s h * (s (g * h))⁻¹
    have hz : p z = 1 := by simp [z, hs]
    have he (φ : E →* α.Extension) (f : G →* H)
        (hφ : α.rightHom.comp φ = f.comp p) :
        Additive.ofMul (φ (s g)).left + Additive.ofMul (φ (s h)).left +
            Additive.ofMul (α (f g, f h)) - Additive.ofMul (φ (s (g * h))).left =
          Additive.ofMul (φ z).left := by
      have hm : φ (s g) * φ (s h) = φ z * φ (s (g * h)) := by
        rw [← map_mul, ← map_mul]
        simp [z]
      have hz' : (φ z).right = 1 := by
        have hh := DFunLike.congr_fun hφ z
        change (φ z).right = f (p z) at hh
        simpa only [hz, map_one] using hh
      have hh := congrArg (fun x : α.Extension => Additive.ofMul x.left) hm
      simp only [Extension.mul_left, htriv, hr φ f hφ, hz', α.map_one_fst,
        mul_one, ofMul_mul] at hh
      exact sub_eq_iff_eq_add.mpr hh
    have hleft := congrArg (fun x : α.Extension => Additive.ofMul x.left) (hker z hz)
    exact (he φ₀ f₀ h₀).trans (hleft.trans (he φ₁ f₁ h₁).symm)
  have hmap (f : G →* H) :
      groupCohomology.map f (centralRestriction f htriv) 2 α.cohomologyClass =
        H2π (Rep.trivial ℤ G (Additive M))
          (mapCocycles₂ f (centralRestriction f htriv) α.toCocycles₂) :=
    congrArg (fun q => q.hom α.toCocycles₂) (H2π_comp_map f (centralRestriction f htriv))
  rw [hmap, hmap, H2π_eq_iff]
  refine ⟨a₁ - a₀, ?_⟩
  funext gh
  rcases gh with ⟨g, h⟩
  change (a₁ h - a₀ h) - (a₁ (g * h) - a₀ (g * h)) + (a₁ g - a₀ g) =
    Additive.ofMul (α (f₀ g, f₀ h)) - Additive.ofMul (α (f₁ g, f₁ h))
  have hh := congrArg (fun x : Additive M => x - a₀ g - a₀ h + a₀ (g * h) -
    Additive.ofMul (α (f₁ g, f₁ h))) (heq g h)
  convert hh.symm using 1 <;> abel

end
end FactorSet
end AllPrimeGroups
