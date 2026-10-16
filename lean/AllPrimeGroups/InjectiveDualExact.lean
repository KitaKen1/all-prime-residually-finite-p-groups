import Mathlib.Algebra.Category.Grp.Injective
import Mathlib.LinearAlgebra.Isomorphisms

/-! Exactness of the contravariant linear dual with an injective target.

The primitive is constructed on the image of the outgoing map, then extended to its whole
codomain. In particular, no equivariant choice of a chain primitive is required. -/

namespace AllPrimeGroups
noncomputable section

universe u v
variable {R : Type u} [Ring R]
  {A B C I : Type v} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
  [AddCommGroup I] [Module R A] [Module R B] [Module R C] [Module R I]

/-- A closed functional on an exact pair extends across the outgoing map. -/
theorem injective_dual_exact [Module.Injective R I]
    (f : A →ₗ[R] B) (g : B →ₗ[R] C)
    (hex : ∀ b, g b = 0 → ∃ a, f a = b)
    (φ : B →ₗ[R] I) (hφ : φ.comp f = 0) :
    ∃ ψ : C →ₗ[R] I, ψ.comp g = φ := by
  have hker : LinearMap.ker g ≤ LinearMap.ker φ := by
    intro b hb
    obtain ⟨a, rfl⟩ := hex b hb
    exact LinearMap.congr_fun hφ a
  let φq := (LinearMap.ker g).liftQ φ hker
  let φr := φq.comp g.quotKerEquivRange.symm.toLinearMap
  obtain ⟨ψ, hψ⟩ := Module.Injective.out (LinearMap.range g).subtype
    Subtype.val_injective φr
  refine ⟨ψ, LinearMap.ext fun b => ?_⟩
  simpa [φr, φq] using hψ ⟨g b, LinearMap.mem_range_self g b⟩

/-- Every divisible abelian group can be used as the target of this dual exactness argument. -/
theorem divisible_dual_exact {A B C I : Type v}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [AddCommGroup I]
    [DivisibleBy I ℤ] (f : A →ₗ[ℤ] B) (g : B →ₗ[ℤ] C)
    (hex : ∀ b, g b = 0 → ∃ a, f a = b)
    (φ : B →ₗ[ℤ] I) (hφ : φ.comp f = 0) :
    ∃ ψ : C →ₗ[ℤ] I, ψ.comp g = φ := by
  have : Module.Injective ℤ I := (Module.Baer.of_divisible I).injective
  exact injective_dual_exact f g hex φ hφ

end
end AllPrimeGroups
