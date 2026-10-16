import AllPrimeGroups.FrameActions
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Basis.Basic

/-! Simultaneous completion of an independent family over a field.

Mathlib extends the induced isomorphism between the two spans to the whole ambient vector
space. Thus no explicit indexing of a complementary basis is needed. -/

namespace AllPrimeGroups
namespace Frames
noncomputable section
open Matrix

section General
variable {K W ι : Type*} [Field K] [AddCommGroup W] [Module K W] [FiniteDimensional K W]

theorem exists_linearEquiv_on_independent (u v : ι → W)
    (hu : LinearIndependent K u) (hv : LinearIndependent K v) :
    ∃ e : W ≃ₗ[K] W, ∀ i, e (u i) = v i := by
  let f := (Module.Basis.span hu).equiv (Module.Basis.span hv) (Equiv.refl ι)
  obtain ⟨e, he⟩ := Submodule.exists_linearEquiv_restrict_eq f
  refine ⟨e, fun i => ?_⟩
  have h := he ((Module.Basis.span hu) i)
  simpa only [f, Module.Basis.equiv_apply, Equiv.refl_apply, Module.Basis.coe_span_apply] using h.symm

end General

variable {K : Type*} [Field K] {n l : ℕ}

def linearEquivMatrix (e : (Fin n → K) ≃ₗ[K] (Fin n → K)) :
    (Matrix (Fin n) (Fin n) K)ˣ where
  val := LinearMap.toMatrix' e.toLinearMap
  inv := LinearMap.toMatrix' e.symm.toLinearMap
  val_inv := by
    rw [← LinearMap.toMatrix'_comp]
    simp
  inv_val := by
    rw [← LinearMap.toMatrix'_comp]
    simp

theorem linearEquivMatrix_mulVec (e : (Fin n → K) ≃ₗ[K] (Fin n → K)) (x : Fin n → K) :
    (linearEquivMatrix e).val *ᵥ x = e x := LinearMap.toMatrix'_mulVec _ _

theorem exists_field_matrix_columns (f : Fin l → Fin n) (hf : Function.Injective f)
    (v : Fin l → Fin n → K) (hv : LinearIndependent K v) :
    ∃ A : (Matrix (Fin n) (Fin n) K)ˣ, ∀ j, A.val *ᵥ Pi.single (f j) 1 = v j := by
  have hu : LinearIndependent K (fun j : Fin l => (Pi.single (f j) 1 : Fin n → K)) := by
    simpa only [Function.comp_def, Pi.basisFun_apply] using
      (Pi.basisFun K (Fin n)).linearIndependent.comp f hf
  obtain ⟨e, he⟩ := exists_linearEquiv_on_independent _ v hu hv
  exact ⟨linearEquivMatrix e, fun j => (linearEquivMatrix_mulVec _ _).trans (he j)⟩

end
end Frames
end AllPrimeGroups
