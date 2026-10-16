import AllPrimeGroups.FrameChainDuality
import AllPrimeGroups.InjectiveDualExact
import Mathlib.Algebra.BigOperators.Fin

/-! The alternating frame coefficient complex is the dual of the augmented frame complex.
Its underlying sequence is exact below the rank for every divisible abelian target. -/

namespace AllPrimeGroups
namespace Frames
noncomputable section
open CategoryTheory

variable {B K : Type} [Ring B] [Field K] (ε : B →+* K) {n k : ℕ}

theorem frameBoundary_single (F : LengthFrame ε n (k + 1)) :
    frameBoundary ε n k (frameChainSingle ε F) =
      ∑ i : Fin (k + 1), (-1 : ℤ) ^ i.val • frameChainSingle ε (lengthFace ε i F) := by
  apply Subtype.ext
  change bd (Finsupp.single F.val 1) = _
  rw [bd_single, one_zsmul]
  simp only [faces, F.property, Submodule.coe_sum, Submodule.coe_smul,
    frameChainSingle, lengthFace]
  exact (Fin.sum_univ_eq_sum_range
    (fun i => (-1 : ℤ) ^ i • Finsupp.single (face F.val i) 1) (k + 1)).symm

/-- The horizontal differential, including the empty-frame augmentation at length zero. -/
def frameCoboundary (M : Type) [AddCommGroup M] (n k : ℕ) :
    frameCoefficients ε M n k ⟶ frameCoefficients ε M n (k + 1) :=
  ∑ i : Fin (k + 1), (-1 : ℤ) ^ i.val • frameFacePullback ε M i

theorem frameCoboundary_apply (M : Type) [AddCommGroup M]
    (f : LengthFrame ε n k → M) (F : LengthFrame ε n (k + 1)) :
    (frameCoboundary ε M n k).hom f F =
      ∑ i : Fin (k + 1), (-1 : ℤ) ^ i.val • f (lengthFace ε i F) := by
  simp [frameCoboundary, Rep.sum_hom, Rep.smul_hom,
    Representation.IntertwiningMap.sum_apply, Representation.IntertwiningMap.smul_apply,
    Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  congr 1

/-- Evaluating a coboundary equals precomposing its functional with the chain boundary. -/
theorem frameDualEquiv_coboundary (M : Type) [AddCommGroup M]
    (f : LengthFrame ε n k → M) :
    frameDualEquiv ε M n (k + 1) ((frameCoboundary ε M n k).hom f) =
      (frameDualEquiv ε M n k f).comp (frameBoundary ε n k) := by
  apply frameLinear_ext ε M
  intro F
  simp only [frameDualEquiv_single, LinearMap.comp_apply, frameBoundary_single,
    map_sum, map_smul]
  exact frameCoboundary_apply ε M f F

theorem frameCoboundary_comp (M : Type) [AddCommGroup M] (n k : ℕ) :
    frameCoboundary ε M n k ≫ frameCoboundary ε M n (k + 1) = 0 := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro f
  change (frameCoboundary ε M n (k + 1)).hom
    ((frameCoboundary ε M n k).hom f) = 0
  apply (frameDualEquiv ε M n (k + 2)).injective
  rw [map_zero, frameDualEquiv_coboundary, frameDualEquiv_coboundary,
    LinearMap.comp_assoc, frameBoundary_comp, LinearMap.comp_zero]

/-- Closed coefficient functions have primitives when the relevant chain length is below rank. -/
theorem frameCoboundary_exact (M : Type) [AddCommGroup M] [DivisibleBy M ℤ]
    (hk : k + 2 ≤ n) (f : LengthFrame ε n (k + 1) → M)
    (hf : (frameCoboundary ε M n (k + 1)).hom f = 0) :
    ∃ g : LengthFrame ε n k → M, (frameCoboundary ε M n k).hom g = f := by
  have hφ : (frameDualEquiv ε M n (k + 1) f).comp
      (frameBoundary ε n (k + 1)) = 0 := by
    rw [← frameDualEquiv_coboundary, hf, map_zero]
  obtain ⟨ψ, hψ⟩ := divisible_dual_exact
    (frameBoundary ε n (k + 1)) (frameBoundary ε n k)
    (frameBoundary_exact ε k hk) (frameDualEquiv ε M n (k + 1) f) hφ
  refine ⟨(frameDualEquiv ε M n k).symm ψ, ?_⟩
  apply (frameDualEquiv ε M n (k + 1)).injective
  rw [frameDualEquiv_coboundary, LinearEquiv.apply_symm_apply, hψ]

/-- The augmentation into vertex functions is injective in positive ambient rank. -/
theorem frameCoboundary_zero_injective (M : Type) [AddCommGroup M] (hn : 1 ≤ n) :
    Function.Injective (frameCoboundary ε M n 0).hom := by
  intro f g h
  apply (frameDualEquiv ε M n 0).injective
  apply LinearMap.ext
  intro z
  obtain ⟨y, rfl⟩ := frameBoundary_zero_surjective ε hn z
  have h' := congrArg (fun t => frameDualEquiv ε M n 1 t y) h
  rw [frameDualEquiv_coboundary, frameDualEquiv_coboundary] at h'
  exact h'

end
end Frames
end AllPrimeGroups
