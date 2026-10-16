import AllPrimeGroups.FrameCoefficientComplex
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

/-! On a transitive frame set, invariant coefficient functions are constant. The horizontal
H⁰ differential is multiplication by the alternating sum of the face signs. -/

namespace AllPrimeGroups
noncomputable section

namespace Homogeneous
variable {G X M : Type} [Group G] [MulAction G X] [MulAction.IsPretransitive G X]
  [AddCommGroup M]

theorem invariant_function_eq (f : (functionRepresentation ℤ G X M).invariants) (x y : X) :
    f.val x = f.val y := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G x y
  have h := congrFun (f.property g⁻¹) x
  change f.val (g⁻¹⁻¹ • x) = f.val x at h
  rw [inv_inv, hg] at h
  exact h.symm

/-- Evaluation at any base point identifies invariant functions with their constant values. -/
def functionInvariantsEquiv (x : X) : (functionRepresentation ℤ G X M).invariants ≃ₗ[ℤ] M where
  toFun f := f.val x
  invFun a := ⟨fun _ => a, fun _ => rfl⟩
  left_inv f := by
    apply Subtype.ext
    funext y
    exact invariant_function_eq f x y
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end Homogeneous

namespace Frames
open CategoryTheory
variable {B K : Type} [Ring B] [Field K] (ε : B →+* K) {n k : ℕ}

/-- A zeroth cohomology class of frame functions is its constant value. -/
def frameH0Equiv (M : Type) [AddCommGroup M]
    [MulAction.IsPretransitive (K1.E n B) (LengthFrame ε n k)]
    (F : LengthFrame ε n k) : groupCohomology.H0 (frameCoefficients ε M n k) ≃ₗ[ℤ] M :=
  (groupCohomology.H0Iso (frameCoefficients ε M n k)).toLinearEquiv.trans
    (Homogeneous.functionInvariantsEquiv F)

theorem frameCoboundary_invariant_apply (M : Type) [AddCommGroup M]
    [MulAction.IsPretransitive (K1.E n B) (LengthFrame ε n k)]
    (f : (frameCoefficients ε M n k).ρ.invariants)
    (F : LengthFrame ε n k) (L : LengthFrame ε n (k + 1)) :
    (frameCoboundary ε M n k).hom f.val L =
      (if Even (k + 1) then (0 : ℤ) else 1) • f.val F := by
  rw [frameCoboundary_apply]
  calc
    _ = ∑ i : Fin (k + 1), (-1 : ℤ) ^ i.val • f.val F := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Homogeneous.invariant_function_eq f (lengthFace ε i L) F]
    _ = (∑ i : Fin (k + 1), (-1 : ℤ) ^ i.val) • f.val F :=
      Finset.sum_smul.symm
    _ = _ := by rw [Fin.sum_neg_one_pow]

set_option backward.isDefEq.respectTransparency false in
/-- Under constant-value coordinates, the H⁰ differential is the alternating sign sum. -/
theorem frameH0Equiv_coboundary (M : Type) [AddCommGroup M]
    [MulAction.IsPretransitive (K1.E n B) (LengthFrame ε n k)]
    [MulAction.IsPretransitive (K1.E n B) (LengthFrame ε n (k + 1))]
    (F : LengthFrame ε n k) (L : LengthFrame ε n (k + 1))
    (c : groupCohomology.H0 (frameCoefficients ε M n k)) :
    frameH0Equiv ε M L
        (groupCohomology.map (MonoidHom.id (K1.E n B)) (frameCoboundary ε M n k) 0 c) =
      (if Even (k + 1) then (0 : ℤ) else 1) • frameH0Equiv ε M F c := by
  have h := congrArg (fun t => (t.hom c).val L)
    (groupCohomology.map_id_comp_H0Iso_hom (frameCoboundary ε M n k))
  change frameH0Equiv ε M L
      (groupCohomology.map (MonoidHom.id (K1.E n B)) (frameCoboundary ε M n k) 0 c) =
    (frameCoboundary ε M n k).hom
      ((groupCohomology.H0Iso (frameCoefficients ε M n k)).hom c).val L at h
  rw [h]
  exact frameCoboundary_invariant_apply ε M _ F L

end Frames
end
end AllPrimeGroups
