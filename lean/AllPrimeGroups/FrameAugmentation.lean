import AllPrimeGroups.FrameCoefficientComplex

/-! Empty-frame coefficients are constant coefficients, with the usual augmentation. -/

namespace AllPrimeGroups
namespace Frames
noncomputable section
open CategoryTheory
variable {B K : Type} [Ring B] [Field K] (ε : B →+* K) {n : ℕ}

def emptyLengthFrame (n : ℕ) : LengthFrame ε n 0 := ⟨⟨[], isFrame_nil⟩, rfl⟩

theorem lengthFrame_zero_eq (F : LengthFrame ε n 0) : F = emptyLengthFrame ε n := by
  apply Subtype.ext
  apply Subtype.ext
  exact List.length_eq_zero_iff.mp F.property

def frameEmptyEquiv (M : Type) [AddCommGroup M] (n : ℕ) :
    (LengthFrame ε n 0 → M) ≃ₗ[ℤ] M where
  toFun f := f (emptyLengthFrame ε n)
  invFun a := fun _ => a
  left_inv f := by
    funext F
    exact congrArg f (lengthFrame_zero_eq ε F).symm
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The empty-frame coefficient representation is the trivial representation. -/
def frameAugmentationIso (M : Type) [AddCommGroup M] (n : ℕ) :
    Rep.trivial ℤ (K1.E n B) M ≅ frameCoefficients ε M n 0 :=
  Rep.mkIso <| .mk (frameEmptyEquiv ε M n).symm (fun _ => by ext; rfl)

def frameAugmentation (M : Type) [AddCommGroup M] (n : ℕ) :
    Rep.trivial ℤ (K1.E n B) M ⟶ frameCoefficients ε M n 1 :=
  (frameAugmentationIso ε M n).hom ≫ frameCoboundary ε M n 0

theorem frameAugmentation_apply (M : Type) [AddCommGroup M] (a : M)
    (F : LengthFrame ε n 1) : (frameAugmentation ε M n).hom a F = a := by
  change (frameCoboundary ε M n 0).hom (fun _ => a) F = a
  rw [frameCoboundary_apply]
  simp

end
end Frames
end AllPrimeGroups
