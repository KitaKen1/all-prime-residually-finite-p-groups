import AllPrimeGroups.FrameCosets
import AllPrimeGroups.FunctionCoinduction

/-! Fixed-length frame functions and the equivariant pullbacks of the actual faces. -/

namespace AllPrimeGroups
namespace Frames
noncomputable section
open CategoryTheory

variable {B K : Type} [Ring B] [Field K] (ε : B →+* K) {n l : ℕ}

/-- A face in the fixed-length frame sets. -/
def lengthFace (i : Fin (l + 1)) (F : LengthFrame ε n (l + 1)) : LengthFrame ε n l :=
  ⟨face F.val i, by
    change (F.val.val.eraseIdx i).length = l
    have hi : i.val < F.val.val.length := by rw [F.property]; exact i.isLt
    rw [List.length_eraseIdx_of_lt hi, F.property]
    omega⟩

theorem lengthFace_equivariant (i : Fin (l + 1)) (g : K1.E n B)
    (F : LengthFrame ε n (l + 1)) :
    lengthFace ε i (g • F) = g • lengthFace ε i F :=
  Subtype.ext (face_elementaryFrame_smul ε g F.val i)

abbrev frameCoefficients (M : Type) [AddCommGroup M] (n l : ℕ) : Rep ℤ (K1.E n B) :=
  Homogeneous.functionRep (k := ℤ) (G := K1.E n B) (X := LengthFrame ε n l) (M := M)

/-- Contravariant face maps on all coefficient functions. -/
def frameFacePullback (M : Type) [AddCommGroup M] (i : Fin (l + 1)) :
    frameCoefficients ε M n l ⟶ frameCoefficients ε M n (l + 1) :=
  Homogeneous.functionPullback (lengthFace ε i) (lengthFace_equivariant ε i)

theorem frameFacePullback_apply (M : Type) [AddCommGroup M] (i : Fin (l + 1))
    (f : LengthFrame ε n l → M) (F : LengthFrame ε n (l + 1)) :
    (frameFacePullback ε M i).hom f F = f (lengthFace ε i F) := rfl

variable (σ : K →+* B) (hs : ε.comp σ = RingHom.id K) {m : ℕ}
  (hnil : ∀ A : Matrix (Fin (m + l)) (Fin (m + l)) B, ε.mapMatrix A = 0 → IsNilpotent A)
  (hunit : ∀ b : B, ε b ≠ 0 → IsUnit b)

/-- The coefficient functions used in the frame double complex are coinduced. -/
def frameCoefficientsCoindIso (M : Type) [AddCommGroup M] (hm : 0 < m) :
    frameCoefficients ε M (m + l) l ≅
      Rep.coind (standardFrameStabilizer ε m l).subtype
        (Rep.trivial ℤ (standardFrameStabilizer ε m l) M) :=
  Homogeneous.orbitCoindIso _ (frameQuotientEquiv ε σ hs hnil hunit hm)
    (frameQuotientEquiv_equivariant ε σ hs hnil hunit hm)

theorem frameCoefficientsCoindIso_apply (M : Type) [AddCommGroup M] (hm : 0 < m)
    (f : LengthFrame ε (m + l) l → M) (g : K1.E (m + l) B) :
    ((frameCoefficientsCoindIso ε σ hs hnil hunit M hm).hom.hom f).val g =
      f (g⁻¹ • standardLengthFrame ε m l) := rfl

end
end Frames
end AllPrimeGroups
