import AllPrimeGroups.FrameCosets
import AllPrimeGroups.PrimeCharacterReduction

/-! Concrete frame transitivity for the all-prime coefficient algebras.

The augmentation splits through the prime-field algebra map, its matrix kernel is nil, and
nonzero reductions are units. All hypotheses of simultaneous frame completion are discharged
here; no finite-rank Steinberg injectivity is used. -/

namespace AllPrimeGroups
namespace PrimeAlgebra
noncomputable section
open Matrix Frames

variable (p : ℕ) (hp : p.Prime)

theorem augmentation_split :
    (augmentation p hp).comp (algebraMap (ZMod p) (R p hp)) = RingHom.id (ZMod p) := by
  ext a
  exact (OAI.SourceBurnside.ConcreteSource.machine.augmentation
    (threshold_le_height p hp) (ZMod p)).commutes a

theorem matrix_isUnit_iff_reduction {n : ℕ} (A : Matrix (Fin n) (Fin n) (R p hp)) :
    IsUnit A ↔ IsUnit ((augmentation p hp).mapMatrix A) :=
  MatrixLifting.isUnit_iff_matrix_reduction (augmentation p hp)
    (algebraMap (ZMod p) (R p hp)) (augmentation_split p hp) (matrix_nil p hp n) A

variable [Fact p.Prime]

theorem exists_frame_transport {m l : ℕ} (hm : 0 < m)
    (F G : ColumnFrame (augmentation p hp) (m + l)) (hF : F.val.length = l) (hG : G.val.length = l) :
    ∃ A : K1.E (m + l) (R p hp), A • F = G :=
  exists_split_elementary_between (augmentation p hp) (algebraMap (ZMod p) (R p hp))
    (augmentation_split p hp) (matrix_nil p hp (m + l)) (unit_of_augmentation_ne_zero p hp)
    hm F G hF hG

theorem frame_isPretransitive {m l : ℕ} (hm : 0 < m) :
    MulAction.IsPretransitive (K1.E (m + l) (R p hp))
      (LengthFrame (augmentation p hp) (m + l) l) :=
  lengthFrame_isPretransitive (augmentation p hp) (algebraMap (ZMod p) (R p hp))
    (augmentation_split p hp) (matrix_nil p hp (m + l)) (unit_of_augmentation_ne_zero p hp) hm

/-- Every frame length strictly below the ambient rank is one elementary-group orbit. -/
theorem frame_isPretransitive_of_lt (n l : ℕ) (hl : l < n) :
    MulAction.IsPretransitive (K1.E n (R p hp)) (LengthFrame (augmentation p hp) n l) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + l := ⟨n - l, by omega⟩
  exact frame_isPretransitive p hp (by omega)

/-- The concrete homogeneous-space model, with all completion hypotheses discharged. -/
def frameQuotientEquiv {m l : ℕ} (hm : 0 < m) :
    (K1.E (m + l) (R p hp) ⧸ standardFrameStabilizer (augmentation p hp) m l) ≃
      LengthFrame (augmentation p hp) (m + l) l :=
  Frames.frameQuotientEquiv (augmentation p hp) (algebraMap (ZMod p) (R p hp))
    (augmentation_split p hp) (matrix_nil p hp (m + l)) (unit_of_augmentation_ne_zero p hp) hm

theorem frameQuotientEquiv_equivariant {m l : ℕ} (hm : 0 < m)
    (g : K1.E (m + l) (R p hp))
    (q : K1.E (m + l) (R p hp) ⧸ standardFrameStabilizer (augmentation p hp) m l) :
    frameQuotientEquiv p hp (m := m) (l := l) hm
      (SMul.smul g q : K1.E (m + l) (R p hp) ⧸ standardFrameStabilizer (augmentation p hp) m l) =
      (SMul.smul g (frameQuotientEquiv p hp (m := m) (l := l) hm q) :
        LengthFrame (augmentation p hp) (m + l) l) :=
  Frames.cosetFrame_equivariant (augmentation p hp) (m := m) (l := l) g q

end
end PrimeAlgebra
end AllPrimeGroups
