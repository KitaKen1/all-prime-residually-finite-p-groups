import AllPrimeGroups.FrameTransitivity
import Mathlib.GroupTheory.GroupAction.Quotient

/-! The homogeneous-space model of fixed-length ordered frames.

The quotient by the actual standard frame stabilizer maps equivariantly to the frame set.
It is always injective, and simultaneous frame completion makes it surjective. This supplies
the explicit coset model for Shapiro with the already identified block stabilizers. -/

namespace AllPrimeGroups
namespace Frames
noncomputable section
open Matrix QuotientGroup

variable {B K : Type*} [Ring B] [Field K] (ε : B →+* K) {m l : ℕ}

def cosetFrame (q : K1.E (m + l) B ⧸ standardFrameStabilizer ε m l) : LengthFrame ε (m + l) l :=
  Quotient.liftOn' q (fun g => g • standardLengthFrame ε m l) (fun g h heq => by
    have hh : (g⁻¹ * h) • standardFrame ε m l = standardFrame ε m l :=
      MulAction.mem_stabilizer_iff.mp (leftRel_apply.mp heq)
    have hh' : (g⁻¹ * h) • standardLengthFrame ε m l = standardLengthFrame ε m l := Subtype.ext hh
    calc
      g • standardLengthFrame ε m l = g • ((g⁻¹ * h) • standardLengthFrame ε m l) :=
        congrArg (g • ·) hh'.symm
      _ = h • standardLengthFrame ε m l := by rw [← mul_smul, mul_inv_cancel_left])

theorem cosetFrame_mk (g : K1.E (m + l) B) :
    cosetFrame ε (QuotientGroup.mk g) = g • standardLengthFrame ε m l := rfl

theorem cosetFrame_injective : Function.Injective (cosetFrame ε (m := m) (l := l)) := by
  intro q r
  refine Quotient.inductionOn₂' q r (fun g h heq => ?_)
  apply Quotient.sound'
  rw [leftRel_apply]
  apply MulAction.mem_stabilizer_iff.mpr
  have hh := congrArg Subtype.val heq
  change g • standardFrame ε m l = h • standardFrame ε m l at hh
  rw [mul_smul, ← hh, inv_smul_smul]

theorem cosetFrame_equivariant (g : K1.E (m + l) B)
    (q : K1.E (m + l) B ⧸ standardFrameStabilizer ε m l) :
    cosetFrame ε (g • q) = g • cosetFrame ε q := by
  refine Quotient.inductionOn' q (fun h => ?_)
  exact mul_smul g h _

section Split
variable (σ : K →+* B) (hs : ε.comp σ = RingHom.id K)
variable (hnil : ∀ A : Matrix (Fin (m + l)) (Fin (m + l)) B, ε.mapMatrix A = 0 → IsNilpotent A)
variable (hunit : ∀ b : B, ε b ≠ 0 → IsUnit b)

include σ hs hnil hunit in
theorem cosetFrame_surjective (hm : 0 < m) : Function.Surjective (cosetFrame ε (m := m) (l := l)) := by
  intro F
  obtain ⟨g, hg⟩ := exists_split_elementary_from_standard ε σ hs hnil hunit hm F.val F.property
  exact ⟨QuotientGroup.mk g, Subtype.ext hg⟩

def frameQuotientEquiv (hm : 0 < m) :
    (K1.E (m + l) B ⧸ standardFrameStabilizer ε m l) ≃ LengthFrame ε (m + l) l :=
  Equiv.ofBijective (cosetFrame ε) ⟨cosetFrame_injective ε, cosetFrame_surjective ε σ hs hnil hunit hm⟩

theorem frameQuotientEquiv_mk (hm : 0 < m) (g : K1.E (m + l) B) :
    frameQuotientEquiv ε σ hs hnil hunit hm (QuotientGroup.mk g) = g • standardLengthFrame ε m l := rfl

theorem frameQuotientEquiv_equivariant (hm : 0 < m) (g : K1.E (m + l) B)
    (q : K1.E (m + l) B ⧸ standardFrameStabilizer ε m l) :
    frameQuotientEquiv ε σ hs hnil hunit hm (g • q) =
      g • frameQuotientEquiv ε σ hs hnil hunit hm q := cosetFrame_equivariant ε g q

end Split
end
end Frames
end AllPrimeGroups
