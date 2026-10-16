import AllPrimeGroups.FrameRepresentations
import AllPrimeGroups.FrameCochains
import Mathlib.LinearAlgebra.Finsupp.Supported
import Mathlib.LinearAlgebra.Finsupp.LSum

/-! Fixed-length frame chains are free on the fixed-length frames. Their linear dual is
exactly the coefficient-function representation used by Shapiro. -/

namespace AllPrimeGroups
namespace Frames
noncomputable section

variable {B K : Type} [Ring B] [Field K] (ε : B →+* K) {n k : ℕ}

/-- The support restriction in `frameChains` is precisely Mathlib's supported submodule. -/
def frameChainsEquivFinsupp (n k : ℕ) :
    frameChains ε n k ≃ₗ[ℤ] (LengthFrame ε n k →₀ ℤ) :=
  Finsupp.supportedEquivFinsupp (R := ℤ) {F : ColumnFrame ε n | F.val.length = k}

def frameChainSingle (F : LengthFrame ε n k) : frameChains ε n k :=
  ⟨Finsupp.single F.val 1, show Deg k (Finsupp.single F.val 1) from by
    simpa only [F.property] using Deg.single F.val (1 : ℤ)⟩

theorem frameChainsEquivFinsupp_symm_single (F : LengthFrame ε n k) :
    (frameChainsEquivFinsupp ε n k).symm (Finsupp.single F 1) =
      frameChainSingle ε F := by
  apply Subtype.ext
  exact Finsupp.supportedEquivFinsupp_symm_single _ F 1

/-- A coefficient function extends uniquely to a linear functional on frame chains. -/
def frameDualEquiv (M : Type) [AddCommGroup M] (n k : ℕ) :
    (LengthFrame ε n k → M) ≃ₗ[ℤ] (frameChains ε n k →ₗ[ℤ] M) :=
  (Finsupp.llift M ℤ ℤ (LengthFrame ε n k)).trans
    (LinearEquiv.congrLeft M ℤ (frameChainsEquivFinsupp ε n k).symm)

theorem frameDualEquiv_symm_apply (M : Type) [AddCommGroup M]
    (φ : frameChains ε n k →ₗ[ℤ] M) (F : LengthFrame ε n k) :
    (frameDualEquiv ε M n k).symm φ F = φ (frameChainSingle ε F) := by
  change φ ((frameChainsEquivFinsupp ε n k).symm (Finsupp.single F 1)) = _
  rw [frameChainsEquivFinsupp_symm_single]

theorem frameDualEquiv_single (M : Type) [AddCommGroup M]
    (f : LengthFrame ε n k → M) (F : LengthFrame ε n k) :
    frameDualEquiv ε M n k f (frameChainSingle ε F) = f F := by
  simpa only [frameDualEquiv_symm_apply] using
    congrFun ((frameDualEquiv ε M n k).symm_apply_apply f) F

theorem frameLinear_ext (M : Type) [AddCommGroup M]
    {φ ψ : frameChains ε n k →ₗ[ℤ] M}
    (h : ∀ F, φ (frameChainSingle ε F) = ψ (frameChainSingle ε F)) : φ = ψ := by
  apply (frameDualEquiv ε M n k).symm.injective
  funext F
  simpa only [frameDualEquiv_symm_apply] using h F

end
end Frames
end AllPrimeGroups
