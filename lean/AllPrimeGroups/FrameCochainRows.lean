import AllPrimeGroups.FrameCoefficientComplex
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

/-! The coefficient differential on every row of the inhomogeneous double complex.
Pointwise lifting gives horizontal exactness; functoriality supplies vertical commutation. -/

namespace AllPrimeGroups
namespace Frames
noncomputable section
open CategoryTheory groupCohomology

variable {B K : Type} [Ring B] [Field K] (ε : B →+* K) {n k : ℕ}

def frameCochainsCoboundary (M : Type) [AddCommGroup M] (n k q : ℕ) :
    (inhomogeneousCochains (frameCoefficients ε M n k)).X q ⟶
      (inhomogeneousCochains (frameCoefficients ε M n (k + 1))).X q :=
  (groupCohomology.cochainsMap (MonoidHom.id (K1.E n B))
    (frameCoboundary ε M n k)).f q

theorem frameCochainsCoboundary_apply (M : Type) [AddCommGroup M] (q : ℕ)
    (c : (Fin q → K1.E n B) → LengthFrame ε n k → M) (x : Fin q → K1.E n B) :
    frameCochainsCoboundary ε M n k q c x = (frameCoboundary ε M n k).hom (c x) := rfl

set_option backward.isDefEq.respectTransparency false in
theorem frameCochainsCoboundary_comm (M : Type) [AddCommGroup M] (n k q : ℕ) :
    (inhomogeneousCochains (frameCoefficients ε M n k)).d q (q + 1) ≫
        frameCochainsCoboundary ε M n k (q + 1) =
      frameCochainsCoboundary ε M n k q ≫
        (inhomogeneousCochains (frameCoefficients ε M n (k + 1))).d q (q + 1) := by
  exact ((groupCohomology.cochainsMap
    (A := frameCoefficients ε M n k) (B := frameCoefficients ε M n (k + 1))
    (MonoidHom.id (K1.E n B))
    (frameCoboundary ε M n k)).comm q (q + 1)).symm

theorem frameCochainsCoboundary_comp (M : Type) [AddCommGroup M] (n k q : ℕ) :
    frameCochainsCoboundary ε M n k q ≫
      frameCochainsCoboundary ε M n (k + 1) q = 0 := by
  ext c x F
  exact congrArg (fun t => t.hom (c x) F) (frameCoboundary_comp ε M n k)

/-- Every horizontal cochain row is exact below the ambient rank. -/
theorem frameCochainsCoboundary_exact (M : Type) [AddCommGroup M] [DivisibleBy M ℤ]
    (q : ℕ) (hk : k + 2 ≤ n)
    (c : (Fin q → K1.E n B) → LengthFrame ε n (k + 1) → M)
    (hc : frameCochainsCoboundary ε M n (k + 1) q c = 0) :
    ∃ b : (Fin q → K1.E n B) → LengthFrame ε n k → M,
      frameCochainsCoboundary ε M n k q b = c := by
  classical
  have hx (x : Fin q → K1.E n B) : (frameCoboundary ε M n (k + 1)).hom (c x) = 0 :=
    congrFun hc x
  choose b hb using fun x => frameCoboundary_exact ε M hk (c x) (hx x)
  exact ⟨b, funext hb⟩

theorem frameCochainsCoboundary_zero_injective (M : Type) [AddCommGroup M]
    (q : ℕ) (hn : 1 ≤ n) :
    Function.Injective (frameCochainsCoboundary ε M n 0 q) := by
  intro c b h
  funext x
  exact frameCoboundary_zero_injective ε M hn (congrFun h x)

end
end Frames
end AllPrimeGroups
