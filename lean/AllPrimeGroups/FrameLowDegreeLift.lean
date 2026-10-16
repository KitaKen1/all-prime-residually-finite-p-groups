import AllPrimeGroups.FrameCochainRows
import AllPrimeGroups.FrameCoefficientH0
import AllPrimeGroups.CochainExactness
import AllPrimeGroups.LowDegreeChase

/-! The finite low-degree chase applied to frame cochains.

A horizontal degree-two cycle lifts to a vertically closed cochain on empty frames, modulo a
vertical boundary. The H¹ and orbit hypotheses are kept explicit in this generic version. -/

namespace AllPrimeGroups
namespace Frames
noncomputable section
open CategoryTheory groupCohomology

variable {B K : Type} [Ring B] [Field K] (ε : B →+* K) {n : ℕ}

theorem frame_zero_cochain_eq_zero (M : Type) [AddCommGroup M]
    [MulAction.IsPretransitive (K1.E n B) (LengthFrame ε n 4)]
    (L : LengthFrame ε n 5)
    (c : (inhomogeneousCochains (frameCoefficients ε M n 4)).X 0)
    (hc : (inhomogeneousCochains (frameCoefficients ε M n 4)).d 0 1 c = 0)
    (hh : frameCochainsCoboundary ε M n 4 0 c = 0) : c = 0 := by
  funext x F
  let f : (frameCoefficients ε M n 4).ρ.invariants :=
    ⟨c x, cochain_zero_invariant _ c hc x⟩
  have hs := frameCoboundary_invariant_apply ε M f F L
  norm_num at hs
  have hz := congrFun (congrFun hh x) L
  exact hs.symm.trans hz

set_option backward.isDefEq.respectTransparency false in
/-- A horizontal H² cycle lifts at the level of cochain representatives. -/
theorem frame_low_degree_lift (M : Type) [AddCommGroup M] [DivisibleBy M ℤ]
    [MulAction.IsPretransitive (K1.E n B) (LengthFrame ε n 4)]
    [Subsingleton (groupCohomology (frameCoefficients ε M n 3) 1)]
    (hn : 5 ≤ n) (L : LengthFrame ε n 5)
    (c : (inhomogeneousCochains (frameCoefficients ε M n 1)).X 2)
    (hc : (inhomogeneousCochains (frameCoefficients ε M n 1)).d 2 3 c = 0)
    (b : (inhomogeneousCochains (frameCoefficients ε M n 2)).X 1)
    (hb : frameCochainsCoboundary ε M n 1 2 c =
      (inhomogeneousCochains (frameCoefficients ε M n 2)).d 1 2 b) :
    ∃ (z : (inhomogeneousCochains (frameCoefficients ε M n 0)).X 2)
      (d : (inhomogeneousCochains (frameCoefficients ε M n 1)).X 1),
      (inhomogeneousCochains (frameCoefficients ε M n 0)).d 2 3 z = 0 ∧
      frameCochainsCoboundary ε M n 0 2 z =
        c - (inhomogeneousCochains (frameCoefficients ε M n 1)).d 1 2 d := by
  apply low_degree_lift
    (fun k q => (frameCochainsCoboundary ε M n k q).hom.toAddMonoidHom)
    (fun k q => ((inhomogeneousCochains (frameCoefficients ε M n k)).d q (q + 1)).hom.toAddMonoidHom)
    (fun k q x => congrArg (fun t => t x) (frameCochainsCoboundary_comp ε M n k q))
    (fun k q x => congrArg (fun t => t x)
      ((inhomogeneousCochains (frameCoefficients ε M n k)).d_comp_d q (q + 1) (q + 2)))
    (fun k q x => congrArg (fun t => t x) (frameCochainsCoboundary_comm ε M n k q))
    (fun k hk q x hx => frameCochainsCoboundary_exact ε M q (by omega) x hx)
    (frameCochainsCoboundary_zero_injective ε M 3 (by omega))
    (fun x hx => cochain_primitive_of_subsingleton (frameCoefficients ε M n 3) 0 x hx)
    (fun x hx hh => frame_zero_cochain_eq_zero ε M L x hx hh) c hc b hb

end
end Frames
end AllPrimeGroups
