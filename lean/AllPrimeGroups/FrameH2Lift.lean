import AllPrimeGroups.FrameLowDegreeLift
import AllPrimeGroups.FrameAugmentation

/-! A frame-coefficient H² class killed by the next face differential comes from constant
coefficients. This is the low-degree edge lifting statement, with its orbit and H¹ inputs explicit. -/

namespace AllPrimeGroups
namespace Frames
noncomputable section
open CategoryTheory groupCohomology
variable {B K : Type} [Ring B] [Field K] (ε : B →+* K) {n : ℕ}

set_option backward.isDefEq.respectTransparency false in
theorem frameH2_lift_empty (M : Type) [AddCommGroup M] [DivisibleBy M ℤ]
    [MulAction.IsPretransitive (K1.E n B) (LengthFrame ε n 4)]
    [Subsingleton (groupCohomology (frameCoefficients ε M n 3) 1)]
    (hn : 5 ≤ n) (L : LengthFrame ε n 5)
    (x : groupCohomology (frameCoefficients ε M n 1) 2)
    (hx : map (MonoidHom.id (K1.E n B)) (frameCoboundary ε M n 1) 2 x = 0) :
    ∃ y : groupCohomology (frameCoefficients ε M n 0) 2,
      map (MonoidHom.id (K1.E n B)) (frameCoboundary ε M n 0) 2 y = x := by
  induction x using groupCohomology_induction_on with
  | h x =>
    let c := iCocycles (frameCoefficients ε M n 1) 2 x
    have hc : (inhomogeneousCochains (frameCoefficients ε M n 1)).d 2 3 c = 0 :=
      congrArg (fun t => t x) ((inhomogeneousCochains (frameCoefficients ε M n 1)).iCycles_d 2 3)
    let dx := cocyclesMap (MonoidHom.id (K1.E n B)) (frameCoboundary ε M n 1) 2 x
    have hdx : π (frameCoefficients ε M n 2) 2 dx = 0 := by
      have h := congrArg (fun t => t x)
        (π_map (MonoidHom.id (K1.E n B)) (frameCoboundary ε M n 1) 2)
      exact h.symm.trans hx
    obtain ⟨b, hb⟩ := (cochain_boundary_iff (frameCoefficients ε M n 2) 1 dx).mp hdx
    have hb' : frameCochainsCoboundary ε M n 1 2 c =
        (inhomogeneousCochains (frameCoefficients ε M n 2)).d 1 2 b :=
      (cochain_map_cocycle _ (frameCoboundary ε M n 1) 2 x).symm.trans hb.symm
    obtain ⟨z, d, hz, hzd⟩ := frame_low_degree_lift ε M hn L c hc b hb'
    have hz' : _root_.inhomogeneousCochains.d (frameCoefficients ε M n 0) 2 z = 0 := by
      rwa [inhomogeneousCochains.d_def] at hz
    let y := cocyclesMk z hz'
    refine ⟨π (frameCoefficients ε M n 0) 2 y, ?_⟩
    have hnat := congrArg (fun t => t y)
      (π_map (MonoidHom.id (K1.E n B)) (frameCoboundary ε M n 0) 2)
    apply hnat.trans
    apply (cochain_class_eq_iff (frameCoefficients ε M n 1) 1 _ x).mpr
    refine ⟨-d, ?_⟩
    rw [map_neg]
    change -((inhomogeneousCochains (frameCoefficients ε M n 1)).d 1 2 d) =
      iCocycles (frameCoefficients ε M n 1) 2
        (cocyclesMap (MonoidHom.id (K1.E n B)) (frameCoboundary ε M n 0) 2 y) - c
    rw [cochain_map_cocycle, iCocycles_mk]
    change -((inhomogeneousCochains (frameCoefficients ε M n 1)).d 1 2 d) =
      frameCochainsCoboundary ε M n 0 2 z - c
    rw [hzd]
    abel

set_option backward.isDefEq.respectTransparency false in
/-- The initial horizontal H² cycle is in the image of the constant-coefficient augmentation. -/
theorem frameH2_lift (M : Type) [AddCommGroup M] [DivisibleBy M ℤ]
    [MulAction.IsPretransitive (K1.E n B) (LengthFrame ε n 4)]
    [Subsingleton (groupCohomology (frameCoefficients ε M n 3) 1)]
    (hn : 5 ≤ n) (L : LengthFrame ε n 5)
    (x : groupCohomology (frameCoefficients ε M n 1) 2)
    (hx : map (MonoidHom.id (K1.E n B)) (frameCoboundary ε M n 1) 2 x = 0) :
    ∃ y : groupCohomology (Rep.trivial ℤ (K1.E n B) M) 2,
      map (MonoidHom.id (K1.E n B)) (frameAugmentation ε M n) 2 y = x := by
  obtain ⟨y, hy⟩ := frameH2_lift_empty ε M hn L x hx
  let e : groupCohomology (Rep.trivial ℤ (K1.E n B) M) 2 ≅
      groupCohomology (frameCoefficients ε M n 0) 2 :=
    (groupCohomology.functor ℤ (K1.E n B) 2).mapIso (frameAugmentationIso ε M n)
  refine ⟨e.inv y, ?_⟩
  rw [frameAugmentation, map_id_comp]
  change map (MonoidHom.id (K1.E n B)) (frameCoboundary ε M n 0) 2 (e.hom (e.inv y)) = x
  have he : e.hom (e.inv y) = y := e.toLinearEquiv.apply_symm_apply y
  rw [he, hy]

end
end Frames
end AllPrimeGroups
