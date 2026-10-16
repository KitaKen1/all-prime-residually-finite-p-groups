import AllPrimeGroups.FunctionCoinduction
import AllPrimeGroups.ExplicitShapiro

/-! Shapiro on a transitive set, explicitly evaluated at its standard point.

The naturality statement applies to an equivariant face whose standard point maps to the
standard point of the target. This is the form needed for the normalized stabilizer faces. -/

namespace AllPrimeGroups
namespace Homogeneous
noncomputable section
open CategoryTheory QuotientGroup

universe u
variable {k G X M : Type u} [CommRing k] [Group G] [MulAction G X]
  [AddCommGroup M] [Module k M]
variable (S : Subgroup G) (e : (G ⧸ S) ≃ X)
  (he : ∀ (g : G) (q : G ⧸ S), e (g • q) = g • e q)

/-- Evaluation at the standard point, as a morphism for its stabilizer. -/
def orbitEvaluation :
    Rep.res S.subtype (functionRep (k := k) (G := G) (X := X) (M := M)) ⟶
      Rep.trivial k S M :=
  (Rep.resCoindHomEquiv.{u} S.subtype _ _).symm (orbitCoindIso S e he).hom

@[simp] theorem orbitEvaluation_apply (f : X → M) :
    (orbitEvaluation (k := k) (M := M) S e he).hom f = f (e (QuotientGroup.mk 1)) := by
  change f (e (QuotientGroup.mk (1 : G)⁻¹)) = _
  rw [inv_one]

theorem orbitEvaluation_adjunct :
    Rep.resCoindToHom S.subtype _ _ (orbitEvaluation (k := k) (M := M) S e he) =
      (orbitCoindIso S e he).hom :=
  (Rep.resCoindHomEquiv.{u} S.subtype _ _).apply_symm_apply _

/-- Shapiro for all functions on a homogeneous space, in every cohomological degree. -/
def orbitShapiroIso (n : ℕ) :
    groupCohomology (functionRep (k := k) (G := G) (X := X) (M := M)) n ≅
      groupCohomology (Rep.trivial k S M) n :=
  (groupCohomology.functor k G n).mapIso (orbitCoindIso S e he) ≪≫
    groupCohomology.coindIso (Rep.trivial k S M) n

set_option backward.isDefEq.respectTransparency false in
/-- The abstract Shapiro isomorphism is exactly restriction followed by point evaluation. -/
theorem orbitShapiroIso_hom (n : ℕ) :
    (orbitShapiroIso (k := k) (M := M) S e he n).hom =
      groupCohomology.map S.subtype (orbitEvaluation S e he) n := by
  have h : (orbitShapiroIso (k := k) (M := M) S e he n).hom = _ := Iso.trans_hom _ _
  rw [h, Functor.mapIso_hom, groupCohomology.functor_map,
    AllPrimeGroups.groupCohomology.coindIso_hom, ← groupCohomology.map_comp]
  apply groupCohomology.map_congr rfl
  rfl

/-- The identity of trivial coefficients across a change of groups. -/
def trivialRestriction {H L : Type u} [Group H] [Group L] (f : H →* L) :
    Rep.res f (Rep.trivial k L M) ⟶ Rep.trivial k H M :=
  Rep.ofHom ⟨LinearMap.id, fun _ => rfl⟩

variable {Y : Type u} [MulAction G Y] (T : Subgroup G)
  (d : (G ⧸ T) ≃ Y) (hd : ∀ (g : G) (q : G ⧸ T), d (g • q) = g • d q)

set_option backward.isDefEq.respectTransparency false in
/-- A face preserving the standard points becomes subgroup restriction under Shapiro. -/
theorem orbitShapiroIso_naturality (a : X → Y)
    (ha : ∀ (g : G) (x : X), a (g • x) = g • a x) (hST : S ≤ T)
    (hbase : a (e (QuotientGroup.mk 1)) = d (QuotientGroup.mk 1)) (n : ℕ) :
    groupCohomology.map (MonoidHom.id G) (functionPullback (k := k) (M := M) a ha) n ≫
        (orbitShapiroIso S e he n).hom =
      (orbitShapiroIso T d hd n).hom ≫
        groupCohomology.map (Subgroup.inclusion hST)
          (trivialRestriction (k := k) (M := M) (Subgroup.inclusion hST)) n := by
  rw [orbitShapiroIso_hom, orbitShapiroIso_hom, ← groupCohomology.map_comp,
    ← groupCohomology.map_comp]
  apply groupCohomology.map_congr rfl
  ext f
  change f (a (e (QuotientGroup.mk (1 : G)⁻¹))) =
    f (d (QuotientGroup.mk (1 : G)⁻¹))
  simpa only [inv_one] using congrArg f hbase

end
end Homogeneous
end AllPrimeGroups
