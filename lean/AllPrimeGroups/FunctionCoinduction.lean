import Mathlib.RepresentationTheory.Coinduced
import Mathlib.GroupTheory.GroupAction.Quotient

/-! Functions on a homogeneous space as coinduction of trivial coefficients.

The inverse in `g ↦ f(g⁻¹ S)` converts the left action on `G/S` to Mathlib's
right-translation convention for coinduction. No finite-index hypothesis is used. -/

namespace AllPrimeGroups
namespace Homogeneous
noncomputable section
open CategoryTheory QuotientGroup

universe u

variable {k G X M : Type u} [CommRing k] [Group G] [MulAction G X]
  [AddCommGroup M] [Module k M]

/-- The contragredient action on all coefficient functions. -/
def functionRepresentation (k G X M : Type u) [CommRing k] [Group G] [MulAction G X]
    [AddCommGroup M] [Module k M] : Representation k G (X → M) where
  toFun g := LinearMap.funLeft k M (fun x => g⁻¹ • x)
  map_one' := by ext f x; simp
  map_mul' g h := by ext f x; simp [mul_smul]

abbrev functionRep : Rep k G := Rep.of (functionRepresentation k G X M)

@[simp] theorem functionRep_apply (g : G) (f : X → M) (x : X) :
    (functionRep (k := k) (G := G) (X := X) (M := M)).ρ g f x = f (g⁻¹ • x) := rfl

/-- Pullback along an equivariant map is a morphism of representations. -/
def functionPullback {Y : Type u} [MulAction G Y] (a : X → Y)
    (ha : ∀ (g : G) (x : X), a (g • x) = g • a x) :
    functionRep (k := k) (G := G) (X := Y) (M := M) ⟶
      functionRep (k := k) (G := G) (X := X) (M := M) :=
  Rep.ofHom ⟨LinearMap.funLeft k M a, fun g => by
    ext f x
    exact congrArg f (ha g⁻¹ x).symm⟩

/-- An equivariant bijection gives an isomorphism of function representations. -/
def functionIso {Y : Type u} [MulAction G Y] (e : X ≃ Y)
    (he : ∀ (g : G) (x : X), e (g • x) = g • e x) :
    functionRep (k := k) (G := G) (X := Y) (M := M) ≅
      functionRep (k := k) (G := G) (X := X) (M := M) :=
  Rep.mkIso <| .mk (LinearEquiv.funCongrLeft k M e) (fun g => by
    ext f x
    exact congrArg f (he g⁻¹ x).symm)

variable (S : Subgroup G)

/-- A left-coset function gives a left `S`-invariant function on `G` by inversion. -/
def cosetToCoind : (G ⧸ S → M) →ₗ[k]
    Representation.coindV S.subtype (Representation.trivial k S M) where
  toFun f := ⟨fun g => f (QuotientGroup.mk g⁻¹), fun s g => by
    change f (QuotientGroup.mk ((s : G) * g)⁻¹) = f (QuotientGroup.mk g⁻¹)
    apply congrArg f
    apply Quotient.sound'
    rw [leftRel_apply]
    simp⟩
  map_add' f h := rfl
  map_smul' c f := rfl

/-- Descend an `S`-invariant function after inversion. -/
def coindToCoset
    (f : Representation.coindV S.subtype (Representation.trivial k S M)) : G ⧸ S → M :=
  fun q => Quotient.liftOn' q (fun g => f.val g⁻¹) (fun g h heq => by
    have hs : h⁻¹ * g ∈ S := by
      simpa using S.inv_mem (leftRel_apply.mp heq)
    have hh := f.property ⟨h⁻¹ * g, hs⟩ g⁻¹
    simpa using hh.symm)

def cosetCoindEquiv : (G ⧸ S → M) ≃ₗ[k]
    Representation.coindV S.subtype (Representation.trivial k S M) where
  __ := cosetToCoind (k := k) (M := M) S
  invFun := coindToCoset S
  left_inv f := by
    funext q
    refine Quotient.inductionOn' q (fun g => ?_)
    change f (QuotientGroup.mk g⁻¹⁻¹) = f (QuotientGroup.mk g)
    rw [inv_inv]
  right_inv f := by
    apply Subtype.ext
    funext g
    change f.val g⁻¹⁻¹ = f.val g
    rw [inv_inv]

/-- The function representation on `G/S` is coinduced from trivial coefficients on `S`. -/
def cosetCoindIso :
    functionRep (k := k) (G := G) (X := G ⧸ S) (M := M) ≅
      Rep.coind S.subtype (Rep.trivial k S M) :=
  Rep.mkIso <| .mk (cosetCoindEquiv (k := k) (M := M) S) (fun g => by
    ext f h
    change f (g⁻¹ • (QuotientGroup.mk h⁻¹ : G ⧸ S)) =
      f (QuotientGroup.mk (h * g)⁻¹)
    simp [mul_inv_rev])

@[simp] theorem cosetCoindIso_hom_apply (f : G ⧸ S → M) (g : G) :
    ((cosetCoindIso (k := k) (M := M) S).hom.hom f).val g =
      f (QuotientGroup.mk g⁻¹) := rfl

/-- All functions on an equivariant homogeneous-space model are coinduced. -/
def orbitCoindIso (e : (G ⧸ S) ≃ X)
    (he : ∀ (g : G) (q : G ⧸ S), e (g • q) = g • e q) :
    functionRep (k := k) (G := G) (X := X) (M := M) ≅
      Rep.coind S.subtype (Rep.trivial k S M) :=
  functionIso e he ≪≫ cosetCoindIso S

theorem orbitCoindIso_hom_apply (e : (G ⧸ S) ≃ X)
    (he : ∀ (g : G) (q : G ⧸ S), e (g • q) = g • e q) (f : X → M) (g : G) :
    ((orbitCoindIso (k := k) (M := M) S e he).hom.hom f).val g =
      f (e (QuotientGroup.mk g⁻¹)) := rfl

end
end Homogeneous
end AllPrimeGroups
