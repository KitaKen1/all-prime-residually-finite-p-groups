import AllPrimeGroups.CentralExtensionCharacters
import AllPrimeGroups.HomogeneousShapiro

/-! Realizing a restriction equality of central H² classes by a compatible homomorphism.
Pull back the ambient factor set, use the existing equivalence of cohomologous extensions,
then map the pulled-back extension into the ambient one. Kernel values are preserved. -/

namespace AllPrimeGroups
namespace CentralCocycles
noncomputable section
open CategoryTheory _root_.groupCohomology

local instance (G A : Type*) [Group G] [Group A] : MulDistribMulAction G A := trivialAction G A

variable {G H E A M : Type} [Group G] [Group H] [Group E] [Group A] [CommGroup M]

def pullback (α : FactorSet H M) (f : G →* H) : FactorSet G M where
  toFun p := α (f p.1, f p.2)
  isMulCocycle₂' g h j := by
    have hα := α.isMulCocycle₂ (f g) (f h) (f j)
    change α (f g * f h, f j) * α (f g, f h) = α (f h, f j) * α (f g, f h * f j) at hα
    change α (f (g * h), f j) * α (f g, f h) = α (f h, f j) * α (f g, f (h * j))
    simpa only [map_mul] using hα
  map_one_one' := by simp

def pullbackMap (α : FactorSet H M) (f : G →* H) : (pullback α f).Extension →* α.Extension where
  toFun x := ⟨x.left, f x.right⟩
  map_one' := by ext <;> simp
  map_mul' x y := by
    apply FactorSet.Extension.ext
    · rfl
    · exact map_mul f x.right y.right

set_option backward.isDefEq.respectTransparency false in
theorem pullback_class (α : FactorSet H M) (f : G →* H) :
    map f (Homogeneous.trivialRestriction (k := ℤ) (M := Additive M) f) 2 α.cohomologyClass =
      (pullback α f).cohomologyClass := by
  have h := congrArg (fun t => t.hom α.toCocycles₂)
    (H2π_comp_map f (Homogeneous.trivialRestriction (k := ℤ) (M := Additive M) f))
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- An ambient H² lift realizes the original character by a homomorphism of central extensions. -/
theorem CharacterData.exists_lift (S : GroupExtension A E G) (χ : A →* M)
    (D : CharacterData S χ) (α : FactorSet H M) (f : G →* H)
    (hclass : map f (Homogeneous.trivialRestriction (k := ℤ) (M := Additive M) f) 2
      α.cohomologyClass = D.cocycle.cohomologyClass) :
    ∃ ψ : E →* α.Extension,
      α.rightHom.comp ψ = f.comp S.rightHom ∧
      ∀ a, ψ (S.inl a) = α.inl (χ a) := by
  have heq : D.cocycle.cohomologyClass = (pullback α f).cohomologyClass :=
    hclass.symm.trans (pullback_class α f)
  obtain ⟨e⟩ := FactorSet.nonempty_groupExtensionEquiv D.cocycle (pullback α f)
    ((FactorSet.cohomologyClass_eq_iff _ _).mp heq)
  let ψ := (pullbackMap α f).comp (e.toMulEquiv.toMonoidHom.comp D.lift)
  refine ⟨ψ, ?_, ?_⟩
  · apply MonoidHom.ext
    intro x
    change f (e (D.lift x)).right = f (S.rightHom x)
    have he := e.rightHom_map (D.lift x)
    change (e (D.lift x)).right = (D.lift x).right at he
    rw [he]
    exact congrArg f (DFunLike.congr_fun D.projection x)
  · intro a
    change pullbackMap α f (e (D.lift (S.inl a))) = α.inl (χ a)
    rw [D.kernel]
    have he := e.map_inl (χ a)
    change e (D.cocycle.inl (χ a)) = (pullback α f).inl (χ a) at he
    rw [he]
    apply FactorSet.Extension.ext
    · rfl
    · exact map_one f

end
end CentralCocycles
end AllPrimeGroups
