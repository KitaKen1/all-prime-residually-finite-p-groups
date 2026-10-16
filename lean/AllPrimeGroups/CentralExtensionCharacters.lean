import AllPrimeGroups.FactorSetPullback

/-! Push a central-extension class through any character, retaining a lift of the total group.

The old kernel is allowed to arrive with only its original group structure. Its commutativity
is derived from centrality locally; the exported data only mentions the character coefficients. -/

namespace AllPrimeGroups
namespace CentralCocycles
noncomputable section
open CategoryTheory

@[instance_reducible]
def trivialAction (G A : Type*) [Group G] [Group A] : MulDistribMulAction G A where
  smul _ a := a
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_one _ := rfl
  smul_mul _ _ _ := rfl

local instance (G A : Type*) [Group G] [Group A] : MulDistribMulAction G A := trivialAction G A

variable {A E H M : Type} [Group A] [Group E] [Group H] [CommGroup M]

/-- A character-valued central cocycle and its compatible lift of the original extension. -/
structure CharacterData (S : GroupExtension A E H) (χ : A →* M) where
  cocycle : FactorSet H M
  lift : E →* cocycle.Extension
  projection : cocycle.rightHom.comp lift = S.rightHom
  kernel : ∀ a, lift (S.inl a) = cocycle.inl (χ a)

/-- Construct the character cocycle using any normalized section. -/
def characterData (S : GroupExtension A E H) (hc : S.inl.range ≤ Subgroup.center E)
    (χ : A →* M) (s : S.Section) (hs : s 1 = 1) : CharacterData S χ := by
  letI : CommGroup A :=
    { (inferInstance : Group A) with
      mul_comm a b := S.inl_injective (by
        rw [map_mul, map_mul]
        exact Subgroup.mem_center_iff.mp (hc ⟨b, rfl⟩) (S.inl a)) }
  have hact : GroupExtension.InducesAction S :=
    (GroupExtension.inducesAction_iff_smul_eq_self hc).mpr (fun _ _ => rfl)
  let α := GroupExtension.factorSet s hs hact
  let f : A →*[H] M := { χ with map_smul' := fun _ _ => rfl }
  let e := GroupExtension.factorSetToGroupExtensionEquiv s hs hact
  refine
    { cocycle := α.map f
      lift := (α.mapExtension f).comp e.symm.toMonoidHom
      projection := ?_
      kernel := ?_ }
  · apply MonoidHom.ext
    intro x
    change (e.symm x).right = S.rightHom x
    exact e.symm.rightHom_map x
  · intro a
    change α.mapExtension f (e.symm (S.inl a)) = (α.map f).inl (χ a)
    rw [e.symm.map_inl]
    rfl

/-- The character cocycle has the expected value on a pair of quotient elements. -/
theorem characterData_cocycle_apply (S : GroupExtension A E H)
    (hc : S.inl.range ≤ Subgroup.center E) (χ : A →* M) (s : S.Section) (hs : s 1 = 1)
    (g h : H) :
    (characterData S hc χ s hs).cocycle (g, h) = χ (GroupExtension.factorSetFun s (g, h)) := rfl

/-- Equality on a common cover kernel gives equality of character-valued H² pullbacks. -/
theorem CharacterData.pullback_class_eq (S : GroupExtension A E H) (χ : A →* M)
    (D : CharacterData S χ) {G V : Type} [Group G] [Group V]
    (p : V →* G) (hp : Function.Surjective p) (f₀ f₁ : G →* H) (q₀ q₁ : V →* E)
    (h₀ : S.rightHom.comp q₀ = f₀.comp p) (h₁ : S.rightHom.comp q₁ = f₁.comp p)
    (hker : ∀ x, p x = 1 → q₀ x = q₁ x) :
    groupCohomology.map f₀ (FactorSet.centralRestriction f₀ (fun _ _ => rfl)) 2
        D.cocycle.cohomologyClass =
      groupCohomology.map f₁ (FactorSet.centralRestriction f₁ (fun _ _ => rfl)) 2
        D.cocycle.cohomologyClass := by
  apply FactorSet.cohomologyClass_comp_eq_of_lifts D.cocycle (fun _ _ => rfl) p hp f₀ f₁
    (D.lift.comp q₀) (D.lift.comp q₁)
  · rw [← MonoidHom.comp_assoc, D.projection, h₀]
  · rw [← MonoidHom.comp_assoc, D.projection, h₁]
  · intro x hx
    exact congrArg D.lift (hker x hx)

end
end CentralCocycles
end AllPrimeGroups
