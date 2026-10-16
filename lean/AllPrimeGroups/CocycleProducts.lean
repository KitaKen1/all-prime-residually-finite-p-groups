/-
The multiplicative cocycle product proof is adapted from Yunzhou Xie and contributors,
LeanPool/BrauerGroupNew/Mathlib/RepresentationTheory/Homological/GroupCohomology/LowDegree.lean,
Apache-2.0; see upstream/LeanPool-LICENSE and upstream/LeanPool-provenance.json.
-/
import AllPrimeGroups.ExtensionCohomology

namespace AllPrimeGroups
namespace FactorSet

open groupCohomology

variable {G M : Type} [Group G] [CommGroup M] [MulDistribMulAction G M]

/-- Multiply the two central-extension cocycles pointwise. -/
def product (α β : FactorSet G M) : FactorSet G M where
  toFun p := α p * β p
  isMulCocycle₂' a b c := by
    simp [α.isMulCocycle₂ a b c, β.isMulCocycle₂ a b c, smul_mul', mul_mul_mul_comm]
  map_one_one' := by simp

@[simp] theorem product_apply (α β : FactorSet G M) (p : G × G) :
    product α β p = α p * β p := rfl

theorem toCocycles₂_product (α β : FactorSet G M) :
    (product α β).toCocycles₂ = α.toCocycles₂ + β.toCocycles₂ := by
  apply cocycles₂_ext
  intro g h
  rfl

/-- Products of factor sets realize sums of extension classes in H². -/
theorem cohomologyClass_product (α β : FactorSet G M) :
    (product α β).cohomologyClass = α.cohomologyClass + β.cohomologyClass := by
  simp only [cohomologyClass, toCocycles₂_product, map_add]

end FactorSet
end AllPrimeGroups
