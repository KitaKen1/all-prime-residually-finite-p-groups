import AllPrimeGroups.CongruencePGroup
import AllPrimeGroups.Separation
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.Index

/-! The set of nil augmentation elements parametrizes the congruence unit group.
Finite quotient separation is supplied explicitly; no grading hypothesis is hidden here. -/

namespace AllPrimeGroups.NilCongruence
noncomputable section

variable {R S : Type*} [Ring R] [Ring S]

abbrev Group (ε : R →+* S) := (Units.map ε.toMonoidHom).ker

/-- The bijection `a ↦ 1 + a`. It is a set equivalence, not an additive group map. -/
def kernelEquiv (ε : R →+* S) (hnil : ∀ a : R, ε a = 0 → IsNilpotent a) :
    {a : R // ε a = 0} ≃ Group ε where
  toFun a := ⟨(hnil a.val a.property).isUnit_one_add.unit, by
    apply Units.ext
    change ε (1 + a.val) = 1
    rw [map_add, map_one, a.property, add_zero]⟩
  invFun u := ⟨u.val.val - 1, by
    have hu : ε u.val.val = 1 := congrArg Units.val u.property
    rw [map_sub, hu, map_one, sub_self]⟩
  left_inv a := Subtype.ext (by change 1 + a.val - 1 = a.val; abel)
  right_inv u := Subtype.ext (Units.ext (by change 1 + (u.val.val - 1) = u.val.val; abel))

theorem card (ε : R →+* S) (hnil : ∀ a : R, ε a = 0 → IsNilpotent a) :
    Nat.card (Group ε) = Nat.card {a : R // ε a = 0} :=
  (Nat.card_congr (kernelEquiv ε hnil)).symm

theorem kernel_infinite [Infinite R] [Finite S] (ε : R →+* S) :
    Infinite {a : R // ε a = 0} := by
  change Infinite ε.toAddMonoidHom.ker
  by_contra! h
  have : Finite R := ε.toAddMonoidHom.finite_iff_finite_ker_range.mpr ⟨h, inferInstance⟩
  exact not_finite R

theorem infinite [Infinite R] [Finite S] (ε : R →+* S)
    (hnil : ∀ a : R, ε a = 0 → IsNilpotent a) : Infinite (Group ε) := by
  have := kernel_infinite ε
  exact Infinite.of_injective (kernelEquiv ε hnil) (kernelEquiv ε hnil).injective

/-- Finite coefficient quotients that meet in zero separate all units. -/
theorem units_residuallyFinite {ι : Type*} {Q : ι → Type*}
    [∀ i, Ring (Q i)] [∀ i, Finite (Q i)] (q : ∀ i, R →+* Q i)
    (hsep : ∀ a : R, (∀ i, q i a = 0) → a = 0) : Group.ResiduallyFinite Rˣ := by
  apply residuallyFinite_of_separating_family (fun i => Units.map (q i).toMonoidHom)
  intro u hu
  apply Units.ext
  have hz : u.val - 1 = 0 := hsep _ (fun i => by
    have hi : q i u.val = 1 := congrArg Units.val (hu i)
    rw [map_sub, hi, map_one, sub_self])
  exact sub_eq_zero.mp hz

theorem residuallyFinite (ε : R →+* S) {ι : Type*} {Q : ι → Type*}
    [∀ i, Ring (Q i)] [∀ i, Finite (Q i)] (q : ∀ i, R →+* Q i)
    (hsep : ∀ a : R, (∀ i, q i a = 0) → a = 0) :
    Group.ResiduallyFinite (Group ε) := by
  have := units_residuallyFinite q hsep
  infer_instance

/-- Exact cardinality over an arbitrary field; for a finite field this is a
prime-power formula after substituting its cardinality. -/
theorem card_eq_pow_finrank {K : Type*} [Field K] [Algebra K R] (ε : R →ₐ[K] K)
    (hnil : ∀ a : R, ε a = 0 → IsNilpotent a) [Module.Finite K ε.toLinearMap.ker] :
    Nat.card (Group ε.toRingHom) = Nat.card K ^ Module.finrank K ε.toLinearMap.ker := by
  rw [card ε.toRingHom hnil]
  exact Module.natCard_eq_pow_finrank (K := K) (V := ε.toLinearMap.ker)

set_option backward.isDefEq.respectTransparency false in
theorem card_eq_prime_pow_finrank {p : ℕ} [Fact p.Prime] [Algebra (ZMod p) R]
    (ε : R →ₐ[ZMod p] ZMod p) (hnil : ∀ a : R, ε a = 0 → IsNilpotent a)
    [Module.Finite (ZMod p) ε.toLinearMap.ker] :
    Nat.card (Group ε.toRingHom) = p ^ Module.finrank (ZMod p) ε.toLinearMap.ker := by
  have hc := card_eq_pow_finrank (K := ZMod p) ε hnil
  rw [Nat.card_zmod] at hc
  exact hc

theorem properties {p : ℕ} (hp : p.Prime) [CharP R p] [Infinite R] [Finite S]
    (ε : R →+* S) (hnil : ∀ a : R, ε a = 0 → IsNilpotent a)
    {ι : Type*} {Q : ι → Type*} [∀ i, Ring (Q i)] [∀ i, Finite (Q i)]
    (q : ∀ i, R →+* Q i) (hsep : ∀ a : R, (∀ i, q i a = 0) → a = 0) :
    Infinite (Group ε) ∧ Group.ResiduallyFinite (Group ε) ∧ IsPGroup p (Group ε) :=
  ⟨infinite ε hnil, residuallyFinite ε q hsep, units_congruence_isPGroup hp ε hnil⟩

end
end AllPrimeGroups.NilCongruence
