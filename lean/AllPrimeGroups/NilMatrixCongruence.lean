import AllPrimeGroups.NilCongruence
import Mathlib.LinearAlgebra.Matrix.CharP

/-! Matrix versions of the nil augmentation unit group, including its exact cardinality.
Matrix nilpotence is a separate explicit hypothesis, stronger than scalar nilpotence. -/

namespace AllPrimeGroups.NilCongruence
noncomputable section

variable {R S : Type*} [Ring R] [Ring S] (ε : R →+* S) (n : ℕ)

abbrev MatrixGroup := Group (ε.mapMatrix : Matrix (Fin n) (Fin n) R →+* _)

/-- A matrix is in the augmentation kernel exactly when each entry is. -/
def matrixKernelEquiv :
    {M : Matrix (Fin n) (Fin n) R // ε.mapMatrix M = 0} ≃
      Matrix (Fin n) (Fin n) {a : R // ε a = 0} where
  toFun M i j := ⟨M.val i j, congrFun (congrFun M.property i) j⟩
  invFun M := ⟨fun i j => (M i j).val, by
    ext i j
    exact (M i j).property⟩
  left_inv M := Subtype.ext rfl
  right_inv M := by rfl

set_option backward.isDefEq.respectTransparency false in
theorem matrix_card
    (hnil : ∀ M : Matrix (Fin n) (Fin n) R, ε.mapMatrix M = 0 → IsNilpotent M) :
    Nat.card (MatrixGroup ε n) = Nat.card {a : R // ε a = 0} ^ (n * n) := by
  change Nat.card (Group (ε.mapMatrix : Matrix (Fin n) (Fin n) R →+* _)) = _
  rw [card (ε.mapMatrix : Matrix (Fin n) (Fin n) R →+* _) hnil,
    Nat.card_congr (matrixKernelEquiv ε n)]
  simp only [Matrix, Nat.card_fun, Nat.card_fin, ← pow_mul]

theorem matrix_card_eq_pow_finrank {K : Type*} [Field K] [Algebra K R]
    (α : R →ₐ[K] K)
    (hnil : ∀ M : Matrix (Fin n) (Fin n) R, α.toRingHom.mapMatrix M = 0 → IsNilpotent M)
    [Module.Finite K α.toLinearMap.ker] :
    Nat.card (MatrixGroup α.toRingHom n) =
      Nat.card K ^ (n * n * Module.finrank K α.toLinearMap.ker) := by
  rw [matrix_card α.toRingHom n hnil]
  have hc : Nat.card {a : R // α.toRingHom a = 0} =
      Nat.card K ^ Module.finrank K α.toLinearMap.ker :=
    Module.natCard_eq_pow_finrank (K := K) (V := α.toLinearMap.ker)
  rw [hc, ← pow_mul, Nat.mul_comm (Module.finrank K α.toLinearMap.ker)]

set_option backward.isDefEq.respectTransparency false in
theorem matrix_card_eq_prime_pow_finrank {p : ℕ} [Fact p.Prime] [Algebra (ZMod p) R]
    (α : R →ₐ[ZMod p] ZMod p)
    (hnil : ∀ M : Matrix (Fin n) (Fin n) R, α.toRingHom.mapMatrix M = 0 → IsNilpotent M)
    [Module.Finite (ZMod p) α.toLinearMap.ker] :
    Nat.card (MatrixGroup α.toRingHom n) =
      p ^ (n * n * Module.finrank (ZMod p) α.toLinearMap.ker) := by
  have hc := matrix_card_eq_pow_finrank (K := ZMod p) n α hnil
  rw [Nat.card_zmod] at hc
  exact hc

set_option backward.isDefEq.respectTransparency false in
theorem matrix_infinite [Infinite R] [Finite S] (hn : 0 < n)
    (hnil : ∀ M : Matrix (Fin n) (Fin n) R, ε.mapMatrix M = 0 → IsNilpotent M) :
    Infinite (MatrixGroup ε n) := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have := kernel_infinite ε
  let e := (matrixKernelEquiv ε n).symm.trans
    (kernelEquiv (ε.mapMatrix : Matrix (Fin n) (Fin n) R →+* _) hnil)
  have : Infinite (Matrix (Fin n) (Fin n) {a : R // ε a = 0}) :=
    Infinite.of_injective (fun a => fun _ _ => a) (by
      intro a b hab
      exact congrFun (congrFun hab ⟨0, hn⟩) ⟨0, hn⟩)
  exact Infinite.of_injective e e.injective

/-- Entrywise finite quotient separation lifts to the full matrix unit group. -/
theorem matrix_units_residuallyFinite {ι : Type*} {Q : ι → Type*}
    [∀ i, Ring (Q i)] [∀ i, Finite (Q i)] (q : ∀ i, R →+* Q i)
    (hsep : ∀ a : R, (∀ i, q i a = 0) → a = 0) :
    Group.ResiduallyFinite (Matrix (Fin n) (Fin n) R)ˣ := by
  apply units_residuallyFinite (fun i => (q i).mapMatrix)
  intro M hM
  ext i j
  exact hsep (M i j) (fun d => congrFun (congrFun (hM d) i) j)

theorem matrix_residuallyFinite {ι : Type*} {Q : ι → Type*}
    [∀ i, Ring (Q i)] [∀ i, Finite (Q i)] (q : ∀ i, R →+* Q i)
    (hsep : ∀ a : R, (∀ i, q i a = 0) → a = 0) :
    Group.ResiduallyFinite (MatrixGroup ε n) := by
  have := matrix_units_residuallyFinite n q hsep
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- Scalar characteristic suffices in positive rank; the rank-zero group is trivial. -/
theorem matrix_isPGroup {p : ℕ} (hp : p.Prime) [CharP R p]
    (hnil : ∀ M : Matrix (Fin n) (Fin n) R, ε.mapMatrix M = 0 → IsNilpotent M) :
    IsPGroup p (MatrixGroup ε n) := by
  by_cases hn : 0 < n
  · have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    exact units_congruence_isPGroup hp (A := Matrix (Fin n) (Fin n) R)
      (B := Matrix (Fin n) (Fin n) S) ε.mapMatrix hnil
  · have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    intro g
    exact ⟨0, Subsingleton.elim _ _⟩

set_option backward.isDefEq.respectTransparency false in
theorem matrix_properties {p : ℕ} (hp : p.Prime) [CharP R p] [Infinite R] [Finite S]
    (hn : 0 < n)
    (hnil : ∀ M : Matrix (Fin n) (Fin n) R, ε.mapMatrix M = 0 → IsNilpotent M)
    {ι : Type*} {Q : ι → Type*} [∀ i, Ring (Q i)] [∀ i, Finite (Q i)]
    (q : ∀ i, R →+* Q i) (hsep : ∀ a : R, (∀ i, q i a = 0) → a = 0) :
    Infinite (MatrixGroup ε n) ∧ Group.ResiduallyFinite (MatrixGroup ε n) ∧
      IsPGroup p (MatrixGroup ε n) := by
  exact ⟨matrix_infinite ε n hn hnil, matrix_residuallyFinite ε n q hsep,
    matrix_isPGroup ε n hp hnil⟩

end
end AllPrimeGroups.NilCongruence
