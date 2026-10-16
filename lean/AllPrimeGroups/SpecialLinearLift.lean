import AllPrimeGroups.KernelExtras
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.Tactic.Ring

/-! Over a field, every matrix of determinant one is the elementary image of an element of
the Steinberg group. This replaces the two-element-field statement used upstream, where
every invertible numerical matrix lifts. The diagonal part is treated by Whitehead's
identity; the reduction to a diagonal matrix is mathlib's transvection decomposition. -/

namespace AllPrimeGroups.Elementary
open Matrix
open scoped BigOperators

variable {N : ℕ} {K : Type*} [Field K]

/-- A matrix that is the elementary image of an element of the Steinberg group. -/
def Realized (A : Matrix (Fin N) (Fin N) K) : Prop :=
  ∃ g : Steinberg N K, (representation g).val = A

theorem realized_one : Realized (1 : Matrix (Fin N) (Fin N) K) := ⟨1, by simp⟩

theorem Realized.mul {A B : Matrix (Fin N) (Fin N) K} (hA : Realized A) (hB : Realized B) :
    Realized (A * B) := by
  obtain ⟨g, rfl⟩ := hA
  obtain ⟨k, rfl⟩ := hB
  exact ⟨g * k, by simp⟩

theorem realized_single (i j : Fin N) (hij : i ≠ j) (c : K) :
    Realized (1 + Matrix.single i j c) :=
  ⟨Steinberg.x ⟨i, j, hij⟩ c, by rw [representation_x]; rfl⟩

theorem realized_transvections (L : List (TransvectionStruct (Fin N) K)) :
    Realized (L.map TransvectionStruct.toMatrix).prod := by
  induction L with
  | nil => simpa using realized_one
  | cons t L ih =>
    rw [List.map_cons, List.prod_cons]
    exact (realized_single t.i t.j t.hij t.c).mul ih

/-- The product of three elementary matrices that interchanges two coordinates. -/
theorem interchange_eq (i j : Fin N) (hij : i ≠ j) (c d : K) (hcd : c * d = 1) :
    (1 + Matrix.single i j c) * (1 + Matrix.single j i (-d)) * (1 + Matrix.single i j c) =
      1 + Matrix.single i j c + Matrix.single j i (-d) + Matrix.single i i (-1) +
        Matrix.single j j (-1) := by
  have hdc : d * c = 1 := by rw [mul_comm]; exact hcd
  ext a b
  simp only [add_mul, mul_add, one_mul, mul_one, Matrix.single_mul_single_same,
    Matrix.single_mul_single_of_ne _ _ _ _ hij.symm, mul_neg, neg_mul, hcd, hdc,
    Matrix.add_apply, Matrix.single_apply, Matrix.zero_apply]
  by_cases hai : i = a <;> by_cases haj : j = a <;> by_cases hbi : i = b <;>
    by_cases hbj : j = b <;> simp_all [Matrix.one_apply]

/-- Whitehead's identity: a diagonal matrix with entries c and d in two positions. -/
theorem whitehead (i j : Fin N) (hij : i ≠ j) (c d : K) :
    (1 + Matrix.single i j c + Matrix.single j i (-d) + Matrix.single i i (-1) +
        Matrix.single j j (-1)) *
      (1 + Matrix.single i j (-1) + Matrix.single j i 1 + Matrix.single i i (-1) +
        Matrix.single j j (-1)) =
      1 + Matrix.single i i (c - 1) + Matrix.single j j (d - 1) := by
  ext a b
  simp only [add_mul, mul_add, one_mul, mul_one, Matrix.single_mul_single_same,
    Matrix.single_mul_single_of_ne _ _ _ _ hij, Matrix.single_mul_single_of_ne _ _ _ _ hij.symm,
    mul_neg, neg_neg, Matrix.add_apply, Matrix.single_apply, Matrix.zero_apply]
  by_cases hai : i = a <;> by_cases haj : j = a <;> by_cases hbi : i = b <;>
    by_cases hbj : j = b <;> simp_all [Matrix.one_apply]

theorem realized_torus (i j : Fin N) (hij : i ≠ j) (c d : K) (hcd : c * d = 1) :
    Realized (1 + Matrix.single i i (c - 1) + Matrix.single j j (d - 1)) := by
  rw [← whitehead i j hij c d, ← interchange_eq i j hij c d hcd]
  have h := interchange_eq i j hij (-1 : K) (-1) (by ring)
  rw [neg_neg] at h
  rw [← h]
  exact (((realized_single i j hij c).mul (realized_single j i hij.symm (-d))).mul
    (realized_single i j hij c)).mul
    (((realized_single i j hij (-1)).mul (realized_single j i hij.symm 1)).mul
      (realized_single i j hij (-1)))

end AllPrimeGroups.Elementary
