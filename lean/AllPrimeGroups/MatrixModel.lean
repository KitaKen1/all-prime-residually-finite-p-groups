/-
Adapted from OpenAI PeriodicGroups/Steinberg/PresentationModel.lean,
commit pinned in upstream/provenance.json. Apache-2.0, see upstream/OpenAI-LICENSE.
The mathematical definitions and the elementary representation proofs are retained.
-/
import AllPrimeGroups.SteinbergCore
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Matrix.Basis
import Mathlib.Tactic.Abel

namespace AllPrimeGroups
universe u

namespace Elementary

variable {n : ℕ} {R : Type u} [Ring R]

def e (p : Root n) (a : R) : (Matrix (Fin n) (Fin n) R)ˣ where
  val := 1 + Matrix.single p.row p.col a
  inv := 1 + Matrix.single p.row p.col (-a)
  val_inv := by simp [add_mul, mul_add, p.ne.symm, ← Matrix.single_neg, add_assoc]
  inv_val := by simp [add_mul, mul_add, p.ne.symm, ← Matrix.single_neg, add_assoc]

@[simp] theorem coe_e (p : Root n) (a : R) :
    ↑(e p a) = 1 + Matrix.single p.row p.col a := rfl

@[simp] theorem e_add (p : Root n) (a b : R) : e p (a + b) = e p a * e p b := by
  apply Units.ext
  simp [coe_e, add_mul, mul_add, p.ne.symm, Matrix.single_add, add_assoc]

@[simp] theorem e_zero (p : Root n) : e p (0 : R) = 1 := by
  apply Units.ext
  simp

@[simp] theorem e_inv (p : Root n) (a : R) : (e p a)⁻¹ = e p (-a) := by
  apply Units.ext
  rfl

theorem e_commute (p q : Root n) (h₁ : p.col ≠ q.row) (h₂ : p.row ≠ q.col)
    (a b : R) : Commute (e p a) (e q b) := by
  change e p a * e q b = e q b * e p a
  apply Units.ext
  simp only [Units.val_mul, coe_e, add_mul, mul_add, one_mul, mul_one,
    Matrix.single_mul_single_of_ne _ _ _ _ h₁,
    Matrix.single_mul_single_of_ne _ _ _ _ h₂.symm]
  abel

theorem e_mul (i j k : Fin n) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (a b : R) :
    bracket (e ⟨i, j, hij⟩ a) (e ⟨j, k, hjk⟩ b) = e ⟨i, k, hik⟩ (a * b) := by
  apply Units.ext
  simp only [bracket, e_inv, Units.val_mul, coe_e]
  simp only [add_mul, mul_add, one_mul, mul_one]
  simp [hij.symm, hjk.symm, hik.symm, ← Matrix.single_neg]
  abel

def representation : Steinberg n R →* (Matrix (Fin n) (Fin n) R)ˣ :=
  Steinberg.lift e e_add e_commute e_mul

@[simp] theorem representation_x (p : Root n) (a : R) :
    representation (Steinberg.x p a) = e p a := Steinberg.lift_x _ _ _ _ _ _

theorem e_injective (p : Root n) : Function.Injective (e p : R → _) := by
  intro a b h
  have h' := congrArg (fun g : (Matrix (Fin n) (Fin n) R)ˣ => g.val p.row p.col) h
  simpa [coe_e, p.ne] using h'

theorem x_injective (p : Root n) : Function.Injective (Steinberg.x p : R → _) := by
  intro a b h
  apply e_injective p
  simpa using congrArg representation h

theorem steinberg_infinite [Infinite R] (p : Root n) : Infinite (Steinberg n R) :=
  Infinite.of_injective _ (x_injective p)

end Elementary

end AllPrimeGroups
