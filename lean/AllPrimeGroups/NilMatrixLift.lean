import AllPrimeGroups.MatrixModel
import Mathlib.RingTheory.Nilpotent.Basic

/-! Reflection of invertibility through a split ring map with nil kernel.

The argument works in noncommutative rings. Applied to matrix rings, it converts a completion
over the residue field to an actual invertible completion over the coefficient algebra. -/

namespace AllPrimeGroups
namespace MatrixLifting

variable {B C : Type*} [Ring B] [Ring C]

theorem isUnit_iff_of_split_nil (ε : B →+* C) (σ : C →+* B)
    (hs : ε.comp σ = RingHom.id C) (hnil : ∀ b : B, ε b = 0 → IsNilpotent b) (b : B) :
    IsUnit b ↔ IsUnit (ε b) := by
  constructor
  · exact fun h => h.map ε
  · rintro ⟨v, hv⟩
    let U : Bˣ := Units.map σ.toMonoidHom v
    have hσ (c : C) : ε (σ c) = c := DFunLike.congr_fun hs c
    have hε : ε (U⁻¹ : Bˣ) = (v⁻¹ : Cˣ) := hσ _
    have hnil' : IsNilpotent ((U⁻¹ : Bˣ) * b - 1) := hnil _ (by
      rw [map_sub, map_mul, map_one, hε, ← hv, Units.inv_mul, sub_self])
    have hprod : IsUnit ((U⁻¹ : Bˣ) * b) := by
      simpa only [sub_add_cancel] using hnil'.isUnit_add_one
    exact (Units.isUnit_units_mul U⁻¹ b).mp hprod

theorem isUnit_iff_matrix_reduction (ε : B →+* C) (σ : C →+* B)
    (hs : ε.comp σ = RingHom.id C) {n : ℕ}
    (hnil : ∀ A : Matrix (Fin n) (Fin n) B, ε.mapMatrix A = 0 → IsNilpotent A)
    (A : Matrix (Fin n) (Fin n) B) : IsUnit A ↔ IsUnit (ε.mapMatrix A) := by
  apply isUnit_iff_of_split_nil ε.mapMatrix σ.mapMatrix _ hnil A
  rw [RingHom.mapMatrix_comp, hs, RingHom.mapMatrix_id]

end MatrixLifting
end AllPrimeGroups
