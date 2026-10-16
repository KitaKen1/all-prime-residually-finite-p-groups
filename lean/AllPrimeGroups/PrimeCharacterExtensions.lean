import AllPrimeGroups.PrimeCharacterRealization

/-! Realization of every central rational-circle character, and the all-prime target.
The character on the cover centre is restricted to its matrix kernel. Exactness identifies
every central element in the matrix kernel with such an included kernel element. -/

namespace AllPrimeGroups
namespace PrimeAlgebra
noncomputable section
open Frames FrameStabilizer

variable (p : ℕ) (hp : p.Prime) [Fact p.Prime]

set_option backward.isDefEq.respectTransparency false in
theorem character_extensions {m : ℕ} (hm : 7 ≤ m) :
    Central.CharacterExtensions (toSteinberg (m := m) (B := R p hp)) Elementary.representation := by
  intro χ
  let χk : (Elementary.representation (n := m) (R := R p hp)).ker →*
      Multiplicative (AddCircle (1 : ℚ)) :=
    (AddMonoidHom.toMultiplicativeRight χ).comp
      (kernelCenterInclusion (augmentation p hp) (unit_of_augmentation_ne_zero p hp) (by omega))
  obtain ⟨V, hV, π, i, ψ, hi, hrange, hcentral, hψ, hχ⟩ := kernel_character_realization p hp hm χk
  refine ⟨V, hV, π, i, ψ, hi, hrange, hcentral, hψ, ?_⟩
  intro z hz
  have hzM : toMatrix z.val = 1 := by
    have h := DFunLike.congr_fun (representation_toSteinberg (m := m) (B := R p hp)) z.val
    exact h.symm.trans hz
  have hzS : toLastColumn z.val = 1 := Subtype.ext (Subtype.ext hzM)
  have hzker : z.val ∈ (kernelInclusion (m := m) (B := R p hp)).range := by
    rw [range_kernelInclusion, MonoidHom.mem_ker]
    exact hzS
  obtain ⟨j, hj⟩ := hzker
  have he : kernelCenterInclusion (augmentation p hp) (unit_of_augmentation_ne_zero p hp)
      (show 6 ≤ m by omega) j = z := Subtype.ext hj
  rw [← hj, hχ]
  exact congrArg (fun a => i ((AddMonoidHom.toMultiplicativeRight χ) a)) he

theorem stabilization_injective (n : ℕ) (hn : 7 ≤ n) :
    Function.Injective (Stable.of (R p hp) n) := by
  apply Stable.of_injective_of_characters (augmentation p hp) (unit_of_augmentation_ne_zero p hp)
    n (by omega)
  intro m hm
  exact character_extensions p hp (by omega)

end
end PrimeAlgebra

/-- The concrete character-extension obligation holds in all the required ranks. -/
theorem primeCharacterExtensions : PrimeCharacterExtensions := by
  intro p hp m hm
  have : Fact p.Prime := ⟨hp⟩
  exact PrimeAlgebra.character_extensions p hp (by omega)

/-- Every prime admits an infinite finitely presented residually finite p-group. -/
theorem all_prime_groups : Target := target_of_character_extensions primeCharacterExtensions

end AllPrimeGroups
