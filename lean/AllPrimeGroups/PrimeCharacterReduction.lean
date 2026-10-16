import AllPrimeGroups.StabilityCharacters
import AllPrimeGroups.PrimeSeparation

/-! The character-extension route connected to the all-prime target.

Injectivity of each successor map in the tail of a chain suffices for injectivity into its
direct limit. Applied to the character criterion, this reduces the final target to the explicit
character-extension obligation in ranks at least twelve. This module does not prove that
obligation. -/

namespace AllPrimeGroups

namespace Chain

variable {C : ℕ → Type*} [∀ n, Group (C n)]

theorem connect_injective_from (step : ∀ n, C n →* C (n + 1)) (n : ℕ)
    (hinj : ∀ k, n ≤ k → Function.Injective (step k)) (m : ℕ) (h : n ≤ m) :
    Function.Injective (connect step n m h) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  induction k with
  | zero =>
    simpa [connect, Nat.leRecOn_self] using
      (Function.injective_id : Function.Injective (id : C n → C n))
  | succ k ih =>
    simp only [Nat.add_succ] at h ⊢
    rw [connect_succ step n (n + k) (Nat.le_add_right n k)]
    exact (hinj (n + k) (Nat.le_add_right n k)).comp (ih (Nat.le_add_right n k))

theorem of_injective_from (step : ∀ n, C n →* C (n + 1)) (n : ℕ)
    (hinj : ∀ k, n ≤ k → Function.Injective (step k)) : Function.Injective (of step n) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  obtain ⟨m, hm, hmx⟩ := (of_eq_one_iff step n x).mp (MonoidHom.mem_ker.mp hx)
  have hx' : x = 1 := connect_injective_from step n hinj m hm (hmx.trans (map_one _).symm)
  rw [hx']
  exact Subgroup.one_mem _

end Chain

namespace Stable

variable {B : Type*} [Ring B] {K : Type*} [Field K]

theorem of_injective_of_characters (ε : B →+* K) (hunit : ∀ b : B, ε b ≠ 0 → IsUnit b)
    (n : ℕ) (hn : 6 ≤ n)
    (hext : ∀ m, n ≤ m → Central.CharacterExtensions
      (FrameStabilizer.toSteinberg (m := m) (B := B)) Elementary.representation) :
    Function.Injective (of B n) := by
  apply Chain.of_injective_from (steinbergStep B) n
  intro m hm
  exact FrameStabilizer.pad_injective_of_characters ε hunit (by omega) (hext m hm)

end Stable

namespace PrimeAlgebra

theorem augmentation_kernel_nil (p : ℕ) (hp : p.Prime) (b : R p hp)
    (hb : augmentation p hp b = 0) : IsNilpotent b := by
  let M : Matrix (Fin 1) (Fin 1) (R p hp) := Matrix.diagonal (fun _ => b)
  have hM : (augmentation p hp).mapMatrix M = 0 := by
    ext i j
    have hij : i = j := Subsingleton.elim i j
    subst j
    simpa [M, RingHom.mapMatrix_apply] using hb
  obtain ⟨k, hk⟩ := matrix_nil p hp 1 M hM
  refine ⟨k, ?_⟩
  have h := congrArg (fun A : Matrix (Fin 1) (Fin 1) (R p hp) => A 0 0) hk
  simpa [M, Matrix.diagonal_pow] using h

theorem unit_of_augmentation_ne_zero (p : ℕ) (hp : p.Prime) (b : R p hp)
    (hb : augmentation p hp b ≠ 0) : IsUnit b := by
  have : Fact p.Prime := ⟨hp⟩
  exact (isUnit_iff_augmentation_ne_zero
    (OAI.SourceBurnside.ConcreteSource.machine.augmentation (threshold_le_height p hp) (ZMod p))
    (augmentation_kernel_nil p hp) b).mpr hb

end PrimeAlgebra

/-- The remaining concrete cohomological obligation, stated without assuming any injectivity. -/
def PrimeCharacterExtensions : Prop :=
  ∀ (p : ℕ) (hp : p.Prime) (m : ℕ), 12 ≤ m →
    Central.CharacterExtensions
      (FrameStabilizer.toSteinberg (m := m) (B := PrimeAlgebra.R p hp)) Elementary.representation

theorem target_of_character_extensions (h : PrimeCharacterExtensions) : Target := by
  apply Phases.target_of_injective
  intro p hp
  have : Fact p.Prime := ⟨hp⟩
  exact Stable.of_injective_of_characters (PrimeAlgebra.augmentation p hp)
    (PrimeAlgebra.unit_of_augmentation_ne_zero p hp) 12 (by omega) (h p hp)

end AllPrimeGroups
