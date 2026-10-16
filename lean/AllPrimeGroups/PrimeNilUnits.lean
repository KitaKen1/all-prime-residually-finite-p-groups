import AllPrimeGroups.NilMatrixCongruence
import AllPrimeGroups.PrimeCharacterReduction
import AllPrimeGroups.FinitePQuotients

/-! Infinite residually finite p-groups of augmentation units, in every positive matrix rank.
These groups are not asserted to be finitely presented. The main Steinberg construction
provides finite presentation separately. -/

namespace AllPrimeGroups.PrimeAlgebra
noncomputable section

variable (p : ℕ) (hp : p.Prime)

abbrev CongruenceUnits := NilCongruence.Group (augmentation p hp)
abbrev MatrixCongruenceUnits (n : ℕ) := NilCongruence.MatrixGroup (augmentation p hp) n

theorem truncations_separate (a : R p hp)
    (ha : ∀ d, (Phases.primeTruncIdeal p hp d).ringCon.mk' a = 0) : a = 0 := by
  apply Phases.Hierarchy.eq_zero_of_forall_mem OAI.SourceBurnside.ConcreteSource.machine
    (threshold_le_height p hp) p
  intro d
  have h := ha d
  rw [← map_zero (Phases.primeTruncIdeal p hp d).ringCon.mk'] at h
  simpa only [sub_zero] using
    ((Phases.primeTruncIdeal p hp d).rel_iff a 0).mp
      ((Phases.primeTruncIdeal p hp d).ringCon.eq.mp h)

theorem units_residuallyFinite : Group.ResiduallyFinite (R p hp)ˣ := by
  have : Fact p.Prime := ⟨hp⟩
  have : ∀ d, Finite (Phases.primeTruncIdeal p hp d).ringCon.Quotient :=
    Phases.Hierarchy.finite_trunc OAI.SourceBurnside.ConcreteSource.machine
      (threshold_le_height p hp) p
  exact NilCongruence.units_residuallyFinite
    (fun d => (Phases.primeTruncIdeal p hp d).ringCon.mk') (truncations_separate p hp)

theorem congruenceUnits_infinite : Infinite (CongruenceUnits p hp) := by
  have := infinite p hp
  have : NeZero p := ⟨hp.ne_zero⟩
  exact NilCongruence.infinite (augmentation p hp) (augmentation_kernel_nil p hp)

theorem congruenceUnits_residuallyFinite : Group.ResiduallyFinite (CongruenceUnits p hp) := by
  have := units_residuallyFinite p hp
  infer_instance

theorem congruenceUnits_isPGroup : IsPGroup p (CongruenceUnits p hp) := by
  have := charP p hp
  exact units_congruence_isPGroup hp (augmentation p hp) (augmentation_kernel_nil p hp)

theorem congruenceUnits_properties :
    Infinite (CongruenceUnits p hp) ∧ Group.ResiduallyFinite (CongruenceUnits p hp) ∧
      IsPGroup p (CongruenceUnits p hp) :=
  ⟨congruenceUnits_infinite p hp, congruenceUnits_residuallyFinite p hp,
    congruenceUnits_isPGroup p hp⟩

theorem matrixUnits_residuallyFinite (n : ℕ) :
    Group.ResiduallyFinite (Matrix (Fin n) (Fin n) (R p hp))ˣ := by
  have : Fact p.Prime := ⟨hp⟩
  have : ∀ d, Finite (Phases.primeTruncIdeal p hp d).ringCon.Quotient :=
    Phases.Hierarchy.finite_trunc OAI.SourceBurnside.ConcreteSource.machine
      (threshold_le_height p hp) p
  exact NilCongruence.matrix_units_residuallyFinite n
    (fun d => (Phases.primeTruncIdeal p hp d).ringCon.mk') (truncations_separate p hp)

theorem matrixCongruenceUnits_infinite {n : ℕ} (hn : 0 < n) :
    Infinite (MatrixCongruenceUnits p hp n) := by
  have := infinite p hp
  have : NeZero p := ⟨hp.ne_zero⟩
  exact NilCongruence.matrix_infinite (augmentation p hp) n hn (matrix_nil p hp n)

theorem matrixCongruenceUnits_residuallyFinite (n : ℕ) :
    Group.ResiduallyFinite (MatrixCongruenceUnits p hp n) := by
  have := matrixUnits_residuallyFinite p hp n
  infer_instance

set_option backward.isDefEq.respectTransparency false in
theorem matrixCongruenceUnits_isPGroup (n : ℕ) :
    IsPGroup p (MatrixCongruenceUnits p hp n) := by
  have := charP p hp
  exact NilCongruence.matrix_isPGroup (augmentation p hp) n hp (matrix_nil p hp n)

theorem matrixCongruenceUnits_properties {n : ℕ} (hn : 0 < n) :
    Infinite (MatrixCongruenceUnits p hp n) ∧
      Group.ResiduallyFinite (MatrixCongruenceUnits p hp n) ∧
        IsPGroup p (MatrixCongruenceUnits p hp n) :=
  ⟨matrixCongruenceUnits_infinite p hp hn, matrixCongruenceUnits_residuallyFinite p hp n,
    matrixCongruenceUnits_isPGroup p hp n⟩

theorem matrixCongruenceUnits_finite_quotients_unbounded {n : ℕ} (hn : 0 < n) (B : ℕ) :
    ∃ (H : Type) (_ : Group H) (_ : Finite H) (f : MatrixCongruenceUnits p hp n →* H),
      Function.Surjective f ∧ IsPGroup p H ∧
        ∃ k : ℕ, Nat.card H = p ^ k ∧ B ≤ Nat.card H := by
  have := matrixCongruenceUnits_infinite p hp hn
  have := matrixCongruenceUnits_residuallyFinite p hp n
  exact FinitePQuotients.unbounded_quotients hp (matrixCongruenceUnits_isPGroup p hp n) B

end
end AllPrimeGroups.PrimeAlgebra
