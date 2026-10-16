/-
It imports the upstream modules through Steinberg/CoefficientQuotients, which must be built
first (`python3 scripts/build_upstream.py`).

The coefficient algebra R(p) for a prime p (manuscript Theorem 18.1): the word algebra of the
upstream machine hierarchy over `ZMod p`, at an initial height chosen above the machine
threshold so that every block length of the hierarchy is prime to p. This file collects the
coefficient obligations that are already available for it: it is infinite, of characteristic
p, its augmentation kernel is matrix-nil, and its Steinberg groups of rank at least five are
finitely presented, and its stable matrix kernel has relative p-power torsion. Finite-rank
injectivity and stable separation are not proved here.
-/
import OAI.GroupTheory.PeriodicGroups.Steinberg.CoefficientQuotients
import AllPrimeGroups.PrimeMatrixNil
import AllPrimeGroups.PrimePeriods
import AllPrimeGroups.SteinbergPresentation
import AllPrimeGroups.RelativeTorsion

namespace AllPrimeGroups.PrimeAlgebra
open OAI OAI.SourceBurnside
noncomputable section

theorem dilation_odd : Odd ConcreteSource.dilation := by
  rw [Nat.odd_iff]
  decide

/-- The initial height for the prime p: above the machine threshold, with every block length
of the hierarchy prime to p. -/
def height (p : ℕ) (hp : p.Prime) : ℕ :=
  (exists_prime_free_hierarchy p hp ConcreteSource.dilation dilation_odd
    ConcreteSource.machine.threshold).choose

theorem threshold_le_height (p : ℕ) (hp : p.Prime) :
    ConcreteSource.machine.threshold ≤ height p hp :=
  (exists_prime_free_hierarchy p hp ConcreteSource.dilation dilation_odd
    ConcreteSource.machine.threshold).choose_spec.1.le

theorem blockLength_coprime (p : ℕ) (hp : p.Prime) (j : ℕ) :
    (blockLength (height p hp * ConcreteSource.dilation ^ j)).Coprime p :=
  (exists_prime_free_hierarchy p hp ConcreteSource.dilation dilation_odd
    ConcreteSource.machine.threshold).choose_spec.2 j

/-- The coefficient algebra R(p). -/
abbrev R (p : ℕ) (hp : p.Prime) : Type :=
  ConcreteSource.machine.Algebra (ZMod p) (height p hp) (threshold_le_height p hp)

/-- Degree-zero reduction. -/
def augmentation (p : ℕ) (hp : p.Prime) : R p hp →+* ZMod p :=
  (ConcreteSource.machine.augmentation (threshold_le_height p hp) (ZMod p)).toRingHom

theorem infinite (p : ℕ) (hp : p.Prime) : Infinite (R p hp) := by
  have : Fact p.Prime := ⟨hp⟩
  exact ConcreteSource.machine.infinite_algebra (ZMod p) (height p hp) (threshold_le_height p hp)

theorem charP (p : ℕ) (hp : p.Prime) : CharP (R p hp) p := by
  have : Fact p.Prime := ⟨hp⟩
  have := infinite p hp
  exact charP_of_injective_algebraMap (algebraMap (ZMod p) (R p hp)).injective p

/-- Manuscript Theorem 18.1, matrix nilpotence of the positive ideal. -/
theorem matrix_nil (p : ℕ) (hp : p.Prime) (n : ℕ) (M : Matrix (Fin n) (Fin n) (R p hp))
    (hM : (augmentation p hp).mapMatrix M = 0) : IsNilpotent M :=
  PrimeMatrixNil.matrix_nil ConcreteSource.machine (threshold_le_height p hp) (ZMod p) hp.pos
    ConcreteSource.dilation_large n M hM

/-- Manuscript Theorem 10.1 for R(p). -/
theorem steinberg_finitelyPresented (p : ℕ) (hp : p.Prime) {n : ℕ} (hn : 5 ≤ n) :
    Group.IsFinitelyPresented (Steinberg n (R p hp)) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  exact AllPrimeGroups.steinberg_finitelyPresented hn
    (ConcreteSource.machine.table (height p hp) (threshold_le_height p hp)).relations
    (FiniteTable.Codec.finite_algebraTable_relations
      (ConcreteSource.machine.threshold_four.trans (threshold_le_height p hp)) _)

/-- The homogeneous substitution: a word of length r goes to the same word times t^r. -/
def grading (p : ℕ) (hp : p.Prime) : R p hp →+* Polynomial (R p hp) :=
  ((ConcreteSource.machine.table (height p hp) (threshold_le_height p hp)).gradingHom (K := ZMod p)
    (ConcreteSource.machine.table_homogeneous (threshold_le_height p hp))).toRingHom

theorem scalarEval_one (p : ℕ) (hp : p.Prime) [Fact p.Prime] :
    Kernel.scalarEval (R := R p hp) (1 : ZMod p) =
      ((ConcreteSource.machine.table (height p hp) (threshold_le_height p hp)).evalOne
        (K := ZMod p)).toRingHom := by
  apply Polynomial.ringHom_ext
  · intro a
    simp [Kernel.scalarEval, WordAlgebra.Table.evalOne]
  · simp [Kernel.scalarEval, WordAlgebra.Table.evalOne]

theorem scalarEval_zero (p : ℕ) (hp : p.Prime) [Fact p.Prime] :
    Kernel.scalarEval (R := R p hp) (0 : ZMod p) =
      ((ConcreteSource.machine.table (height p hp) (threshold_le_height p hp)).evalZero
        (K := ZMod p)).toRingHom := by
  apply Polynomial.ringHom_ext
  · intro a
    simp [Kernel.scalarEval, WordAlgebra.Table.evalZero]
  · simp [Kernel.scalarEval, WordAlgebra.Table.evalZero]

theorem grading_one (p : ℕ) (hp : p.Prime) [Fact p.Prime] :
    (Kernel.scalarEval (1 : ZMod p)).comp (grading p hp) = RingHom.id (R p hp) := by
  rw [scalarEval_one]
  exact congrArg AlgHom.toRingHom
    ((ConcreteSource.machine.table (height p hp) (threshold_le_height p hp)).evalOne_gradingHom
      (ConcreteSource.machine.table_homogeneous (threshold_le_height p hp)))

theorem grading_zero (p : ℕ) (hp : p.Prime) [Fact p.Prime] :
    (Kernel.scalarEval (0 : ZMod p)).comp (grading p hp) =
      (algebraMap (ZMod p) (R p hp)).comp (augmentation p hp) := by
  rw [scalarEval_zero]
  exact congrArg AlgHom.toRingHom
    ((ConcreteSource.machine.table (height p hp) (threshold_le_height p hp)).evalZero_gradingHom
      (ConcreteSource.machine.table_homogeneous (threshold_le_height p hp))
      (ConcreteSource.machine.table_zero_nonempty (threshold_le_height p hp)))

/-- Manuscript Theorem 14.1 for R(p). -/
theorem relative_torsion (p : ℕ) (hp : p.Prime) (z : StableSteinberg (R p hp))
    (hz : Stable.representation (R p hp) z = 1) (hε : Stable.map (augmentation p hp) z = 1) :
    ∃ a : ℕ, z ^ p ^ a = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  exact Stable.relative_torsion (augmentation p hp) (grading p hp) (grading_one p hp)
    (grading_zero p hp) z hz hε

end
end AllPrimeGroups.PrimeAlgebra
