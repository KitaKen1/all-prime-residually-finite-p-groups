import AllPrimeGroups.StableGroup
import AllPrimeGroups.FinitePerfect

/-! Finite quotients from stable stage images.
Finiteness of an entire unstable Steinberg group is not needed for these detectors. -/

namespace AllPrimeGroups.Stable
noncomputable section

variable (R : Type*) [Ring R]

abbrev StageImage (n : ℕ) := (of R n).range

def stageRepresentation (n : ℕ) : StageImage R n →* StableMatrixUnits R :=
  (representation R).domRestrict (StageImage R n)

theorem stageRepresentation_range_le (n : ℕ) :
    (stageRepresentation R n).range ≤ (matrixOf R n).range := by
  rintro x ⟨g, rfl⟩
  obtain ⟨z, hz⟩ := g.property
  refine ⟨Elementary.representation z, ?_⟩
  change matrixOf R n (Elementary.representation z) = representation R g.val
  rw [← hz, representation_of]

theorem stageRepresentation_kernel_le_center (n : ℕ) :
    (stageRepresentation R n).ker ≤ Subgroup.center (StageImage R n) := by
  intro g hg
  have hmat : representation R g.val = 1 := hg
  have hc := kernel_central R g.val hmat
  apply Subgroup.mem_center_iff.mpr
  intro h
  apply Subtype.ext
  exact Subgroup.mem_center_iff.mp hc h.val

/-- Over a finite ring, every stage image of rank at least three is finite.
The source Steinberg group need not be known finite or known to stabilize injectively. -/
theorem stageImage_finite [Finite R] (n : ℕ) (hn : 3 ≤ n) : Finite (StageImage R n) := by
  let : Group.IsPerfect (Steinberg n R) := Steinberg.isPerfect hn
  let : Group.IsPerfect (StageImage R n) := Group.IsPerfect.range (of R n)
  have hmatrix : Finite (matrixOf R n).range :=
    Finite.of_surjective (matrixOf R n).rangeRestrict (matrixOf R n).rangeRestrict_surjective
  let : Finite (stageRepresentation R n).range :=
    Finite.of_injective (Subgroup.inclusion (stageRepresentation_range_le R n))
      (Subgroup.inclusion_injective _)
  let : (stageRepresentation R n).ker.FiniteIndex := inferInstance
  let : (Subgroup.center (StageImage R n)).FiniteIndex :=
    Subgroup.finiteIndex_of_le (stageRepresentation_kernel_le_center R n)
  exact finite_of_perfect_finite_center_quotient (StageImage R n)

variable {R} {S : Type*} [Ring S]

/-- A concrete group homomorphism to the finite stable stage image of a coefficient quotient. -/
def detector (n : ℕ) (ε : R →+* S) : Steinberg n R →* StageImage S n :=
  (of S n).rangeRestrict.comp (Steinberg.map ε)

@[simp] theorem detector_coe (n : ℕ) (ε : R →+* S) (g : Steinberg n R) :
    (detector n ε g).val = of S n (Steinberg.map ε g) := rfl

theorem detector_kernel_finiteIndex [Finite S] (n : ℕ) (hn : 3 ≤ n) (ε : R →+* S) :
    (detector n ε).ker.FiniteIndex := by
  let : Finite (StageImage S n) := stageImage_finite S n hn
  infer_instance

end
end AllPrimeGroups.Stable
