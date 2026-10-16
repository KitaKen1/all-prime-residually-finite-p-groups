import AllPrimeGroups.PrimeCharacterExtensions
import AllPrimeGroups.FiniteLocal

/-! The concrete groups supplied by the all-prime construction, in every rank at least seven.

`G p hp n` is the kernel of reduction into the finite-rank Steinberg group over `ZMod p`,
as specified in manuscript Theorem 1.1. It embeds into the candidate used by the existence
proof. The argument does not require identifying these two kernels.
-/

namespace AllPrimeGroups.PrimeGroups
noncomputable section

variable (p : ℕ) (hp : p.Prime)

/-- The fixed-rank reduction kernel specified in manuscript Theorem 1.1. -/
abbrev subgroup (n : ℕ) : Subgroup (Steinberg n (PrimeAlgebra.R p hp)) :=
  (Steinberg.map (PrimeAlgebra.augmentation p hp)).ker

abbrev G (n : ℕ) : Type := subgroup p hp n

theorem le_candidate (n : ℕ) :
    subgroup p hp n ≤ CandidateSubgroup n (PrimeAlgebra.augmentation p hp) := by
  intro g hg
  apply Subtype.ext
  change Stable.of (ZMod p) n (Steinberg.map (PrimeAlgebra.augmentation p hp) g) = 1
  rw [MonoidHom.mem_ker.mp hg, map_one]

theorem finiteIndex {n : ℕ} (hn : 6 ≤ n) : (subgroup p hp n).FiniteIndex := by
  have : Fact p.Prime := ⟨hp⟩
  have := Steinberg.finite_of_finite_field (K := ZMod p) hn
  infer_instance

theorem infinite {n : ℕ} (hn : 6 ≤ n) : Infinite (G p hp n) := by
  have : Fact p.Prime := ⟨hp⟩
  have := PrimeAlgebra.infinite p hp
  let root : Root n := ⟨⟨0, by omega⟩, ⟨1, by omega⟩,
    fun h => (by decide : (0 : ℕ) ≠ 1) (congrArg Fin.val h)⟩
  have : Infinite (Steinberg n (PrimeAlgebra.R p hp)) := Elementary.steinberg_infinite root
  by_contra h
  have hfin : Finite (G p hp n) := not_infinite_iff_finite.mp h
  have hwhole : Finite (Steinberg n (PrimeAlgebra.R p hp)) :=
    (Subgroup.finite_iff_finite_and_finiteIndex (subgroup p hp n)).mpr
      ⟨hfin, finiteIndex p hp hn⟩
  exact not_finite (Steinberg n (PrimeAlgebra.R p hp))

theorem finitelyPresented {n : ℕ} (hn : 6 ≤ n) : Group.IsFinitelyPresented (G p hp n) := by
  have : Fact p.Prime := ⟨hp⟩
  have := PrimeAlgebra.steinberg_finitelyPresented p hp (show 5 ≤ n by omega)
  have := finiteIndex p hp hn
  exact isFinitelyPresented_of_finiteIndex (subgroup p hp n)

set_option backward.isDefEq.respectTransparency false in
theorem candidate_residuallyFinite {n : ℕ} (hn : 7 ≤ n) :
    Group.ResiduallyFinite (CandidateSubgroup n (PrimeAlgebra.augmentation p hp)) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨ι, Q, hring, hfin, q, hsep⟩ := Phases.separation_obligation p hp
  exact @Candidate.residuallyFinite (PrimeAlgebra.R p hp) (ZMod p) inferInstance inferInstance
    n (PrimeAlgebra.augmentation p hp) (by omega)
    (PrimeAlgebra.stabilization_injective p hp n hn) ι Q hring hfin q hsep

private theorem residuallyFinite_of_injective {A B : Type*} [Group A] [Group B]
    [Group.ResiduallyFinite B] (f : A →* B) (hf : Function.Injective f) :
    Group.ResiduallyFinite A := by
  apply Group.residuallyFinite_iff_forall_finiteIndexNormalSubgroup.mpr
  intro g hg
  apply hf
  rw [map_one]
  exact Group.eq_one_iff_forall_finiteIndexNormalSubroup _
    (fun H => hg (H.comap f))

theorem residuallyFinite {n : ℕ} (hn : 7 ≤ n) : Group.ResiduallyFinite (G p hp n) := by
  have := candidate_residuallyFinite p hp hn
  exact residuallyFinite_of_injective (Subgroup.inclusion (le_candidate p hp n))
    (Subgroup.inclusion_injective _)

theorem isPGroup {n : ℕ} (hn : 7 ≤ n) : IsPGroup p (G p hp n) := by
  have : Fact p.Prime := ⟨hp⟩
  have := PrimeAlgebra.charP p hp
  have hcandidate := Candidate.isPGroup n (PrimeAlgebra.augmentation p hp) hp (by omega)
    (PrimeAlgebra.matrix_nil p hp n) (PrimeAlgebra.stabilization_injective p hp n hn)
    (PrimeAlgebra.relative_torsion p hp)
  exact hcandidate.of_injective (Subgroup.inclusion (le_candidate p hp n))
    (Subgroup.inclusion_injective _)

/-- All four properties hold for this same explicit group in every rank at least seven. -/
theorem properties {n : ℕ} (hn : 7 ≤ n) :
    Infinite (G p hp n) ∧ Group.IsFinitelyPresented (G p hp n) ∧
      Group.ResiduallyFinite (G p hp n) ∧ IsPGroup p (G p hp n) :=
  ⟨infinite p hp (by omega), finitelyPresented p hp (by omega),
    residuallyFinite p hp hn, isPGroup p hp hn⟩

end
end AllPrimeGroups.PrimeGroups
