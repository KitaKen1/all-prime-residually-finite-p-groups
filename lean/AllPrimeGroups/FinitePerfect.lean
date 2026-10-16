import AllPrimeGroups.RootCalculus
import Mathlib.GroupTheory.Schreier
import Mathlib.GroupTheory.IsPerfect

namespace AllPrimeGroups

/-- Schur's theorem shortens manuscript Section 13. Finite generation is unnecessary. -/
theorem finite_of_perfect_finite_center_quotient (G : Type*) [Group G]
    [Group.IsPerfect G] [Finite (G ⧸ Subgroup.center G)] : Finite G := by
  classical
  let F : (G ⧸ Subgroup.center G) × (G ⧸ Subgroup.center G) → G :=
    fun q => bracket q.1.out q.2.out
  have hc (z : Subgroup.center G) (g : G) : Commute g (z : G) :=
    Subgroup.mem_center_iff.mp z.property g
  have hs : commutatorSet G ⊆ Set.range F := by
    intro g hg
    obtain ⟨x, y, rfl⟩ := mem_commutatorSet_iff.mp hg
    obtain ⟨z, hz⟩ := QuotientGroup.mk_out_eq_mul (s := Subgroup.center G) x
    obtain ⟨w, hw⟩ := QuotientGroup.mk_out_eq_mul (s := Subgroup.center G) y
    refine ⟨(QuotientGroup.mk x, QuotientGroup.mk y), ?_⟩
    change bracket (QuotientGroup.mk x : G ⧸ Subgroup.center G).out
      (QuotientGroup.mk y : G ⧸ Subgroup.center G).out = bracket x y
    rw [hz, hw, CommutatorCalculus.separated x y z w (hc z x) (hc w x) (hc z y) (hc w y),
      (bracket_eq_one_iff _ _).mpr (hc w z), mul_one]
  have : Finite (commutatorSet G) := ((Set.finite_range F).subset hs).to_subtype
  have : Finite (commutator G) := inferInstance
  exact Finite.of_surjective (commutator G).subtype
    (fun g => ⟨⟨g, Group.IsPerfect.mem_commutator⟩, rfl⟩)

end AllPrimeGroups
