/-
It imports the upstream modules through Steinberg/CoefficientQuotients, through
`PrimeAlgebra`.

The reduction of the existence theorem to the two statements about R(p) that remain open:
finite-rank injectivity at rank twelve (manuscript Theorem 12.1) and stable separation by
finite coefficient quotients (manuscript Theorem 22.2). `OpenObligations` is a proposition;
nothing in it is asserted to hold.
-/
import AllPrimeGroups.PrimeAlgebra
import AllPrimeGroups.Assembly

namespace AllPrimeGroups
noncomputable section

/-- The statements about R(p) that are not yet proved. -/
def OpenObligations (p : ℕ) (hp : p.Prime) : Prop :=
  Function.Injective (Stable.of (PrimeAlgebra.R p hp) 12) ∧
  ∃ (ι : Type) (Q : ι → Type) (_ : ∀ i, Ring (Q i)) (_ : ∀ i, Finite (Q i))
    (q : ∀ i, PrimeAlgebra.R p hp →+* Q i),
    ∀ z : StableSteinberg (PrimeAlgebra.R p hp), (∀ i, Stable.map (q i) z = 1) → z = 1

theorem coefficientObligations_of_open (p : ℕ) (hp : p.Prime) (h : OpenObligations p hp) :
    CoefficientObligations p := by
  obtain ⟨hinj, ι, Q, hring, hfin, q, hsep⟩ := h
  exact ⟨PrimeAlgebra.R p hp, inferInstance, PrimeAlgebra.charP p hp, PrimeAlgebra.infinite p hp,
    PrimeAlgebra.augmentation p hp, 12, by decide,
    PrimeAlgebra.steinberg_finitelyPresented p hp (by decide),
    PrimeAlgebra.matrix_nil p hp 12, hinj, PrimeAlgebra.relative_torsion p hp,
    ι, Q, hring, hfin, q, hsep⟩

/-- The existence theorem follows from the two open statements for every prime. -/
theorem target_of_open (h : ∀ p : ℕ, ∀ hp : p.Prime, OpenObligations p hp) : Target :=
  target_of_obligations fun p hp => coefficientObligations_of_open p hp (h p hp)

end
end AllPrimeGroups
