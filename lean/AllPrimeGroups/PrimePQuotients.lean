import AllPrimeGroups.FinitePQuotients
import AllPrimeGroups.PrimeGroups

/-! Finite p-group quotients and simultaneous separation for the concrete groups. -/

namespace AllPrimeGroups.PrimeGroups
noncomputable section

variable (p : ℕ) (hp : p.Prime) {n : ℕ}

theorem finite_quotient_card (hn : 7 ≤ n) (N : FiniteIndexNormalSubgroup (G p hp n)) :
    ∃ k : ℕ, Nat.card (G p hp n ⧸ N.toSubgroup) = p ^ k :=
  FinitePQuotients.finite_quotient_card hp (isPGroup p hp hn) N

theorem finite_p_quotient_separates (hn : 7 ≤ n) {x y : G p hp n} (hxy : x ≠ y) :
    ∃ (H : Type) (_ : Group H) (_ : Finite H) (f : G p hp n →* H),
      Function.Surjective f ∧ IsPGroup p H ∧
        (∃ k : ℕ, Nat.card H = p ^ k) ∧ f x ≠ f y := by
  have := residuallyFinite p hp hn
  exact FinitePQuotients.separate_pair hp (isPGroup p hp hn) hxy

theorem finite_p_quotient_injective_on (hn : 7 ≤ n) (s : Finset (G p hp n)) :
    ∃ (H : Type) (_ : Group H) (_ : Finite H) (f : G p hp n →* H),
      Function.Surjective f ∧ IsPGroup p H ∧
        (∃ k : ℕ, Nat.card H = p ^ k) ∧ Set.InjOn f (s : Set (G p hp n)) := by
  have := residuallyFinite p hp hn
  exact FinitePQuotients.separate_finset hp (isPGroup p hp hn) s

theorem finite_p_quotients_unbounded (hn : 7 ≤ n) (B : ℕ) :
    ∃ (H : Type) (_ : Group H) (_ : Finite H) (f : G p hp n →* H),
      Function.Surjective f ∧ IsPGroup p H ∧
        ∃ k : ℕ, Nat.card H = p ^ k ∧ B ≤ Nat.card H := by
  have := residuallyFinite p hp hn
  have := infinite p hp (show 6 ≤ n by omega)
  exact FinitePQuotients.unbounded_quotients hp (isPGroup p hp hn) B

theorem finite_quotient_embedding_injective (hn : 7 ≤ n) :
    Function.Injective (FinitePQuotients.quotientProductMap (G := G p hp n)) := by
  have := residuallyFinite p hp hn
  exact FinitePQuotients.quotientProductMap_injective

end
end AllPrimeGroups.PrimeGroups
