import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.ResiduallyFinite

/-! Finite p-group quotients of residually finite p-groups.
Use the finite quotient supplied by residual finiteness. Surjectivity transfers p-group
structure, and Mathlib identifies its cardinality as a power of p. For simultaneous
separation, restrict a finite product map to its image rather than proving a separate
p-group theorem for the entire product.
-/

namespace AllPrimeGroups.FinitePQuotients
noncomputable section

universe u v
variable {p : ℕ} {G : Type u} [Group G]

theorem range_isPGroup (hG : IsPGroup p G) {H : Type v} [Group H] (f : G →* H) :
    IsPGroup p f.range :=
  hG.of_surjective f.rangeRestrict f.rangeRestrict_surjective

/-- Manuscript Lemma 5.3: every finite homomorphic image has prime-power cardinality. -/
theorem finite_image_card (hp : p.Prime) (hG : IsPGroup p G)
    {H : Type v} [Group H] (f : G →* H) [Finite f.range] :
    ∃ k : ℕ, Nat.card f.range = p ^ k := by
  have : Fact p.Prime := ⟨hp⟩
  exact (range_isPGroup hG f).exists_card_eq

theorem finite_quotient_card (hp : p.Prime) (hG : IsPGroup p G)
    (N : FiniteIndexNormalSubgroup G) : ∃ k : ℕ, Nat.card (G ⧸ N.toSubgroup) = p ^ k := by
  have : Fact p.Prime := ⟨hp⟩
  exact (hG.to_quotient N.toSubgroup).exists_card_eq

/-- Distinct elements are separated by a surjection to a finite p-group. -/
theorem separate_pair [Group.ResiduallyFinite G] (hp : p.Prime) (hG : IsPGroup p G)
    {x y : G} (hxy : x ≠ y) :
    ∃ (H : Type u) (_ : Group H) (_ : Finite H) (f : G →* H),
      Function.Surjective f ∧ IsPGroup p H ∧
        (∃ k : ℕ, Nat.card H = p ^ k) ∧ f x ≠ f y := by
  obtain ⟨N, hN⟩ := Group.exists_finiteIndexNormalSubgroup_of_residuallyFinite x y hxy
  exact ⟨G ⧸ N.toSubgroup, inferInstance, inferInstance, QuotientGroup.mk' N.toSubgroup,
    Quotient.mk''_surjective, hG.to_quotient N.toSubgroup, finite_quotient_card hp hG N, hN⟩

/-- Manuscript Corollary 4.1, retaining surjectivity and the exact p-power order. -/
theorem separate_one [Group.ResiduallyFinite G] (hp : p.Prime) (hG : IsPGroup p G)
    {g : G} (hg : g ≠ 1) :
    ∃ (H : Type u) (_ : Group H) (_ : Finite H) (f : G →* H),
      Function.Surjective f ∧ IsPGroup p H ∧
        (∃ k : ℕ, Nat.card H = p ^ k) ∧ f g ≠ 1 := by
  obtain ⟨H, hH, hfin, f, hf, hpH, hcard, hsep⟩ := separate_pair hp hG hg
  exact ⟨H, hH, hfin, f, hf, hpH, hcard, by simpa only [map_one] using hsep⟩

/-- One finite p-group quotient is injective on any prescribed finite subset. -/
theorem separate_finset [Group.ResiduallyFinite G] (hp : p.Prime) (hG : IsPGroup p G)
    (s : Finset G) :
    ∃ (H : Type u) (_ : Group H) (_ : Finite H) (f : G →* H),
      Function.Surjective f ∧ IsPGroup p H ∧
        (∃ k : ℕ, Nat.card H = p ^ k) ∧ Set.InjOn f (s : Set G) := by
  classical
  let I := {q : s × s // q.1 ≠ q.2}
  have hsep (i : I) : ∃ N : FiniteIndexNormalSubgroup G,
      ((i.val.1 : G) : G ⧸ N.toSubgroup) ≠ (i.val.2 : G) :=
    Group.exists_finiteIndexNormalSubgroup_of_residuallyFinite _ _
      (fun h => i.property (Subtype.ext h))
  choose N hN using hsep
  let f : G →* ∀ i : I, G ⧸ (N i).toSubgroup :=
    MonoidHom.pi (fun i => QuotientGroup.mk' (N i).toSubgroup)
  have hinj : Set.InjOn f (s : Set G) := by
    intro x hx y hy hxy
    by_contra hne
    let i : I := ⟨(⟨x, hx⟩, ⟨y, hy⟩), fun h => hne (congrArg Subtype.val h)⟩
    exact hN i (congrFun hxy i)
  refine ⟨f.range, inferInstance, inferInstance, f.rangeRestrict,
    f.rangeRestrict_surjective, range_isPGroup hG f, finite_image_card hp hG f, ?_⟩
  intro x hx y hy hxy
  exact hinj hx hy (congrArg Subtype.val hxy)

/-- An infinite residually finite p-group has finite p-group quotients of unbounded order. -/
theorem unbounded_quotients [Group.ResiduallyFinite G] [Infinite G]
    (hp : p.Prime) (hG : IsPGroup p G) (B : ℕ) :
    ∃ (H : Type u) (_ : Group H) (_ : Finite H) (f : G →* H),
      Function.Surjective f ∧ IsPGroup p H ∧
        ∃ k : ℕ, Nat.card H = p ^ k ∧ B ≤ Nat.card H := by
  obtain ⟨s, hs⟩ := Finset.exists_card_eq (α := G) B
  obtain ⟨H, hH, hfin, f, hf, hpH, ⟨k, hk⟩, hinj⟩ := separate_finset hp hG s
  refine ⟨H, hH, hfin, f, hf, hpH, k, hk, ?_⟩
  have hle := Nat.card_le_card_of_injective (fun x : s => f x.val)
    (fun x y h => Subtype.ext (hinj x.property y.property h))
  simpa only [Nat.card_eq_fintype_card, Fintype.card_coe, hs] using hle

/-- The canonical map to the product of all finite normal quotients. -/
def quotientProductMap : G →* ∀ N : FiniteIndexNormalSubgroup G, G ⧸ N.toSubgroup :=
  MonoidHom.pi (fun N => QuotientGroup.mk' N.toSubgroup)

theorem quotientProductMap_injective [Group.ResiduallyFinite G] :
    Function.Injective (quotientProductMap (G := G)) := by
  intro x y hxy
  by_contra hne
  obtain ⟨N, hN⟩ := Group.exists_finiteIndexNormalSubgroup_of_residuallyFinite x y hne
  exact hN (congrFun hxy N)

end
end AllPrimeGroups.FinitePQuotients
