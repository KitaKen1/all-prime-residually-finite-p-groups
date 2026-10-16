import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

/-! Concrete cochain consequences of vanishing group cohomology. -/

namespace AllPrimeGroups
noncomputable section
open CategoryTheory groupCohomology

variable {k G : Type} [CommRing k] [Group G] (A : Rep k G)

set_option backward.isDefEq.respectTransparency false in
/-- A cohomology class is zero exactly when its cocycle representative is a boundary. -/
theorem cochain_boundary_iff (q : ℕ) (x : cocycles A (q + 1)) :
    π A (q + 1) x = 0 ↔ ∃ b : (inhomogeneousCochains A).X q,
      (inhomogeneousCochains A).d q (q + 1) b = iCocycles A (q + 1) x := by
  let S := ShortComplex.mk (toCocycles A q (q + 1)) (π A (q + 1))
    ((inhomogeneousCochains A).toCycles_comp_homologyπ q (q + 1))
  have hex : S.Exact := S.exact_of_g_is_cokernel
    ((inhomogeneousCochains A).homologyIsCokernel q (q + 1) (CochainComplex.prev_nat_succ q))
  constructor
  · intro hx
    obtain ⟨b, hb⟩ := (ShortComplex.moduleCat_exact_iff S).mp hex x hx
    refine ⟨b, ?_⟩
    have h := congrArg (fun t => t b) ((inhomogeneousCochains A).toCycles_i q (q + 1))
    change iCocycles A (q + 1) (toCocycles A q (q + 1) b) = _ at h
    rw [hb] at h
    exact h.symm
  · rintro ⟨b, hb⟩
    have he : toCocycles A q (q + 1) b = x := by
      apply (ModuleCat.mono_iff_injective (iCocycles A (q + 1))).mp inferInstance
      have h := congrArg (fun t => t b) ((inhomogeneousCochains A).toCycles_i q (q + 1))
      exact h.trans hb
    have hz := congrArg (fun t => t b)
      ((inhomogeneousCochains A).toCycles_comp_homologyπ q (q + 1))
    change π A (q + 1) (toCocycles A q (q + 1) b) = 0 at hz
    rwa [he] at hz

theorem cochain_class_eq_iff (q : ℕ) (x y : cocycles A (q + 1)) :
    π A (q + 1) x = π A (q + 1) y ↔ ∃ b : (inhomogeneousCochains A).X q,
      (inhomogeneousCochains A).d q (q + 1) b =
        iCocycles A (q + 1) x - iCocycles A (q + 1) y := by
  rw [← sub_eq_zero, ← map_sub, cochain_boundary_iff, map_sub]

set_option backward.isDefEq.respectTransparency false in
theorem cochain_map_cocycle {D : Rep k G} (φ : A ⟶ D) (q : ℕ) (x : cocycles A q) :
    iCocycles D q (cocyclesMap (MonoidHom.id G) φ q x) =
      (cochainsMap (MonoidHom.id G) φ).f q (iCocycles A q x) := by
  exact congrArg (fun t => t x) (_root_.HomologicalComplex.cyclesMap_i
    (cochainsMap (A := A) (B := D) (MonoidHom.id G) φ) q)

set_option backward.isDefEq.respectTransparency false in
/-- Vanishing cohomology supplies a primitive for every closed cochain. -/
theorem cochain_primitive_of_subsingleton (q : ℕ)
    [Subsingleton (groupCohomology A (q + 1))]
    (c : (inhomogeneousCochains A).X (q + 1))
    (hc : (inhomogeneousCochains A).d (q + 1) (q + 2) c = 0) :
    ∃ b : (inhomogeneousCochains A).X q,
      (inhomogeneousCochains A).d q (q + 1) b = c := by
  have hex : (inhomogeneousCochains A).ExactAt (q + 1) :=
    ((inhomogeneousCochains A).exactAt_iff_isZero_homology (q + 1)).mpr
      (ModuleCat.isZero_of_subsingleton (groupCohomology A (q + 1)))
  have hex' : ((inhomogeneousCochains A).sc' q (q + 1) (q + 2)).Exact :=
    ((inhomogeneousCochains A).exactAt_iff' q (q + 1) (q + 2) (CochainComplex.prev_nat_succ q)
      (by simp)).mp hex
  exact (ShortComplex.moduleCat_exact_iff _).mp hex' c hc

theorem cochainsIso₀_hom_apply (c : (inhomogeneousCochains A).X 0) (x : Fin 0 → G) :
    (cochainsIso₀ A).hom c = c x := by
  change c default = c x
  rw [Subsingleton.elim (default : Fin 0 → G) x]

/-- A vertically closed zero-cochain has an invariant value. -/
theorem cochain_zero_invariant (c : (inhomogeneousCochains A).X 0)
    (hc : (inhomogeneousCochains A).d 0 1 c = 0) (x : Fin 0 → G) :
    c x ∈ A.ρ.invariants := by
  rw [← cochainsIso₀_hom_apply A c x, ← d₀₁_ker_eq_invariants]
  change d₀₁ A ((cochainsIso₀ A).hom c) = 0
  have h := congrArg (fun t => t c) (comp_d₀₁_eq A)
  change d₀₁ A ((cochainsIso₀ A).hom c) =
    (cochainsIso₁ A).hom ((inhomogeneousCochains A).d 0 1 c) at h
  rw [hc, map_zero] at h
  exact h

end
end AllPrimeGroups
