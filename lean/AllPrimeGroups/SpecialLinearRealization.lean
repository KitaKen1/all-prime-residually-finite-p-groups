import AllPrimeGroups.SpecialLinearLift

/-! Over a field, the elementary image of the Steinberg group contains every matrix of
determinant one. -/

namespace AllPrimeGroups.Elementary
open Matrix
open scoped BigOperators

variable {N : ℕ} {K : Type*} [Field K]

theorem torus_eq_diagonal (i j : Fin N) (hij : i ≠ j) (c d : K) :
    1 + Matrix.single i i (c - 1) + Matrix.single j j (d - 1) =
      Matrix.diagonal (Function.update (Function.update (1 : Fin N → K) i c) j d) := by
  ext a b
  simp only [Matrix.add_apply, Matrix.single_apply, Matrix.one_apply, Matrix.diagonal_apply,
    Function.update_apply, Pi.one_apply]
  by_cases hab : a = b
  · subst hab
    by_cases hai : i = a
    · subst hai
      have hji : ¬ j = i := fun h => hij h.symm
      simp [hij, hji]
    · by_cases haj : j = a
      · subst haj
        simp [hai]
      · have hai' : ¬ a = i := fun h => hai h.symm
        have haj' : ¬ a = j := fun h => haj h.symm
        simp [hai, haj, hai', haj']
  · have h1 : ¬ (i = a ∧ i = b) := fun h => hab (h.1.symm.trans h.2)
    have h2 : ¬ (j = a ∧ j = b) := fun h => hab (h.1.symm.trans h.2)
    simp [hab, h1, h2]

theorem realized_diagonal_aux (S : Finset (Fin N)) :
    ∀ D : Fin N → K, (∀ k, k ∉ S → D k = 1) → ∏ k ∈ S, D k = 1 →
      Realized (Matrix.diagonal D) := by
  induction S using Finset.induction_on with
  | empty =>
    intro D hD _
    have h1 : D = 1 := funext fun k => hD k (Finset.notMem_empty k)
    rw [h1, show Matrix.diagonal (1 : Fin N → K) = 1 from Matrix.diagonal_one]
    exact realized_one
  | insert a S ha ih =>
    intro D hD hprod
    rw [Finset.prod_insert ha] at hprod
    rcases S.eq_empty_or_nonempty with rfl | ⟨b, hb⟩
    · rw [Finset.prod_empty, mul_one] at hprod
      have h1 : D = 1 := funext fun k => by
        by_cases hk : k = a
        · rw [hk]
          exact hprod
        · exact hD k (by simpa using hk)
      rw [h1, show Matrix.diagonal (1 : Fin N → K) = 1 from Matrix.diagonal_one]
      exact realized_one
    · have hab : a ≠ b := fun h => ha (h ▸ hb)
      have hDa : D a ≠ 0 := left_ne_zero_of_mul_eq_one hprod
      let D' : Fin N → K := Function.update (Function.update D a 1) b (D a * D b)
      have hD' : ∀ k, k ∉ S → D' k = 1 := by
        intro k hk
        have hkb : k ≠ b := fun h => hk (h ▸ hb)
        by_cases hka : k = a
        · simp [D', hka, hab]
        · have hk1 := hD k (by simp [hka, hk])
          simp [D', hkb, hka, hk1]
      have hprod' : ∏ k ∈ S, D' k = 1 := by
        rw [Finset.prod_update_of_mem hb, Finset.prod_update_of_notMem (by simp [ha]),
          Finset.sdiff_singleton_eq_erase, mul_assoc, Finset.mul_prod_erase S D hb]
        exact hprod
      have hmul : Matrix.diagonal D =
          Matrix.diagonal (Function.update (Function.update (1 : Fin N → K) a (D a)) b (D a)⁻¹) *
            Matrix.diagonal D' := by
        rw [Matrix.diagonal_mul_diagonal]
        congr 1
        funext k
        by_cases hka : k = a
        · simp [D', hka, hab]
        · by_cases hkb : k = b
          · simp [D', hkb, hDa]
          · simp [D', hka, hkb]
      rw [hmul, ← torus_eq_diagonal a b hab]
      exact (realized_torus a b hab (D a) (D a)⁻¹ (mul_inv_cancel₀ hDa)).mul (ih D' hD' hprod')

theorem realized_diagonal (D : Fin N → K) (hD : ∏ k, D k = 1) : Realized (Matrix.diagonal D) :=
  realized_diagonal_aux Finset.univ D (fun k hk => absurd (Finset.mem_univ k) hk) hD

/-- Over a field, every matrix of determinant one is elementary. -/
theorem realized_of_det_eq_one (M : Matrix (Fin N) (Fin N) K) (hM : M.det = 1) : Realized M := by
  obtain ⟨L, L', D, h⟩ := Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec M
  have hD : ∏ k, D k = 1 := by
    have hdet := congrArg Matrix.det h
    rw [Matrix.det_mul, Matrix.det_mul, TransvectionStruct.det_toMatrix_prod,
      TransvectionStruct.det_toMatrix_prod, one_mul, mul_one, Matrix.det_diagonal, hM] at hdet
    exact hdet.symm
  rw [h]
  exact ((realized_transvections L).mul (realized_diagonal D hD)).mul (realized_transvections L')

theorem exists_representation_eq (P : (Matrix (Fin N) (Fin N) K)ˣ) (hP : P.val.det = 1) :
    ∃ g : Steinberg N K, representation g = P := by
  obtain ⟨g, hg⟩ := realized_of_det_eq_one P.val hP
  exact ⟨g, Units.ext hg⟩

end AllPrimeGroups.Elementary
