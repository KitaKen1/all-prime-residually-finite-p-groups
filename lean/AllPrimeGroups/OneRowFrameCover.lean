import AllPrimeGroups.FrameCharacterClasses

/-! The original one-row cover maps into the one-fixed-column block cover, compatibly
with the actual matrix projection and the smaller Steinberg matrix kernel. -/

namespace AllPrimeGroups
namespace Frames
noncomputable section
open Matrix GLPres FrameStabilizer FrameBlocks FrameFaces

variable {B : Type} [Ring B] {m : ℕ}

theorem rowInclusion_one_left (x : Cover m B) (i : Fin 1) :
    (rowInclusion (0 : Fin 1) x).left i = x.left := by
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  simp [rowInclusion]

theorem rowInclusion_one_matrix (x : Cover m B) :
    sumRelabel (coverMatrix (rowInclusion (0 : Fin 1) x)) = toMatrix x := by
  have hinl (a : Fin m) :
      finSumFinEquiv (Sum.inl a : Fin m ⊕ Fin 1) = a.castSucc := rfl
  have hinr (i : Fin 1) :
      finSumFinEquiv (Sum.inr i : Fin m ⊕ Fin 1) = Fin.last m := by
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    rfl
  apply Units.ext
  ext a b
  obtain ⟨a, rfl⟩ := (finSumFinEquiv : Fin m ⊕ Fin 1 ≃ Fin (m + 1)).surjective a
  obtain ⟨b, rfl⟩ := (finSumFinEquiv : Fin m ⊕ Fin 1 ≃ Fin (m + 1)).surjective b
  change (coverMatrix (rowInclusion (0 : Fin 1) x)).val
    (finSumFinEquiv.symm (finSumFinEquiv a)) (finSumFinEquiv.symm (finSumFinEquiv b)) =
    (toMatrix x).val (finSumFinEquiv a) (finSumFinEquiv b)
  simp only [Equiv.symm_apply_apply]
  rw [coverMatrix_val]
  change (Matrix.fromBlocks (Elementary.representation x.right).val 0
    (rowsMatrix (rowInclusion (0 : Fin 1) x).left * (Elementary.representation x.right).val) 1) a b = _
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      rw [Matrix.fromBlocks_apply₁₁, hinl, hinl, toMatrix_castSucc_entry]
      simp only [LocalGL.pad_apply, LocalGL.coordinateEquiv_symm_castSucc,
        Matrix.fromBlocks_apply₁₁]
    | inr b =>
      rw [Matrix.fromBlocks_apply₁₂, hinl, hinr, toMatrix_last_column_entry]
      simp
  | inr a =>
    cases b with
    | inl b =>
      rw [Matrix.fromBlocks_apply₂₁, hinr, hinl, toMatrix_last_castSucc_entry]
      simp only [Matrix.mul_apply, rowsMatrix, rowInclusion_one_left, Matrix.vecMul, dotProduct]
    | inr b =>
      rw [Matrix.fromBlocks_apply₂₂, hinr, hinr, toMatrix_last_column_entry]
      simp [Matrix.one_apply, Subsingleton.elim a b]

variable {K : Type} [Field K] (ε : B →+* K) (hunit : ∀ b : B, ε b ≠ 0 → IsUnit b)

theorem rowInclusion_standard_projection (hm : 5 ≤ m) (x : Cover m B) :
    ((standardFrameExtension ε hunit (l := 1) hm).rightHom (rowInclusion (0 : Fin 1) x)).val.val =
      toMatrix x := by
  change sumRelabel (coverMatrix (rowInclusion (0 : Fin 1) x)) = toMatrix x
  exact rowInclusion_one_matrix x

theorem rowInclusion_kernel (z : (Elementary.representation (n := m) (R := B)).ker) :
    rowInclusion (0 : Fin 1) (kernelInclusion z) = blockKernelInclusion z :=
  rowInclusion_inr (0 : Fin 1) z.val

/-- Restrict a character of the cover centre to its smaller matrix kernel. -/
def kernelCenterInclusion (hm : 6 ≤ m) :
    (Elementary.representation (n := m) (R := B)).ker →* Subgroup.center (Cover m B) :=
  kernelInclusion.codRestrict _ (fun z => kernel_central ε hunit hm
    ((toMatrix_eq_one_iff _).mpr ⟨rfl, z.property⟩))

end
end Frames
end AllPrimeGroups
