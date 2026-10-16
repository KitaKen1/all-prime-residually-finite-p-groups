import AllPrimeGroups.ScaledFrameFaces

/-! The two faces of an ordered pair, normalized by an elementary signed swap.

The first face is the inclusion in common coordinates. The second is corrected by -1 on
the forgotten row. Its matrix is conjugation of the first by a product of three elementary
matrices, and both lifted faces still coincide on the old Steinberg factor and its kernel. -/

namespace AllPrimeGroups
namespace FrameFaces
noncomputable section
open Matrix FrameStabilizer FrameBlocks GLPres LocalGL

variable {B : Type*} [Ring B] {n m : ℕ}

theorem swap_conjugates_matrix (a b : Fin n) (hab : a ≠ b)
    (A : (Matrix (Fin n) (Fin n) B)ˣ) :
    ev (swapWord a b hab) * A * (ev (swapWord a b hab))⁻¹ =
      MatrixGeometry.relabel (Equiv.swap a b) A := by
  apply units_ext_mulVec
  intro x
  rw [Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    swapWord_inv_mulVec, swapWord_mulVec]
  change (fun k => (A.val *ᵥ (fun j => x (Equiv.swap a b j))) (Equiv.swap a b k)) =
    A.val.submatrix (Equiv.swap a b).symm (Equiv.swap a b).symm *ᵥ x
  rw [Matrix.submatrix_mulVec_equiv]
  rfl

theorem signedSwap_eq_diagonal_swap (a b : Fin n) (hab : a ≠ b) :
    ev (K1.sgnWord (B := B) b a hab.symm) = d a (-1) * ev (swapWord a b hab) := by
  apply units_ext_mulVec
  intro x
  rw [Units.val_mul, ← Matrix.mulVec_mulVec, K1.sgnWord_mulVec, d_mulVec, swapWord_mulVec]
  funext k
  by_cases ha : k = a
  · subst ha
    simp [hab]
  · by_cases hb : k = b
    · subst hb
      simp [hab.symm]
    · simp [ha, hb, Equiv.swap_apply_of_ne_of_ne ha hb]

theorem signedSwap_mem_E (a b : Fin n) (hab : a ≠ b) :
    ev (K1.sgnWord (B := B) a b hab) ∈ K1.E n B := by
  simp only [K1.sgnWord, map_mul, ev_of, Gen.val]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (K1.e_mem_E _ _) (K1.e_mem_E _ _))
    (K1.e_mem_E _ _)

def pairFreeIndex (m : ℕ) : Fin ((m + 1) + 1) := finSumFinEquiv (.inl (Fin.last m))
def pairFixedIndex (m : ℕ) : Fin ((m + 1) + 1) := finSumFinEquiv (.inr (0 : Fin 1))

theorem pairIndices_ne : pairFreeIndex m ≠ pairFixedIndex m :=
  finSumFinEquiv.injective.ne Sum.inl_ne_inr

/-- The signed swap belongs to the common ambient elementary group. -/
def pairNormalizer (m : ℕ) (B : Type*) [Ring B] : K1.E ((m + 1) + 1) B :=
  ⟨ev (K1.sgnWord (pairFixedIndex m) (pairFreeIndex m) pairIndices_ne.symm),
    signedSwap_mem_E _ _ _⟩

theorem facePair_coordinates (a : Fin (m + 1) ⊕ Fin 1) :
    faceCoordinates (m := m) (1 : Fin 2) a =
      faceCoordinates (0 : Fin 2) (Equiv.swap (.inl (Fin.last m)) (.inr 0) a) := by
  cases a with
  | inl a =>
    induction a using Fin.lastCases with
    | last => simp [faceCoordinates]
    | cast a =>
      rw [Equiv.swap_apply_of_ne_of_ne]
      · simp only [faceCoordinates_castSucc]
      · exact Sum.inl_injective.ne (Fin.castSucc_lt_last a).ne
      · exact Sum.inl_ne_inr
  | inr a =>
    have ha : a = 0 := Subsingleton.elim _ _
    subst ha
    simp [faceCoordinates]

theorem facePair_finCoordinates (a : Fin ((m + 1) + 1)) :
    faceCoordinates (m := m) (1 : Fin 2) (finSumFinEquiv.symm a) =
      faceCoordinates (0 : Fin 2) (finSumFinEquiv.symm
        (Equiv.swap (pairFreeIndex m) (pairFixedIndex m) a)) := by
  obtain ⟨a, rfl⟩ := (finSumFinEquiv : Fin (m + 1) ⊕ Fin 1 ≃ Fin ((m + 1) + 1)).surjective a
  have h := Equiv.congr_fun (Equiv.trans_swap_trans_symm (pairFreeIndex m) (pairFixedIndex m)
    (finSumFinEquiv : Fin (m + 1) ⊕ Fin 1 ≃ Fin ((m + 1) + 1))) a
  simp only [Equiv.trans_apply, pairFreeIndex, pairFixedIndex, Equiv.symm_apply_apply] at h ⊢
  rw [h]
  exact facePair_coordinates a

theorem unsignedPair_matrix (x : BlockCover (Fin 2) m B) :
    sumRelabel (coverMatrix (faceCover (1 : Fin 2) x)) =
      ev (swapWord (pairFreeIndex m) (pairFixedIndex m) pairIndices_ne) *
        sumRelabel (coverMatrix (faceCover (0 : Fin 2) x)) *
          (ev (swapWord (pairFreeIndex m) (pairFixedIndex m) pairIndices_ne))⁻¹ := by
  rw [swap_conjugates_matrix, coverMatrix_face, coverMatrix_face]
  apply Units.ext
  ext a b
  change (coverMatrix x).val
      (faceCoordinates (1 : Fin 2) (finSumFinEquiv.symm a))
      (faceCoordinates (1 : Fin 2) (finSumFinEquiv.symm b)) =
    (coverMatrix x).val
      (faceCoordinates (0 : Fin 2) (finSumFinEquiv.symm
        (Equiv.swap (pairFreeIndex m) (pairFixedIndex m) a)))
      (faceCoordinates (0 : Fin 2) (finSumFinEquiv.symm
        (Equiv.swap (pairFreeIndex m) (pairFixedIndex m) b)))
  rw [facePair_finCoordinates, facePair_finCoordinates]

theorem firstFace_flatten (a : Fin (m + 1) ⊕ Fin 1) :
    (finSumFinEquiv : Fin m ⊕ Fin 2 ≃ Fin (m + 2)) (faceCoordinates (0 : Fin 2) a) =
      finSumFinEquiv a := by
  apply Fin.ext
  cases a with
  | inl a =>
    induction a using Fin.lastCases with
    | last => simp [finSumFinEquiv, faceCoordinates]
    | cast a => simp [finSumFinEquiv, faceCoordinates]
  | inr a =>
    have ha : a = 0 := Subsingleton.elim _ _
    subst ha
    simp [finSumFinEquiv, faceCoordinates]

theorem firstFace_finCoordinates (a : Fin (m + 2)) :
    faceCoordinates (m := m) (0 : Fin 2)
      ((finSumFinEquiv : Fin (m + 1) ⊕ Fin 1 ≃ Fin ((m + 1) + 1)).symm a) =
    (finSumFinEquiv : Fin m ⊕ Fin 2 ≃ Fin (m + 2)).symm a := by
  apply (finSumFinEquiv : Fin m ⊕ Fin 2 ≃ Fin (m + 2)).injective
  rw [firstFace_flatten, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- In the common ambient coordinates, the first face is literally inclusion. -/
theorem firstFace_matrix (x : BlockCover (Fin 2) m B) :
    sumRelabel (coverMatrix (faceCover (0 : Fin 2) x)) = sumRelabel (coverMatrix x) := by
  rw [coverMatrix_face]
  apply Units.ext
  ext a b
  change (coverMatrix x).val (faceCoordinates (0 : Fin 2) (finSumFinEquiv.symm a))
    (faceCoordinates (0 : Fin 2) (finSumFinEquiv.symm b)) =
      (coverMatrix x).val (finSumFinEquiv.symm a) (finSumFinEquiv.symm b)
  rw [firstFace_finCoordinates, firstFace_finCoordinates]

def signedPairCover : BlockCover (Fin 2) m B →* BlockCover (Fin 1) (m + 1) B :=
  scaledFaceCover (1 : Fin 2) (-1)

def signedPairBase : BlockStabilizer (Fin 2) m B →* BlockStabilizer (Fin 1) (m + 1) B :=
  scaledFaceBase (1 : Fin 2) (-1)

theorem signedPair_projection (x : BlockCover (Fin 2) m B) :
    signedPairBase (blockProjection x) = blockProjection (signedPairCover x) :=
  scaledFaceBase_projection _ _ x

theorem signedPair_matrix (x : BlockCover (Fin 2) m B) :
    sumRelabel (coverMatrix (signedPairCover x)) = (pairNormalizer m B).val *
      sumRelabel (coverMatrix (faceCover (0 : Fin 2) x)) * (pairNormalizer m B).val⁻¹ := by
  rw [signedPairCover, coverMatrix_scaledFace, map_mul, map_mul, map_inv]
  change MatrixGeometry.relabel finSumFinEquiv
    (MatrixGeometry.singleDiagonal (.inl (Fin.last m)) (-1)) *
      sumRelabel (coverMatrix (faceCover (1 : Fin 2) x)) *
    (MatrixGeometry.relabel finSumFinEquiv
      (MatrixGeometry.singleDiagonal (.inl (Fin.last m)) (-1)))⁻¹ = _
  rw [MatrixGeometry.relabel_singleDiagonal, MatrixCoordinates.upstream_d, unsignedPair_matrix]
  change d (pairFreeIndex m) (-1) * (_ * _ * _) * (d (pairFreeIndex m) (-1))⁻¹ =
    ev (K1.sgnWord (pairFixedIndex m) (pairFreeIndex m) pairIndices_ne.symm) *
      sumRelabel (coverMatrix (faceCover (0 : Fin 2) x)) *
        (ev (K1.sgnWord (pairFixedIndex m) (pairFreeIndex m) pairIndices_ne.symm))⁻¹
  rw [signedSwap_eq_diagonal_swap (pairFreeIndex m) (pairFixedIndex m) pairIndices_ne]
  group

theorem signedPair_agrees_on_steinberg (z : Steinberg m B) :
    signedPairCover (SemidirectProduct.inr z : BlockCover (Fin 2) m B) =
      faceCover (0 : Fin 2) (SemidirectProduct.inr z) := by
  rw [signedPairCover, scaledFaceCover_inr, faceCover_inr]

theorem signedPair_agrees_on_kernel (z : (Elementary.representation (n := m) (R := B)).ker) :
    signedPairCover (blockKernelInclusion z : BlockCover (Fin 2) m B) =
      faceCover (0 : Fin 2) (blockKernelInclusion z) :=
  signedPair_agrees_on_steinberg z.val

theorem signedPair_ambient_matrix (x : BlockCover (Fin 2) m B) :
    sumRelabel (coverMatrix (signedPairCover x)) =
      (pairNormalizer m B).val * sumRelabel (coverMatrix x) * (pairNormalizer m B).val⁻¹ := by
  rw [signedPair_matrix, firstFace_matrix]

/-- An actual matrix stabilizer included in its ambient elementary group. -/
def stabilizerToElementary {l : ℕ} : Stabilizer m l B →* K1.E (m + l) B :=
  ((sumRelabel (m := m) (l := l) (B := B)).comp (Stabilizer m l B).subtype).codRestrict _
    (fun U => U.property.2)

section Local
variable {K : Type*} [Field K] (ε : B →+* K) (hunit : ∀ b : B, ε b ≠ 0 → IsUnit b)

def actualSignedPair (hm : 5 ≤ m) : Stabilizer m 2 B →* Stabilizer (m + 1) 1 B :=
  (stabilizerEquiv ε hunit (show 5 ≤ m + 1 by omega)).toMonoidHom.comp
    (signedPairBase.comp (stabilizerEquiv ε hunit hm).symm.toMonoidHom)

theorem actualSignedPair_projection (hm : 5 ≤ m) (x : BlockCover (Fin 2) m B) :
    actualSignedPair ε hunit hm (toStabilizer (blockProjection x)) =
      toStabilizer (blockProjection (signedPairCover x)) := by
  change stabilizerEquiv ε hunit (show 5 ≤ m + 1 by omega) (signedPairBase
    ((stabilizerEquiv ε hunit hm).symm (stabilizerEquiv ε hunit hm (blockProjection x)))) = _
  rw [MulEquiv.symm_apply_apply, signedPair_projection]
  rfl

theorem actualFirstFace_inclusion (hm : 5 ≤ m) (U : Stabilizer m 2 B) :
    stabilizerToElementary (actualFace ε hunit hm (0 : Fin 2) U) =
      stabilizerToElementary U := by
  obtain ⟨y, rfl⟩ := toStabilizer_surjective ε hunit hm U
  obtain ⟨x, rfl⟩ := blockProjection_surjective y
  rw [actualFace_projection]
  apply Subtype.ext
  exact firstFace_matrix x

/-- The normalized second face is conjugation by an element of E, not merely of GL. -/
theorem actualSignedPair_conjugation (hm : 5 ≤ m) (U : Stabilizer m 2 B) :
    stabilizerToElementary (actualSignedPair ε hunit hm U) =
      pairNormalizer m B * stabilizerToElementary U * (pairNormalizer m B)⁻¹ := by
  obtain ⟨y, rfl⟩ := toStabilizer_surjective ε hunit hm U
  obtain ⟨x, rfl⟩ := blockProjection_surjective y
  rw [actualSignedPair_projection]
  apply Subtype.ext
  exact signedPair_ambient_matrix x

end Local

end
end FrameFaces
end AllPrimeGroups
