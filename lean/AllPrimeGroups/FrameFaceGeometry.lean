import AllPrimeGroups.FrameBlockMatrices
import AllPrimeGroups.BlockFaceMaps

/-! Actual frame stabilizers and the coordinate geometry of the cover faces.

The coordinate equivalence moves the forgotten fixed coordinate into the last free slot.
Conjugation by its permutation matrix is expressed using `MatrixGeometry.relabel`, so no
choice of a matrix representative or word is needed. -/

namespace AllPrimeGroups
namespace FrameFaces

noncomputable section
open Matrix FrameStabilizer FrameBlocks

variable {B : Type*} [Ring B] {m l : ℕ}

/-- Target coordinates, viewed in the source after forgetting fixed column `i`. -/
def faceCoordinates (i : Fin (l + 1)) : Fin (m + 1) ⊕ Fin l ≃ Fin m ⊕ Fin (l + 1) where
  toFun x := match x with
    | .inl a => Fin.lastCases (Sum.inr i) (fun b => Sum.inl b) a
    | .inr j => .inr (i.succAbove j)
  invFun x := match x with
    | .inl b => .inl b.castSucc
    | .inr j => Fin.insertNth (α := fun _ => Fin (m + 1) ⊕ Fin l) i (Sum.inl (Fin.last m))
        (fun k => Sum.inr k) j
  left_inv x := by
    cases x with
    | inl a =>
      induction a using Fin.lastCases with
      | last => simp
      | cast b => simp
    | inr j => simp
  right_inv x := by
    cases x with
    | inl b => simp
    | inr j =>
      induction j using i.succAboveCases with
      | x => simp
      | p j => simp

@[simp] theorem faceCoordinates_last (i : Fin (l + 1)) :
    faceCoordinates (m := m) i (.inl (Fin.last m)) = .inr i := by
  simp [faceCoordinates]

@[simp] theorem faceCoordinates_castSucc (i : Fin (l + 1)) (a : Fin m) :
    faceCoordinates i (.inl a.castSucc) = .inl a := by
  simp [faceCoordinates]

@[simp] theorem faceCoordinates_inr (i : Fin (l + 1)) (j : Fin l) :
    faceCoordinates (m := m) i (.inr j) = .inr (i.succAbove j) := rfl

def coverMatrix : BlockCover (Fin l) m B →*
    (Matrix (Fin m ⊕ Fin l) (Fin m ⊕ Fin l) B)ˣ := matrixMap.comp blockProjection

theorem coverMatrix_val (x : BlockCover (Fin l) m B) :
    (coverMatrix x : Matrix (Fin m ⊕ Fin l) (Fin m ⊕ Fin l) B) =
      Matrix.fromBlocks (Elementary.representation x.right).val 0
        (rowsMatrix x.left * (Elementary.representation x.right).val) 1 :=
  fullMatrix_val _

theorem toMatrix_castSucc_entry (x : Cover m B) (a : Fin m) (b : Fin (m + 1)) :
    (toMatrix x : Matrix (Fin (m + 1)) (Fin (m + 1)) B) a.castSucc b =
      (Kernel.padUnitsHom (Elementary.representation x.right)).val a.castSucc b := by
  have h := congrFun (GLPres.rowMat_mulVec (Multiplicative.toAdd x.left)
    ((Kernel.padUnitsHom (Elementary.representation x.right)).val *ᵥ Pi.single b 1)) a.castSucc
  simp only [GLPres.castSucc_ne_last', ↓reduceIte, Matrix.mulVec_single_one] at h
  exact h

theorem toMatrix_last_castSucc_entry (x : Cover m B) (b : Fin m) :
    (toMatrix x : Matrix (Fin (m + 1)) (Fin (m + 1)) B) (Fin.last m) b.castSucc =
      (Multiplicative.toAdd x.left ᵥ* (Elementary.representation x.right).val) b := by
  have h := congrFun (GLPres.rowMat_mulVec (Multiplicative.toAdd x.left)
    ((Kernel.padUnitsHom (Elementary.representation x.right)).val *ᵥ Pi.single b.castSucc 1))
      (Fin.last m)
  simp only [↓reduceIte, Matrix.mulVec_single_one] at h
  change (toMatrix x).val (Fin.last m) b.castSucc =
    (Kernel.padUnitsHom (Elementary.representation x.right)).val (Fin.last m) b.castSucc +
      ∑ a, Multiplicative.toAdd x.left a *
        (Kernel.padUnitsHom (Elementary.representation x.right)).val a.castSucc b.castSucc at h
  simp only [LocalGL.pad_apply, LocalGL.coordinateEquiv_symm_last,
    LocalGL.coordinateEquiv_symm_castSucc, Matrix.fromBlocks_apply₂₁,
    Matrix.fromBlocks_apply₁₁, Matrix.zero_apply, zero_add] at h
  exact h

theorem toMatrix_last_column_entry (x : Cover m B) (a : Fin (m + 1)) :
    (toMatrix x : Matrix (Fin (m + 1)) (Fin (m + 1)) B) a (Fin.last m) =
      if a = Fin.last m then 1 else 0 := by
  have h := congrFun (toMatrix_last x) a
  simpa only [Matrix.mulVec_single_one, Matrix.col_apply, Pi.single_apply] using h

theorem coverMatrix_face (i : Fin (l + 1)) (x : BlockCover (Fin (l + 1)) m B) :
    coverMatrix (faceCover i x) = MatrixGeometry.relabel (faceCoordinates i).symm (coverMatrix x) := by
  apply Units.ext
  ext a b
  change (coverMatrix (faceCover i x)).val a b =
    (coverMatrix x).val (faceCoordinates i a) (faceCoordinates i b)
  rw [coverMatrix_val, coverMatrix_val]
  have hrep : Elementary.representation (faceCover i x).right = toMatrix (selectCover i x) :=
    DFunLike.congr_fun representation_toSteinberg (selectCover i x)
  rw [hrep]
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      induction a using Fin.lastCases with
      | last =>
        induction b using Fin.lastCases with
        | last => simp [toMatrix_last_column_entry]
        | cast b =>
          simp only [Matrix.fromBlocks_apply₁₁, faceCoordinates_last, faceCoordinates_castSucc,
            Matrix.fromBlocks_apply₂₁, toMatrix_last_castSucc_entry]
          rfl
      | cast a =>
        induction b using Fin.lastCases with
        | last => simp [toMatrix_last_column_entry]
        | cast b =>
          simp only [Matrix.fromBlocks_apply₁₁, faceCoordinates_castSucc,
            toMatrix_castSucc_entry, LocalGL.pad_apply, LocalGL.coordinateEquiv_symm_castSucc,
            Matrix.fromBlocks_apply₁₁]
          rfl
    | inr b =>
      induction a using Fin.lastCases with
      | last => simp
      | cast a => simp
  | inr a =>
    cases b with
    | inl b =>
      induction b using Fin.lastCases with
      | last =>
        simp only [Matrix.fromBlocks_apply₂₁, faceCoordinates_inr, faceCoordinates_last,
          Matrix.fromBlocks_apply₂₂, Matrix.mul_apply, Fin.sum_univ_castSucc,
          toMatrix_last_column_entry, GLPres.castSucc_ne_last', ↓reduceIte,
          rowsMatrix, faceCover, MonoidHom.coe_mk, OneHom.coe_mk,
          extendRow_last, mul_zero, Finset.sum_const_zero, zero_mul, add_zero, Matrix.one_apply]
        exact (ite_eq_right (Fin.succAbove_ne i a)).symm
      | cast b =>
        simp only [Matrix.fromBlocks_apply₂₁, faceCoordinates_inr, faceCoordinates_castSucc,
          Matrix.mul_apply, Fin.sum_univ_castSucc, toMatrix_castSucc_entry,
          LocalGL.pad_apply, LocalGL.coordinateEquiv_symm_castSucc,
          Matrix.fromBlocks_apply₁₁, rowsMatrix, faceCover, MonoidHom.coe_mk, OneHom.coe_mk,
          extendRow_castSucc, extendRow_last, zero_mul, add_zero]
        rfl
    | inr b =>
      simp only [Matrix.fromBlocks_apply₂₂, faceCoordinates_inr, Matrix.one_apply]
      congr 1
      exact propext i.succAbove_right_injective.eq_iff.symm

/-- Forgetting a fixed column enlarges its matrix stabilizer by an injective map. -/
theorem faceBase_injective (i : Fin (l + 1)) :
    Function.Injective (faceBase (m := m) (B := B) i) := by
  intro U V h
  obtain ⟨x, rfl⟩ := blockProjection_surjective U
  obtain ⟨y, rfl⟩ := blockProjection_surjective V
  have hM := congrArg matrixMap h
  rw [faceBase_projection, faceBase_projection] at hM
  change coverMatrix (faceCover i x) = coverMatrix (faceCover i y) at hM
  rw [coverMatrix_face, coverMatrix_face] at hM
  have hinj : Function.Injective (MatrixGeometry.relabel (R := B) (faceCoordinates (m := m) i).symm) :=
    Units.map_injective (Matrix.reindexRingEquiv B (faceCoordinates (m := m) i).symm).injective
  exact toFull_injective (fullMatrix_injective (hinj hM))

section Local
variable {K : Type*} [Field K] (ε : B →+* K) (hunit : ∀ b : B, ε b ≠ 0 → IsUnit b)

/-- The face on actual matrix stabilizers, transported through the proved block identification. -/
def actualFace (hm : 5 ≤ m) (i : Fin (l + 1)) :
    Stabilizer m (l + 1) B →* Stabilizer (m + 1) l B :=
  (stabilizerEquiv ε hunit (show 5 ≤ m + 1 by omega)).toMonoidHom.comp
    ((faceBase i).comp (stabilizerEquiv ε hunit hm).symm.toMonoidHom)

theorem actualFace_projection (hm : 5 ≤ m) (i : Fin (l + 1))
    (x : BlockCover (Fin (l + 1)) m B) :
    actualFace ε hunit hm i (toStabilizer (blockProjection x)) =
      toStabilizer (blockProjection (faceCover i x)) := by
  change stabilizerEquiv ε hunit (show 5 ≤ m + 1 by omega) (faceBase i
    ((stabilizerEquiv ε hunit hm).symm (stabilizerEquiv ε hunit hm (blockProjection x)))) = _
  rw [MulEquiv.symm_apply_apply, faceBase_projection]
  rfl

theorem actualFace_val (hm : 5 ≤ m) (i : Fin (l + 1)) (U : Stabilizer m (l + 1) B) :
    (actualFace ε hunit hm i U).val = MatrixGeometry.relabel (faceCoordinates i).symm U.val := by
  obtain ⟨y, rfl⟩ := toStabilizer_surjective ε hunit hm U
  obtain ⟨x, rfl⟩ := blockProjection_surjective y
  rw [actualFace_projection]
  exact coverMatrix_face i x

theorem actualFace_injective (hm : 5 ≤ m) (i : Fin (l + 1)) :
    Function.Injective (actualFace ε hunit hm i) :=
  (stabilizerEquiv ε hunit (show 5 ≤ m + 1 by omega)).injective.comp
    ((faceBase_injective i).comp (stabilizerEquiv ε hunit hm).symm.injective)

end Local
end
end FrameFaces
end AllPrimeGroups
