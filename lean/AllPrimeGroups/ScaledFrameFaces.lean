import AllPrimeGroups.FrameFaceGeometry

/-! Unit corrections of the frame faces.

Scaling only the forgotten row realizes diagonal conjugation in the new free coordinate.
It leaves the old Steinberg factor, and hence its matrix kernel, pointwise unchanged. This
allows signed elementary coordinate moves to replace the unsigned permutations of the faces. -/

namespace AllPrimeGroups

namespace MatrixGeometry
variable {B ι : Type*} [Ring B] [Fintype ι] [DecidableEq ι]

theorem singleDiagonal_conj_entry (i : ι) (u : Bˣ) (A : (Matrix ι ι B)ˣ) (a b : ι) :
    (singleDiagonal i u * A * (singleDiagonal i u)⁻¹).val a b =
      (if a = i then (u : B) else 1) * A.val a b *
        (if b = i then ((u⁻¹ : Bˣ) : B) else 1) := by
  change (Matrix.diagonal (fun j : ι => ((if j = i then u else 1 : Bˣ) : B)) *
    (A.val : Matrix ι ι B) *
      Matrix.diagonal (fun j : ι => (if j = i then u else 1 : Bˣ).inv)) a b = _
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  split_ifs <;> simp_all

end MatrixGeometry

namespace FrameFaces
noncomputable section
open Matrix FrameStabilizer FrameBlocks GLPres

variable {B : Type*} [Ring B] {m l : ℕ}

def scaleRow (u : Bˣ) : Row m B →* Row m B where
  toFun r := Multiplicative.ofAdd (fun a => (u : B) * Multiplicative.toAdd r a)
  map_one' := by
    apply Multiplicative.toAdd.injective
    funext a
    exact mul_zero _
  map_mul' r s := by
    apply Multiplicative.toAdd.injective
    funext a
    exact mul_add _ _ _

theorem scaleRow_act (u : Bˣ) (A : (Matrix (Fin m) (Fin m) B)ˣ) (r : Row m B) :
    scaleRow u (rowAct A r) = rowAct A (scaleRow u r) := by
  apply Multiplicative.toAdd.injective
  funext a
  change (u : B) * (Multiplicative.toAdd r ᵥ* A.inv) a =
    ((fun b => (u : B) * Multiplicative.toAdd r b) ᵥ* A.inv) a
  simp only [Matrix.vecMul, dotProduct, Finset.mul_sum, mul_assoc]

def scaleRowsAt (i : Fin l) (u : Bˣ) : (Fin l → Row m B) →* (Fin l → Row m B) where
  toFun r j := if j = i then scaleRow u (r j) else r j
  map_one' := by funext j; split_ifs <;> simp
  map_mul' r s := by funext j; split_ifs <;> simp_all

theorem scaleRowsAt_act (i : Fin l) (u : Bˣ) (A : (Matrix (Fin m) (Fin m) B)ˣ)
    (r : Fin l → Row m B) : scaleRowsAt i u (rowsAct A r) = rowsAct A (scaleRowsAt i u r) := by
  funext j
  change (if j = i then scaleRow u (rowAct A (r j)) else rowAct A (r j)) =
    rowAct A (if j = i then scaleRow u (r j) else r j)
  split_ifs <;> first | exact scaleRow_act u A (r j) | rfl

def scaleCover (i : Fin l) (u : Bˣ) : BlockCover (Fin l) m B →* BlockCover (Fin l) m B :=
  SemidirectProduct.map (scaleRowsAt i u) (MonoidHom.id _) (fun z =>
    MonoidHom.ext (scaleRowsAt_act i u (Elementary.representation z)))

def scaleBase (i : Fin l) (u : Bˣ) : BlockStabilizer (Fin l) m B →* BlockStabilizer (Fin l) m B :=
  SemidirectProduct.map (scaleRowsAt i u) (MonoidHom.id _) (fun A =>
    MonoidHom.ext (scaleRowsAt_act i u A.val))

theorem scaleCover_inr (i : Fin l) (u : Bˣ) (z : Steinberg m B) :
    scaleCover i u (SemidirectProduct.inr z : BlockCover (Fin l) m B) =
      SemidirectProduct.inr z := by
  apply SemidirectProduct.ext
  · exact map_one (scaleRowsAt i u)
  · rfl

theorem blockProjection_scaleCover (i : Fin l) (u : Bˣ) (x : BlockCover (Fin l) m B) :
    blockProjection (scaleCover i u x) = scaleBase i u (blockProjection x) := rfl

theorem coverMatrix_scaleCover (i : Fin l) (u : Bˣ) (x : BlockCover (Fin l) m B) :
    coverMatrix (scaleCover i u x) = MatrixGeometry.singleDiagonal (.inr i) u *
      coverMatrix x * (MatrixGeometry.singleDiagonal (.inr i) u)⁻¹ := by
  apply Units.ext
  ext a b
  rw [MatrixGeometry.singleDiagonal_conj_entry, coverMatrix_val, coverMatrix_val]
  simp only [scaleCover, SemidirectProduct.map_right, SemidirectProduct.map_left, MonoidHom.id_apply]
  cases a with
  | inl a => cases b <;> simp [Matrix.fromBlocks]
  | inr a =>
    cases b with
    | inl b =>
      change (rowsMatrix (scaleRowsAt i u x.left) * (Elementary.representation x.right).val) a b = _
      by_cases ha : a = i
      · subst ha
        simp [Matrix.mul_apply, rowsMatrix, scaleRowsAt, scaleRow, Finset.mul_sum, mul_assoc]
      · simp [Matrix.mul_apply, rowsMatrix, scaleRowsAt, ha]
    | inr b =>
      by_cases ha : a = i <;> by_cases hb : b = i <;>
        simp_all [Matrix.fromBlocks_apply₂₂, Matrix.one_apply, eq_comm]

def scaledFaceCover (i : Fin (l + 1)) (u : Bˣ) :
    BlockCover (Fin (l + 1)) m B →* BlockCover (Fin l) (m + 1) B :=
  (faceCover i).comp (scaleCover i u)

def scaledFaceBase (i : Fin (l + 1)) (u : Bˣ) :
    BlockStabilizer (Fin (l + 1)) m B →* BlockStabilizer (Fin l) (m + 1) B :=
  (faceBase i).comp (scaleBase i u)

theorem scaledFaceBase_projection (i : Fin (l + 1)) (u : Bˣ)
    (x : BlockCover (Fin (l + 1)) m B) :
    scaledFaceBase i u (blockProjection x) = blockProjection (scaledFaceCover i u x) := by
  rw [scaledFaceBase, MonoidHom.comp_apply, ← blockProjection_scaleCover, faceBase_projection]
  rfl

theorem scaledFaceCover_inr (i : Fin (l + 1)) (u : Bˣ) (z : Steinberg m B) :
    scaledFaceCover i u (SemidirectProduct.inr z : BlockCover (Fin (l + 1)) m B) =
      (SemidirectProduct.inr (Kernel.padSteinberg z) : BlockCover (Fin l) (m + 1) B) := by
  rw [scaledFaceCover, MonoidHom.comp_apply, scaleCover_inr, faceCover_inr]

theorem scaledFaces_agree_on_kernel (i j : Fin (l + 1)) (u v : Bˣ)
    (z : (Elementary.representation (n := m) (R := B)).ker) :
    scaledFaceCover i u (blockKernelInclusion z : BlockCover (Fin (l + 1)) m B) =
      scaledFaceCover j v (blockKernelInclusion z : BlockCover (Fin (l + 1)) m B) := by
  change scaledFaceCover i u (SemidirectProduct.inr z.val) =
    scaledFaceCover j v (SemidirectProduct.inr z.val)
  rw [scaledFaceCover_inr, scaledFaceCover_inr]

theorem coverMatrix_scaledFace (i : Fin (l + 1)) (u : Bˣ)
    (x : BlockCover (Fin (l + 1)) m B) :
    coverMatrix (scaledFaceCover i u x) = MatrixGeometry.singleDiagonal (.inl (Fin.last m)) u *
      coverMatrix (faceCover i x) * (MatrixGeometry.singleDiagonal (.inl (Fin.last m)) u)⁻¹ := by
  rw [scaledFaceCover, MonoidHom.comp_apply, coverMatrix_face, coverMatrix_scaleCover,
    map_mul, map_mul, map_inv, MatrixGeometry.relabel_singleDiagonal]
  have hi : (faceCoordinates (m := m) i).symm (.inr i) = .inl (Fin.last m) :=
    (faceCoordinates (m := m) i).symm_apply_eq.mpr (faceCoordinates_last i).symm
  rw [hi, coverMatrix_face]

end
end FrameFaces
end AllPrimeGroups
