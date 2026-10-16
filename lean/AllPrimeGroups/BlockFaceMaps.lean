import AllPrimeGroups.MultiRowStabilizer
import Mathlib.Data.Fin.Tuple.Basic

/-! Face maps on the central covers of rectangular frame stabilizers.

Forgetting fixed coordinate `i` moves its row into the smaller Steinberg factor. The other
rows acquire a zero in that new free coordinate. Every face has the same restriction to the
old Steinberg factor, hence also to its matrix kernel. Kernel preservation descends the maps
to the elementary block models via Mathlib's surjective lifting API. -/

namespace AllPrimeGroups
namespace FrameFaces

open Matrix FrameStabilizer GLPres

variable {B : Type*} [Ring B] {m l : ℕ}

def extendRow : Row m B →* Row (m + 1) B where
  toFun r := Multiplicative.ofAdd (Fin.lastCases 0 (Multiplicative.toAdd r))
  map_one' := by
    apply Multiplicative.toAdd.injective
    funext i
    induction i using Fin.lastCases <;> simp
  map_mul' r s := by
    apply Multiplicative.toAdd.injective
    funext i
    induction i using Fin.lastCases <;> simp

theorem extendRow_last (r : Row m B) : Multiplicative.toAdd (extendRow r) (Fin.last m) = 0 := by
  change Fin.lastCases (0 : B) (Multiplicative.toAdd r) (Fin.last m) = (0 : B)
  exact Fin.lastCases_last

theorem extendRow_castSucc (r : Row m B) (i : Fin m) :
    Multiplicative.toAdd (extendRow r) i.castSucc = Multiplicative.toAdd r i := by
  change Fin.lastCases 0 (Multiplicative.toAdd r) i.castSucc = Multiplicative.toAdd r i
  exact Fin.lastCases_castSucc i

theorem extendRow_pad (A : (Matrix (Fin m) (Fin m) B)ˣ) (r : Row m B) :
    rowAct (Kernel.padUnitsHom A) (extendRow r) = extendRow (rowAct A r) := by
  apply Multiplicative.toAdd.injective
  rw [rowAct_apply, ← map_inv Kernel.padUnitsHom A]
  funext j
  induction j using Fin.lastCases with
  | last =>
    simp only [Matrix.vecMul, dotProduct, Fin.sum_univ_castSucc, LocalGL.pad_apply,
      LocalGL.coordinateEquiv_symm_castSucc, LocalGL.coordinateEquiv_symm_last,
      extendRow_last, extendRow_castSucc, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, mul_zero, zero_mul, Finset.sum_const_zero, zero_add]
  | cast j =>
    simp only [Matrix.vecMul, dotProduct, Fin.sum_univ_castSucc, LocalGL.pad_apply,
      LocalGL.coordinateEquiv_symm_castSucc, LocalGL.coordinateEquiv_symm_last,
      extendRow_last, extendRow_castSucc, rowAct_apply, Matrix.fromBlocks_apply₁₁,
      Matrix.fromBlocks_apply₂₁, Matrix.zero_apply, zero_mul, add_zero]

theorem rowAct_e_fixed (p : Root (m + 1)) (a : B) (r : Row (m + 1) B)
    (hr : Multiplicative.toAdd r p.row = 0) : rowAct (Elementary.e p a) r = r := by
  apply Multiplicative.toAdd.injective
  rw [rowAct_apply, Elementary.e_inv, Elementary.coe_e, Matrix.vecMul_add, Matrix.vecMul_one]
  have h : Multiplicative.toAdd r ᵥ* Matrix.single p.row p.col (-a) = 0 := by
    funext j
    by_cases hj : j = p.col
    · subst hj
      simp [Matrix.vecMul, dotProduct, Matrix.single_apply, hr]
    · simp [Matrix.vecMul, dotProduct, Ne.symm hj]
  rw [h, add_zero]

theorem extendRow_rowMat (s r : Row m B) : rowAct (rowMatHom s) (extendRow r) = extendRow r := by
  have h : ∀ L : List (Fin m), rowAct (LocalGL.rowProd (Multiplicative.toAdd s) L)
      (extendRow r) = extendRow r := by
    intro L
    induction L with
    | nil => simp [LocalGL.rowProd]
    | cons b L ih =>
      rw [show LocalGL.rowProd (Multiplicative.toAdd s) (b :: L) =
        LocalGL.rowFactor (Multiplicative.toAdd s) b * LocalGL.rowProd (Multiplicative.toAdd s) L by
          simp [LocalGL.rowProd], map_mul, MulAut.mul_apply, ih]
      apply rowAct_e_fixed
      exact extendRow_last r
  exact h (List.finRange m)

theorem extendRow_toSteinberg (x : Cover m B) (r : Row m B) :
    rowAct (Elementary.representation (toSteinberg x)) (extendRow r) =
      extendRow (rowAct (Elementary.representation x.right) r) := by
  have h := DFunLike.congr_fun (representation_toSteinberg (m := m) (B := B)) x
  change Elementary.representation (toSteinberg x) = toMatrix x at h
  rw [h, toMatrix_apply,
    map_mul, MulAut.mul_apply, extendRow_pad, extendRow_rowMat]

def selectCover (i : Fin (l + 1)) : BlockCover (Fin (l + 1)) m B →* Cover m B where
  toFun x := ⟨x.left i, x.right⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Forget one of the fixed columns on the central cover. -/
def faceCover (i : Fin (l + 1)) : BlockCover (Fin (l + 1)) m B →* BlockCover (Fin l) (m + 1) B where
  toFun x := ⟨fun j => extendRow (x.left (i.succAbove j)), toSteinberg (selectCover i x)⟩
  map_one' := by
    apply SemidirectProduct.ext
    · funext j
      exact map_one extendRow
    · exact map_one (toSteinberg.comp (selectCover i))
  map_mul' x y := by
    apply SemidirectProduct.ext
    · funext j
      change extendRow (x.left (i.succAbove j) * rowAct (Elementary.representation x.right)
        (y.left (i.succAbove j))) = extendRow (x.left (i.succAbove j)) *
        rowAct (Elementary.representation (toSteinberg (selectCover i x)))
          (extendRow (y.left (i.succAbove j)))
      rw [map_mul, extendRow_toSteinberg]
      rfl
    · exact map_mul (toSteinberg.comp (selectCover i)) x y

theorem faceCover_inr (i : Fin (l + 1)) (z : Steinberg m B) :
    faceCover i (SemidirectProduct.inr z : BlockCover (Fin (l + 1)) m B) =
      (SemidirectProduct.inr (Kernel.padSteinberg z) : BlockCover (Fin l) (m + 1) B) := by
  apply SemidirectProduct.ext
  · funext j
    exact map_one extendRow
  · exact toSteinberg_inr z

theorem faceCover_kernel (i : Fin (l + 1)) {x : BlockCover (Fin (l + 1)) m B}
    (hx : blockProjection x = 1) : blockProjection (faceCover i x) = 1 := by
  obtain ⟨hl, hr⟩ := (blockProjection_eq_one_iff x).mp hx
  apply (blockProjection_eq_one_iff _).mpr
  constructor
  · funext j
    change extendRow (x.left (i.succAbove j)) = 1
    rw [hl]
    exact map_one extendRow
  · change Elementary.representation (toSteinberg (selectCover i x)) = 1
    rw [← MonoidHom.comp_apply, representation_toSteinberg]
    apply (toMatrix_eq_one_iff _).mpr
    exact ⟨congrFun hl i, hr⟩

/-- The cover face descends to the elementary model by preserving the projection kernel. -/
noncomputable def faceBase (i : Fin (l + 1)) :
    BlockStabilizer (Fin (l + 1)) m B →* BlockStabilizer (Fin l) (m + 1) B :=
  blockProjection.liftOfSurjective blockProjection_surjective
    ⟨blockProjection.comp (faceCover i), fun _ hx => faceCover_kernel i hx⟩

theorem faceBase_projection (i : Fin (l + 1)) (x : BlockCover (Fin (l + 1)) m B) :
    faceBase i (blockProjection x) = blockProjection (faceCover i x) :=
  MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ x

/-- All faces agree on the smaller Steinberg factor, before any passage to stable groups. -/
theorem faces_agree_on_steinberg (i j : Fin (l + 1)) (z : Steinberg m B) :
    faceCover i (SemidirectProduct.inr z : BlockCover (Fin (l + 1)) m B) =
      faceCover j (SemidirectProduct.inr z : BlockCover (Fin (l + 1)) m B) := by
  rw [faceCover_inr, faceCover_inr]

theorem faces_agree_on_kernel (i j : Fin (l + 1))
    (z : (Elementary.representation (n := m) (R := B)).ker) :
    faceCover i (blockKernelInclusion z : BlockCover (Fin (l + 1)) m B) =
      faceCover j (blockKernelInclusion z : BlockCover (Fin (l + 1)) m B) :=
  faces_agree_on_steinberg i j z.val

end FrameFaces
end AllPrimeGroups
