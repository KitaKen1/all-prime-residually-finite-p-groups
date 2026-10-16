import AllPrimeGroups.MultiRowStabilizer
import AllPrimeGroups.CoordinateStability
import AllPrimeGroups.ExtensionOperations

/-! Identification of rectangular models with actual multi-column stabilizers.

Use sum indices for the free and fixed coordinates. The shape of a fixing matrix and its
invertible upper-left block are reused from the generic part of the pinned upstream source.
K1 reflection along an arbitrary coordinate embedding supplies elementary membership. -/

namespace AllPrimeGroups
namespace FrameBlocks
noncomputable section

open Matrix FrameStabilizer
open AllPrimeGroups.MatrixGeometry

variable {B : Type*} [Ring B] {m l : ℕ}

def rowsMatrix (r : Fin l → GLPres.Row m B) : Matrix (Fin l) (Fin m) B :=
  fun i j => Multiplicative.toAdd (r i) j

def rowsParameters : (Fin l → GLPres.Row m B) →* (Fin l × Fin m → Multiplicative B) where
  toFun r p := Multiplicative.ofAdd (Multiplicative.toAdd (r p.1) p.2)
  map_one' := rfl
  map_mul' _ _ := rfl

def lowerRows : (Fin l → GLPres.Row m B) →* (Matrix (Fin m ⊕ Fin l) (Fin m ⊕ Fin l) B)ˣ :=
  rectangleLower.comp rowsParameters

theorem lowerRows_val (r : Fin l → GLPres.Row m B) :
    (lowerRows r : Matrix (Fin m ⊕ Fin l) (Fin m ⊕ Fin l) B) =
      Matrix.fromBlocks 1 0 (rowsMatrix r) 1 := rfl

theorem rowsMatrix_act (A : (Matrix (Fin m) (Fin m) B)ˣ) (r : Fin l → GLPres.Row m B) :
    rowsMatrix (rowsAct A r) = rowsMatrix r *
      ((A⁻¹ : (Matrix (Fin m) (Fin m) B)ˣ) : Matrix (Fin m) (Fin m) B) := rfl

theorem lowerRows_conj (A : (Matrix (Fin m) (Fin m) B)ˣ) (r : Fin l → GLPres.Row m B) :
    lowerRows (rowsAct A r) = blockInclusion A * lowerRows r * (blockInclusion A)⁻¹ := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, ← map_inv blockInclusion A, blockInclusion_val,
    blockInclusion_val, lowerRows_val, lowerRows_val, rowsMatrix_act]
  simp [Matrix.fromBlocks_multiply]

abbrev FullModel (m l : ℕ) (B : Type*) [Ring B] :=
  (Fin l → GLPres.Row m B) ⋊[rowsAct] (Matrix (Fin m) (Fin m) B)ˣ

def fullMatrix : FullModel m l B →* (Matrix (Fin m ⊕ Fin l) (Fin m ⊕ Fin l) B)ˣ :=
  SemidirectProduct.lift lowerRows blockInclusion (fun A => by
    apply MonoidHom.ext
    intro r
    exact lowerRows_conj A r)

theorem fullMatrix_val (x : FullModel m l B) :
    (fullMatrix x : Matrix (Fin m ⊕ Fin l) (Fin m ⊕ Fin l) B) =
      Matrix.fromBlocks (x.right : Matrix (Fin m) (Fin m) B) 0
        (rowsMatrix x.left * (x.right : Matrix (Fin m) (Fin m) B)) 1 := by
  change (lowerRows x.left * blockInclusion x.right).val = _
  rw [Units.val_mul, lowerRows_val, blockInclusion_val]
  simp [Matrix.fromBlocks_multiply]

theorem fullMatrix_injective : Function.Injective (fullMatrix (m := m) (l := l) (B := B)) := by
  intro x y h
  have hv := congrArg Units.val h
  rw [fullMatrix_val, fullMatrix_val] at hv
  have hA : x.right = y.right := by
    apply Units.ext
    ext i j
    exact congrArg (fun M : Matrix (Fin m ⊕ Fin l) (Fin m ⊕ Fin l) B => M (.inl i) (.inl j)) hv
  have hC : rowsMatrix x.left * (x.right : Matrix (Fin m) (Fin m) B) =
      rowsMatrix y.left * (y.right : Matrix (Fin m) (Fin m) B) := by
    ext i j
    exact congrArg (fun M : Matrix (Fin m ⊕ Fin l) (Fin m ⊕ Fin l) B => M (.inr i) (.inl j)) hv
  rw [hA] at hC
  have hr := congrArg (fun M : Matrix (Fin l) (Fin m) B =>
    M * ((y.right⁻¹ : (Matrix (Fin m) (Fin m) B)ˣ) : Matrix (Fin m) (Fin m) B)) hC
  simp only [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one] at hr
  apply SemidirectProduct.ext
  · funext i
    apply Multiplicative.toAdd.injective
    funext j
    exact congrArg (fun M : Matrix (Fin l) (Fin m) B => M i j) hr
  · exact hA

theorem fullMatrix_fixes (x : FullModel m l B) : fullMatrix x ∈ rightFixer := by
  apply (mem_rightFixer_iff _).mpr
  intro i j
  rw [fullMatrix_val]
  cases i <;> simp [Matrix.fromBlocks, Matrix.one_apply]

theorem exists_fullMatrix (U : rightFixer (ι := Fin m) (κ := Fin l) (R := B)) :
    ∃ x : FullModel m l B, fullMatrix x = U.val := by
  let A := rightProjection U
  let C := U.val.val.submatrix Sum.inr Sum.inl
  let r : Fin l → GLPres.Row m B := fun i => Multiplicative.ofAdd
    (fun j => (C * ((A⁻¹ : (Matrix (Fin m) (Fin m) B)ˣ) : Matrix (Fin m) (Fin m) B)) i j)
  refine ⟨⟨r, A⟩, ?_⟩
  apply Units.ext
  rw [fullMatrix_val]
  change Matrix.fromBlocks A.val 0 ((C * A.inv) * A.val) 1 = U.val.val
  rw [Matrix.mul_assoc, A.inv_val, Matrix.mul_one]
  exact (rightFixer_shape U).symm

def sumRelabel : (Matrix (Fin m ⊕ Fin l) (Fin m ⊕ Fin l) B)ˣ →*
    (Matrix (Fin (m + l)) (Fin (m + l)) B)ˣ := relabel finSumFinEquiv

def leftIndex (i : Fin m) : Fin (m + l) := finSumFinEquiv (Sum.inl i)

theorem leftIndex_injective : Function.Injective (leftIndex (m := m) (l := l)) :=
  finSumFinEquiv.injective.comp Sum.inl_injective

theorem right_not_left (j : Fin l) :
    finSumFinEquiv (Sum.inr j) ∉ Set.range (leftIndex (m := m) (l := l)) := by
  rintro ⟨i, hi⟩
  exact Sum.inl_ne_inr (finSumFinEquiv.injective hi)

theorem padded_eq_embed (A : (Matrix (Fin m) (Fin m) B)ˣ) :
    sumRelabel (blockInclusion (κ := Fin l) A) =
      MatrixCoordinates.embed leftIndex leftIndex_injective A := by
  apply Units.ext
  ext i j
  obtain ⟨i, rfl⟩ := (finSumFinEquiv : Fin m ⊕ Fin l ≃ Fin (m + l)).surjective i
  obtain ⟨j, rfl⟩ := (finSumFinEquiv : Fin m ⊕ Fin l ≃ Fin (m + l)).surjective j
  change (Matrix.fromBlocks A.val 0 0 1).submatrix finSumFinEquiv.symm finSumFinEquiv.symm
    (finSumFinEquiv i) (finSumFinEquiv j) = _
  simp only [Matrix.submatrix_apply, Equiv.symm_apply_apply]
  cases i with
  | inl i =>
    cases j with
    | inl j => exact (embed_entry _ A i j).symm
    | inr j =>
      rw [embed_off_column _ A _ (right_not_left j)]
      simp only [Matrix.fromBlocks_apply₁₂, Matrix.zero_apply, Matrix.one_apply]
      exact (ite_eq_right (finSumFinEquiv.injective.ne Sum.inl_ne_inr)).symm
  | inr i =>
    rw [embed_off_row _ A _ (right_not_left i)]
    cases j with
    | inl j =>
      simp only [Matrix.fromBlocks_apply₂₁, Matrix.zero_apply, Matrix.one_apply]
      exact (ite_eq_right (finSumFinEquiv.injective.ne Sum.inr_ne_inl)).symm
    | inr j =>
      simp only [Matrix.fromBlocks_apply₂₂, Matrix.one_apply]
      congr 1
      exact propext ((finSumFinEquiv.injective.eq_iff.trans Sum.inr_injective.eq_iff).symm)

theorem lowerRows_mem_E (r : Fin l → GLPres.Row m B) : sumRelabel (lowerRows r) ∈ K1.E (m + l) B := by
  apply rectangleLower_mem (P := (K1.E (m + l) B).comap sumRelabel) _ (rowsParameters r)
  intro i j a
  change sumRelabel (elementary (Sum.inr i) (Sum.inl j) Sum.inr_ne_inl a) ∈ K1.E (m + l) B
  rw [sumRelabel, relabel_elementary]
  exact K1.e_mem_E ⟨_, _, finSumFinEquiv.injective.ne Sum.inr_ne_inl⟩ a

def toFull : BlockStabilizer (Fin l) m B →* FullModel m l B :=
  SemidirectProduct.map (MonoidHom.id _) (K1.E m B).subtype (fun _ => rfl)

theorem toFull_injective : Function.Injective (toFull (m := m) (l := l) (B := B)) := by
  intro x y h
  apply SemidirectProduct.ext
  · exact congrArg (fun z : FullModel m l B => z.left) h
  · exact Subtype.ext (congrArg (fun z : FullModel m l B => z.right) h)

def matrixMap : BlockStabilizer (Fin l) m B →* (Matrix (Fin m ⊕ Fin l) (Fin m ⊕ Fin l) B)ˣ :=
  fullMatrix.comp toFull

theorem matrixMap_mem_E (x : BlockStabilizer (Fin l) m B) : sumRelabel (matrixMap x) ∈ K1.E (m + l) B := by
  change sumRelabel (lowerRows x.left * blockInclusion x.right.val) ∈ _
  rw [map_mul, padded_eq_embed]
  exact Subgroup.mul_mem _ (lowerRows_mem_E x.left)
    (MatrixCoordinates.embed_mem_E leftIndex leftIndex_injective x.right.property)

/-- Matrices fixing the ordered block of `l` standard columns, inside the elementary group. -/
def Stabilizer (m l : ℕ) (B : Type*) [Ring B] :
    Subgroup (Matrix (Fin m ⊕ Fin l) (Fin m ⊕ Fin l) B)ˣ :=
  rightFixer ⊓ (K1.E (m + l) B).comap sumRelabel

def toStabilizer : BlockStabilizer (Fin l) m B →* Stabilizer m l B :=
  matrixMap.codRestrict _ (fun x => ⟨fullMatrix_fixes (toFull x), matrixMap_mem_E x⟩)

section Local
variable {K : Type*} [Field K] (ε : B →+* K) (hunit : ∀ b : B, ε b ≠ 0 → IsUnit b)

include hunit in
theorem toStabilizer_surjective (hm : 5 ≤ m) :
    Function.Surjective (toStabilizer (m := m) (l := l) (B := B)) := by
  intro U
  obtain ⟨x, hx⟩ := exists_fullMatrix (⟨U.val, U.property.1⟩ : rightFixer)
  have hE : sumRelabel (fullMatrix x) ∈ K1.E (m + l) B := hx ▸ U.property.2
  have hpad : sumRelabel (blockInclusion (κ := Fin l) x.right) ∈ K1.E (m + l) B := by
    have h := Subgroup.mul_mem (K1.E (m + l) B)
      (Subgroup.inv_mem _ (lowerRows_mem_E x.left)) hE
    change (sumRelabel (lowerRows x.left))⁻¹ *
      sumRelabel (lowerRows x.left * blockInclusion x.right) ∈ _ at h
    rwa [map_mul, inv_mul_cancel_left] at h
  rw [padded_eq_embed] at hpad
  have hA := MatrixCoordinates.mem_E_of_embed ε hunit leftIndex leftIndex_injective hm hpad
  refine ⟨⟨x.left, ⟨x.right, hA⟩⟩, ?_⟩
  apply Subtype.ext
  exact hx

noncomputable def stabilizerEquiv (hm : 5 ≤ m) :
    BlockStabilizer (Fin l) m B ≃* Stabilizer m l B :=
  MulEquiv.ofBijective toStabilizer
    ⟨fun _ _ h => toFull_injective (fullMatrix_injective (congrArg Subtype.val h)),
      toStabilizer_surjective ε hunit hm⟩

noncomputable def stabilizerExtension (hm : 5 ≤ m) :
    GroupExtension (Elementary.representation (n := m) (R := B)).ker
      (BlockCover (Fin l) m B) (Stabilizer m l B) :=
  blockExtension.relabelQuotient (stabilizerEquiv ε hunit hm)

include hunit in
theorem stabilizer_isPerfect (hm : 5 ≤ m) : Group.IsPerfect (Stabilizer m l B) := by
  have := blockStabilizer_isPerfect (ι := Fin l) (B := B) (show 3 ≤ m by omega)
  exact Group.IsPerfect.ofSurjective (toStabilizer_surjective ε hunit hm)

end Local
end
end FrameBlocks
end AllPrimeGroups
