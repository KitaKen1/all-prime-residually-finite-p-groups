import AllPrimeGroups.GLTransport
import AllPrimeGroups.KernelExtras
import Mathlib.GroupTheory.SemidirectProduct

/-! The stabilizer of the last standard column as a semidirect product (manuscript Lemma 11.1,
"the stabilizer P of the first standard column is a row strip semidirect GL").

Rows act on the right through inverses: `rowAct A r = r A⁻¹`. The map
`ι (r, A) = rowMat r · pad A` is an injective homomorphism from `rows ⋊ GL_m` onto the
stabilizer of the last standard column in GL_{m+1}. -/

namespace AllPrimeGroups
namespace GLPres

open LocalGL Matrix

variable {B : Type*} [Ring B] {m : ℕ}

theorem castSucc_ne_last' (b : Fin m) : b.castSucc ≠ Fin.last m := (Fin.castSucc_lt_last b).ne

/-- Rows, as a multiplicative group. -/
abbrev Row (m : ℕ) (B : Type*) [Ring B] := Multiplicative (Fin m → B)

/-- The right action of invertible matrices on rows, through inverses. -/
def rowAct : (Matrix (Fin m) (Fin m) B)ˣ →* MulAut (Row m B) where
  toFun A :=
    { toFun := fun r => Multiplicative.ofAdd
        (Multiplicative.toAdd r ᵥ* ((A⁻¹ : (Matrix (Fin m) (Fin m) B)ˣ) : Matrix (Fin m) (Fin m) B))
      invFun := fun r => Multiplicative.ofAdd
        (Multiplicative.toAdd r ᵥ* (A : Matrix (Fin m) (Fin m) B))
      left_inv := fun r => by
        simp only [toAdd_ofAdd, Matrix.vecMul_vecMul, Units.inv_mul, Matrix.vecMul_one, ofAdd_toAdd]
      right_inv := fun r => by
        simp only [toAdd_ofAdd, Matrix.vecMul_vecMul, Units.mul_inv, Matrix.vecMul_one, ofAdd_toAdd]
      map_mul' := fun r r' => by
        simp only [toAdd_mul, Matrix.add_vecMul, ofAdd_add] }
  map_one' := by
    ext r
    simp
  map_mul' A A' := by
    ext r
    simp only [MulEquiv.coe_mk, Equiv.coe_fn_mk, MulAut.mul_apply, toAdd_ofAdd,
      Matrix.vecMul_vecMul, mul_inv_rev, Units.val_mul]

theorem rowAct_apply (A : (Matrix (Fin m) (Fin m) B)ˣ) (r : Row m B) :
    Multiplicative.toAdd (rowAct A r) =
      Multiplicative.toAdd r ᵥ* ((A⁻¹ : (Matrix (Fin m) (Fin m) B)ˣ) : Matrix (Fin m) (Fin m) B) :=
  rfl

/-- The action of a padded matrix on columns. -/
theorem pad_mulVec (A : (Matrix (Fin m) (Fin m) B)ˣ) (x : Fin (m + 1) → B) :
    ((Kernel.padUnitsHom A : (Matrix (Fin (m + 1)) (Fin (m + 1)) B)ˣ) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) B) *ᵥ x =
      Fin.lastCases (x (Fin.last m))
        (fun a => ((A : Matrix (Fin m) (Fin m) B) *ᵥ fun b => x b.castSucc) a) := by
  funext y
  induction y using Fin.lastCases with
  | last =>
    simp only [Fin.lastCases_last, Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, pad_apply,
      coordinateEquiv_symm_last, coordinateEquiv_symm_castSucc, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, zero_mul, Finset.sum_const_zero, zero_add,
      Matrix.one_apply_eq, one_mul]
  | cast a =>
    simp only [Fin.lastCases_castSucc, Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, pad_apply,
      coordinateEquiv_symm_last, coordinateEquiv_symm_castSucc, Matrix.fromBlocks_apply₁₁,
      Matrix.fromBlocks_apply₁₂, Matrix.zero_apply, zero_mul, add_zero]

/-- The row strip with last row `r`. -/
def rowMat (r : Fin m → B) : (Matrix (Fin (m + 1)) (Fin (m + 1)) B)ˣ :=
  rowProd r (List.finRange m)

theorem rowMat_mulVec (r : Fin m → B) (x : Fin (m + 1) → B) :
    ((rowMat r : (Matrix (Fin (m + 1)) (Fin (m + 1)) B)ˣ) : Matrix (Fin (m + 1)) (Fin (m + 1)) B)
      *ᵥ x = fun a => if a = Fin.last m then x a + ∑ b, r b * x b.castSucc else x a := by
  rw [rowMat, rowProd_mulVec]
  funext a
  rw [Fin.sum_univ_def]

/-- Units of matrices are equal when they act equally on columns. -/
theorem units_ext_mulVec {n : ℕ} {g h : (Matrix (Fin n) (Fin n) B)ˣ}
    (H : ∀ x : Fin n → B, (g : Matrix (Fin n) (Fin n) B) *ᵥ x = (h : Matrix (Fin n) (Fin n) B) *ᵥ x) :
    g = h := by
  apply Units.ext
  ext i j
  have := congrFun (H (Pi.single j 1)) i
  rwa [Matrix.mulVec_single_one, Matrix.mulVec_single_one] at this

theorem rowMat_add (r r' : Fin m → B) : rowMat (r + r') = rowMat r * rowMat r' := by
  apply units_ext_mulVec
  intro x
  rw [Units.val_mul, ← Matrix.mulVec_mulVec, rowMat_mulVec, rowMat_mulVec, rowMat_mulVec]
  funext a
  by_cases ha : a = Fin.last m
  · subst ha
    simp only [↓reduceIte, (Fin.castSucc_lt_last _).ne, Pi.add_apply, add_mul,
      Finset.sum_add_distrib]
    abel
  · simp [ha]

theorem rowMat_zero : rowMat (0 : Fin m → B) = 1 := by
  apply units_ext_mulVec
  intro x
  rw [rowMat_mulVec, Units.val_one, Matrix.one_mulVec]
  funext a
  simp

/-- Rows as a homomorphism. -/
def rowMatHom : Row m B →* (Matrix (Fin (m + 1)) (Fin (m + 1)) B)ˣ where
  toFun r := rowMat (Multiplicative.toAdd r)
  map_one' := rowMat_zero
  map_mul' _ _ := rowMat_add _ _

theorem pad_rowMat (A : (Matrix (Fin m) (Fin m) B)ˣ) (r : Fin m → B) :
    Kernel.padUnitsHom A * rowMat r * (Kernel.padUnitsHom A)⁻¹ =
      rowMat (r ᵥ* ((A⁻¹ : (Matrix (Fin m) (Fin m) B)ˣ) : Matrix (Fin m) (Fin m) B)) := by
  apply units_ext_mulVec
  intro x
  rw [← map_inv, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    pad_mulVec, rowMat_mulVec, pad_mulVec, rowMat_mulVec]
  funext y
  induction y using Fin.lastCases with
  | last =>
    simp only [Fin.lastCases_last, ↓reduceIte, Fin.lastCases_castSucc, castSucc_ne_last']
    congr 1
    exact Matrix.dotProduct_mulVec r _ _
  | cast a =>
    simp only [Fin.lastCases_castSucc, castSucc_ne_last', ↓reduceIte]
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]

/-- The semidirect product of rows and GL_m embedded in GL_{m+1}. -/
def ι : Row m B ⋊[rowAct] (Matrix (Fin m) (Fin m) B)ˣ →* (Matrix (Fin (m + 1)) (Fin (m + 1)) B)ˣ :=
  SemidirectProduct.lift rowMatHom Kernel.padUnitsHom (fun A => by
    refine MonoidHom.ext fun r => ?_
    show rowMat (Multiplicative.toAdd (rowAct A r)) =
      Kernel.padUnitsHom A * rowMat (Multiplicative.toAdd r) * (Kernel.padUnitsHom A)⁻¹
    rw [rowAct_apply]
    exact (pad_rowMat A (Multiplicative.toAdd r)).symm)

theorem ι_inl (r : Row m B) : ι (SemidirectProduct.inl r) = rowMat (Multiplicative.toAdd r) :=
  SemidirectProduct.lift_inl _ _ _ _

theorem ι_inr (A : (Matrix (Fin m) (Fin m) B)ˣ) :
    ι (SemidirectProduct.inr A) = Kernel.padUnitsHom A :=
  SemidirectProduct.lift_inr _ _ _ _

theorem rowMat_last (r : Fin m → B) :
    ((rowMat r : (Matrix (Fin (m + 1)) (Fin (m + 1)) B)ˣ) : Matrix (Fin (m + 1)) (Fin (m + 1)) B)
      *ᵥ Pi.single (Fin.last m) 1 = Pi.single (Fin.last m) 1 := by
  rw [rowMat_mulVec]
  funext a
  by_cases ha : a = Fin.last m
  · subst ha
    simp
  · simp [ha]

theorem pad_last (A : (Matrix (Fin m) (Fin m) B)ˣ) :
    ((Kernel.padUnitsHom A : (Matrix (Fin (m + 1)) (Fin (m + 1)) B)ˣ) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) B) *ᵥ Pi.single (Fin.last m) 1 =
      Pi.single (Fin.last m) 1 := by
  rw [pad_mulVec]
  funext y
  induction y using Fin.lastCases with
  | last => simp
  | cast a =>
    simp only [Fin.lastCases_castSucc, Pi.single_apply, castSucc_ne_last', ↓reduceIte]
    rw [show (fun b : Fin m => (0 : B)) = 0 from rfl, Matrix.mulVec_zero]
    rfl

/-- The image of `ι` fixes the last standard column. -/
theorem ι_last (x : Row m B ⋊[rowAct] (Matrix (Fin m) (Fin m) B)ˣ) :
    ((ι x : (Matrix (Fin (m + 1)) (Fin (m + 1)) B)ˣ) : Matrix (Fin (m + 1)) (Fin (m + 1)) B) *ᵥ
      Pi.single (Fin.last m) 1 = Pi.single (Fin.last m) 1 := by
  rw [← SemidirectProduct.inl_left_mul_inr_right x, map_mul, ι_inl, ι_inr, Units.val_mul,
    ← Matrix.mulVec_mulVec, pad_last, rowMat_last]

theorem ι_injective : Function.Injective (ι (m := m) (B := B)) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  rw [← SemidirectProduct.inl_left_mul_inr_right x, map_mul, ι_inl, ι_inr] at hx
  have hA : x.right = 1 := by
    apply Units.ext
    ext a b
    have h1 := congrArg (fun g : (Matrix (Fin (m + 1)) (Fin (m + 1)) B)ˣ =>
      ((g : Matrix (Fin (m + 1)) (Fin (m + 1)) B) *ᵥ Pi.single b.castSucc 1) a.castSucc) hx
    simp only [Units.val_mul, ← Matrix.mulVec_mulVec, rowMat_mulVec, castSucc_ne_last',
      ↓reduceIte, pad_mulVec, Fin.lastCases_castSucc, Units.val_one, Matrix.one_mulVec] at h1
    have e : (fun c : Fin m => (Pi.single b.castSucc (1 : B) : Fin (m + 1) → B) c.castSucc) =
        Pi.single b 1 := by
      funext c
      by_cases hc : c = b
      · subst hc
        simp
      · simp [hc, (Fin.castSucc_injective m).ne hc]
    rw [e, Matrix.mulVec_single_one] at h1
    rw [Units.val_one, Matrix.one_apply]
    by_cases hab : a = b
    · subst hab
      simpa using h1
    · simpa [hab, (Fin.castSucc_injective m).ne hab] using h1
  have hr : Multiplicative.toAdd x.left = 0 := by
    rw [hA, map_one, mul_one] at hx
    funext b
    have h1 := congrArg (fun g : (Matrix (Fin (m + 1)) (Fin (m + 1)) B)ˣ =>
      ((g : Matrix (Fin (m + 1)) (Fin (m + 1)) B) *ᵥ Pi.single b.castSucc 1) (Fin.last m)) hx
    simp only [rowMat_mulVec, ↓reduceIte, Units.val_one, Matrix.one_mulVec] at h1
    simpa [Pi.single_apply, castSucc_ne_last', (Fin.castSucc_injective m).eq_iff] using h1
  have : x = 1 := SemidirectProduct.ext (by
    rw [SemidirectProduct.one_left]
    exact hr) (by rw [SemidirectProduct.one_right]; exact hA)
  rw [this]
  exact Subgroup.one_mem _

/-- Every matrix fixing the last standard column is in the image of `ι`. -/
theorem exists_ι (p : (Matrix (Fin (m + 1)) (Fin (m + 1)) B)ˣ)
    (hp : (p : Matrix (Fin (m + 1)) (Fin (m + 1)) B) *ᵥ Pi.single (Fin.last m) 1 =
      Pi.single (Fin.last m) 1) : ∃ x, ι x = p := by
  set r : Fin m → B := fun b => (p : Matrix (Fin (m + 1)) (Fin (m + 1)) B) (Fin.last m) b.castSucc
    with hr
  set p' := p * rowMat (-r) with hp'
  have hll : (p : Matrix (Fin (m + 1)) (Fin (m + 1)) B) (Fin.last m) (Fin.last m) = 1 := by
    have := congrFun hp (Fin.last m)
    rwa [Matrix.mulVec_single_one, Pi.single_eq_same] at this
  have hcol : ∀ y, (p' : Matrix (Fin (m + 1)) (Fin (m + 1)) B) y (Fin.last m) =
      if y = Fin.last m then 1 else 0 := by
    intro y
    have := congrFun (show (p' : Matrix (Fin (m + 1)) (Fin (m + 1)) B) *ᵥ
        Pi.single (Fin.last m) 1 = Pi.single (Fin.last m) 1 by
      rw [hp', Units.val_mul, ← Matrix.mulVec_mulVec, rowMat_last, hp]) y
    rw [Matrix.mulVec_single_one] at this
    change (p' : Matrix (Fin (m + 1)) (Fin (m + 1)) B).col (Fin.last m) y = _
    rw [this]
    by_cases hy : y = Fin.last m
    · subst hy
      simp
    · simp [hy]
  have hrow : ∀ b : Fin m, (p' : Matrix (Fin (m + 1)) (Fin (m + 1)) B) (Fin.last m)
      b.castSucc = 0 := by
    intro b
    have h1 := congrFun (show (p' : Matrix (Fin (m + 1)) (Fin (m + 1)) B) *ᵥ
        Pi.single b.castSucc 1 = (p : Matrix (Fin (m + 1)) (Fin (m + 1)) B) *ᵥ
          ((rowMat (-r) : (Matrix (Fin (m + 1)) (Fin (m + 1)) B)ˣ) *ᵥ Pi.single b.castSucc 1) by
      rw [hp', Units.val_mul, ← Matrix.mulVec_mulVec]) (Fin.last m)
    rw [Matrix.mulVec_single_one, rowMat_mulVec] at h1
    change (p' : Matrix (Fin (m + 1)) (Fin (m + 1)) B).col b.castSucc (Fin.last m) = 0
    rw [h1]
    have e : (fun a : Fin (m + 1) => if a = Fin.last m then
        (Pi.single b.castSucc (1 : B) : Fin (m + 1) → B) a +
          ∑ c, (-r) c * (Pi.single b.castSucc (1 : B) : Fin (m + 1) → B) c.castSucc
        else (Pi.single b.castSucc (1 : B) : Fin (m + 1) → B) a) =
        Pi.single b.castSucc 1 + Pi.single (Fin.last m) (-r b) := by
      funext a
      by_cases ha : a = Fin.last m
      · subst ha
        simp [Pi.single_apply, (Fin.castSucc_injective m).eq_iff]
      · simp [ha, Pi.single_apply]
    rw [e, Matrix.mulVec_add, Matrix.mulVec_single_one, Matrix.mulVec_single, Pi.add_apply]
    simp [Matrix.col, hll, hr]
  obtain ⟨A, hA⟩ := eq_pad p' hcol hrow
  refine ⟨SemidirectProduct.inl (Multiplicative.ofAdd
    (r ᵥ* ((A⁻¹ : (Matrix (Fin m) (Fin m) B)ˣ) : Matrix (Fin m) (Fin m) B))) *
      SemidirectProduct.inr A, ?_⟩
  rw [map_mul, ι_inl, ι_inr, toAdd_ofAdd, ← pad_rowMat, inv_mul_cancel_right, ← hA,
    hp', mul_assoc, ← rowMat_add, neg_add_cancel, rowMat_zero, mul_one]

end GLPres
end AllPrimeGroups
