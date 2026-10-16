import AllPrimeGroups.NilMatrixLift
import AllPrimeGroups.FieldFrameCompletion

/-! Completing several reduced independent columns at once over a split matrix-nil extension.

First complete the reductions over the field, then replace the designated columns of its
coefficient lift by the original columns. The reduction stays invertible, so nil-kernel unit
reflection makes the whole matrix invertible. One unused diagonal coordinate makes it
elementary without changing any designated column. -/

namespace AllPrimeGroups
namespace Frames
noncomputable section
open Matrix GLPres LocalGL

variable {B K : Type*} [Ring B] [Field K]
variable (ε : B →+* K) (σ : K →+* B) (hs : ε.comp σ = RingHom.id K)
variable {n l : ℕ}
variable (hnil : ∀ A : Matrix (Fin n) (Fin n) B, ε.mapMatrix A = 0 → IsNilpotent A)

include σ hs hnil in
theorem exists_split_matrix_columns (f : Fin l → Fin n) (hf : Function.Injective f)
    (v : Fin l → Col n B) (hv : LinearIndependent K (fun j => red ε (v j))) :
    ∃ A : (Matrix (Fin n) (Fin n) B)ˣ, ∀ j, A.val *ᵥ Pi.single (f j) 1 = v j := by
  classical
  obtain ⟨M, hM⟩ := exists_field_matrix_columns f hf (fun j => red ε (v j)) hv
  let c : Fin n → Col n B := Function.extend f v (fun j i => σ (M.val i j))
  let A : Matrix (Fin n) (Fin n) B := fun i j => c j i
  have hcol (j : Fin l) : A *ᵥ Pi.single (f j) 1 = v j := by
    funext i
    rw [Matrix.mulVec_single_one, Matrix.col_apply]
    exact congrFun (hf.extend_apply v (fun j i => σ (M.val i j)) j) i
  have hεA : ε.mapMatrix A = M.val := by
    ext i j
    change ε (Function.extend f v (fun j i => σ (M.val i j)) j i) = M.val i j
    by_cases hj : ∃ k, f k = j
    · obtain ⟨k, rfl⟩ := hj
      have hc := congrArg ε (congrFun (hf.extend_apply v (fun j i => σ (M.val i j)) k) i)
      have h := congrFun (hM k) i
      have h' : ε (v k i) = M.val i (f k) := by
        simpa only [Matrix.mulVec_single_one, Matrix.col_apply, red] using h.symm
      exact hc.trans h'
    · have hc := congrArg ε (congrFun
        (Function.extend_apply' v (fun j i => σ (M.val i j)) j hj) i)
      exact hc.trans (DFunLike.congr_fun hs _)
  have hA : IsUnit A := (MatrixLifting.isUnit_iff_matrix_reduction ε σ hs hnil A).mpr
    (hεA.symm ▸ M.isUnit)
  obtain ⟨U, hU⟩ := hA
  exact ⟨U, fun j => hU.symm ▸ hcol j⟩

variable (hunit : ∀ b : B, ε b ≠ 0 → IsUnit b)

include σ hs hnil hunit in
theorem exists_split_elementary_columns (f : Fin l → Fin n) (hf : Function.Injective f)
    (i₀ : Fin n) (hi₀ : ∀ j, f j ≠ i₀) (v : Fin l → Col n B)
    (hv : LinearIndependent K (fun j => red ε (v j))) :
    ∃ A : K1.E n B, ∀ j, A.val.val *ᵥ Pi.single (f j) 1 = v j := by
  obtain ⟨M, hM⟩ := exists_split_matrix_columns ε σ hs hnil f hf v hv
  obtain ⟨u, hu⟩ := K1.exists_mul_d_mem_E ε hunit i₀ M
  refine ⟨⟨M * d i₀ u, hu⟩, fun j => ?_⟩
  change (M * d i₀ u).val *ᵥ Pi.single (f j) 1 = v j
  rw [Units.val_mul, ← Matrix.mulVec_mulVec, coe_d, Matrix.diagonal_mulVec_single]
  simp only [Function.update_of_ne (hi₀ j), Pi.one_apply, one_mul]
  exact hM j

end
end Frames
end AllPrimeGroups
