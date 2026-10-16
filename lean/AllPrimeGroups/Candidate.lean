import AllPrimeGroups.FiniteStage
import AllPrimeGroups.CongruencePGroup
import Mathlib.LinearAlgebra.Matrix.CharP

/-! A candidate with a finite quotient defined by the stable stage image.
This is a concrete subgroup; finite presentation, p-torsion in its Steinberg
kernel, and residual finiteness are not asserted without their remaining proofs. -/

namespace AllPrimeGroups
noncomputable section

variable {R S : Type*} [Ring R] [Ring S]

abbrev CandidateSubgroup (n : ℕ) (ε : R →+* S) : Subgroup (Steinberg n R) :=
  (Stable.detector n ε).ker

namespace Candidate

variable (n : ℕ) (ε : R →+* S)

theorem finiteIndex [Finite S] (hn : 3 ≤ n) : (CandidateSubgroup n ε).FiniteIndex :=
  Stable.detector_kernel_finiteIndex n hn ε

/-- Infinite coefficients and a finite augmentation quotient make this SAME candidate infinite. -/
theorem infinite [Infinite R] [Finite S] (hn : 3 ≤ n) : Infinite (CandidateSubgroup n ε) := by
  let p : Root n := ⟨⟨0, by omega⟩, ⟨1, by omega⟩,
    fun h => (by decide : (0 : ℕ) ≠ 1) (congrArg Fin.val h)⟩
  let : Infinite (Steinberg n R) := Elementary.steinberg_infinite p
  by_contra h
  have hf : Finite (CandidateSubgroup n ε) := not_infinite_iff_finite.mp h
  have hG : Finite (Steinberg n R) :=
    (Subgroup.finite_iff_finite_and_finiteIndex (CandidateSubgroup n ε)).mpr
      ⟨hf, finiteIndex n ε hn⟩
  exact not_finite (Steinberg n R)

theorem map_elementary (p : Root n) (a : R) :
    Units.map ε.mapMatrix.toMonoidHom (Elementary.e p a) = Elementary.e p (ε a) := by
  apply Units.ext
  ext i j
  simp [Elementary.coe_e, RingHom.mapMatrix_apply, Matrix.add_apply,
    Matrix.one_apply, Matrix.single_apply]
  split_ifs <;> simp

theorem representation_natural :
    (Units.map ε.mapMatrix.toMonoidHom).comp (Elementary.representation (n := n)) =
      (Elementary.representation (n := n)).comp (Steinberg.map ε) := by
  apply Steinberg.hom_ext
  intro p a
  simp only [MonoidHom.comp_apply, Elementary.representation_x, Steinberg.map_x,
    map_elementary]

/-- The candidate maps into the matrix congruence subgroup, even without
knowing that St_n(S) embeds into its stable group. -/
def matrixRepresentation : CandidateSubgroup n ε →*
    (Units.map (ε.mapMatrix (m := Fin n)).toMonoidHom).ker where
  toFun g := ⟨Elementary.representation g.val, by
    have hdet : Stable.detector n ε g.val = 1 := g.property
    have hs : Stable.of S n (Steinberg.map ε g.val) = 1 := congrArg Subtype.val hdet
    have hm := Stable.finite_matrix_kernel S n (Steinberg.map ε g.val) (by rw [hs, map_one])
    have he := DFunLike.congr_fun (representation_natural n ε) g.val
    exact MonoidHom.mem_ker.mpr (by simpa only [MonoidHom.comp_apply, hm] using he)⟩
  map_one' := Subtype.ext (map_one Elementary.representation)
  map_mul' g h := Subtype.ext (map_mul Elementary.representation g.val h.val)

abbrev MatrixImage : Subgroup (Matrix (Fin n) (Fin n) R)ˣ :=
  ((Elementary.representation (n := n) (R := R)).domRestrict (CandidateSubgroup n ε)).range

/-- This proves p-power order for the matrix IMAGE, retaining the matrix-nil
hypothesis explicitly. The extra Steinberg kernel is still a separate obligation. -/
theorem matrixImage_isPGroup {p : ℕ} (hp : p.Prime) [CharP R p] (hn : 3 ≤ n)
    (hnil : ∀ A : Matrix (Fin n) (Fin n) R, ε.mapMatrix A = 0 → IsNilpotent A) :
    IsPGroup p (MatrixImage n ε) := by
  let : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hU := units_congruence_isPGroup hp (ε.mapMatrix (m := Fin n)) hnil
  have hr : MatrixImage n ε ≤ (Units.map ε.mapMatrix.toMonoidHom).ker := by
    rintro u ⟨g, rfl⟩
    exact (matrixRepresentation n ε g).property
  exact hU.of_injective (Subgroup.inclusion hr) (Subgroup.inclusion_injective hr)

end Candidate
end
end AllPrimeGroups
