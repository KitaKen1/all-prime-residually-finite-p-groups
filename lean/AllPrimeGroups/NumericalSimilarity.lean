/-
Stable invariance of numerical evaluation under a numerical change of basis, adapted from
OpenAI PeriodicGroups/Steinberg/MatrixUnits.lean (commit pinned in upstream/provenance.json;
Apache-2.0, see upstream/OpenAI-LICENSE).
Upstream works over the two-element field, where every invertible numerical matrix lifts to
the Steinberg group. Over `ZMod ℓ` the lift exists for determinant one, so the statements
here carry that hypothesis.
-/
import AllPrimeGroups.BandFactorization
import AllPrimeGroups.SpecialLinearRealization

namespace AllPrimeGroups
universe u v w
variable {ℓ : ℕ} [Fact ℓ.Prime]
namespace Kernel
noncomputable section
open Classical
variable {n N : ℕ} {R : Type*} [Ring R] [Algebra (ZMod ℓ) R]

def numericUnits (P : (Matrix (Fin N) (Fin N) (ZMod ℓ))ˣ) : (Matrix (Fin N) (Fin N) R)ˣ :=
  Units.map (algebraMap (ZMod ℓ) R).mapMatrix.toMonoidHom P

omit [Fact ℓ.Prime] [Algebra (ZMod ℓ) R] in
lemma bigBasisUnits_entry {S : Type*} [Ring S] (P : (Matrix (Fin N) (Fin N) S)ˣ)
    (i j : Fin n) (s t : Fin N) :
    (bigBasisUnits P).val (blockIndex i s) (blockIndex j t)=if i=j then P.val s t else 0 := by
  change flattenRing (Matrix.diagonal (fun _ : Fin n=>P.val)) (blockIndex i s) (blockIndex j t)=_
  simp only [flattenRing,RingEquiv.trans_apply,Matrix.coe_reindexRingEquiv,Matrix.reindex_apply,
    Matrix.submatrix_apply,blockIndex,Equiv.symm_apply_apply,Matrix.compRingEquiv_apply,Matrix.comp_apply]
  by_cases hij : i=j <;> simp [Matrix.diagonal,hij]

/-- The block-diagonal copies of a matrix have the corresponding power as determinant. -/
lemma bigBasisUnits_det {S : Type*} [CommRing S] (P : (Matrix (Fin N) (Fin N) S)ˣ) :
    (bigBasisUnits (n:=n) P).val.det=P.val.det^n := by
  let e : Fin N × Fin n ≃ Fin (n*N) := (Equiv.prodComm (Fin N) (Fin n)).trans finProdFinEquiv
  have h : (bigBasisUnits (n:=n) P).val=
      Matrix.reindex e e (Matrix.blockDiagonal (fun _ : Fin n=>P.val)) := by
    apply Matrix.ext
    intro u v
    obtain ⟨⟨i,s⟩,rfl⟩ := finProdFinEquiv.surjective u
    obtain ⟨⟨j,t⟩,rfl⟩ := finProdFinEquiv.surjective v
    change (bigBasisUnits P).val (blockIndex i s) (blockIndex j t)=_
    rw [bigBasisUnits_entry]
    simp [e,Matrix.blockDiagonal_apply]
  rw [h,Matrix.det_reindex_self,Matrix.det_blockDiagonal,Finset.prod_const,Finset.card_univ,
    Fintype.card_fin]

lemma bigBasisUnits_map (P : (Matrix (Fin N) (Fin N) (ZMod ℓ))ˣ) :
    Units.map (algebraMap (ZMod ℓ) R).mapMatrix.toMonoidHom (bigBasisUnits (n:=n) P)=
      bigBasisUnits (numericUnits (R:=R) P) := by
  apply Units.ext
  apply Matrix.ext
  intro u v
  obtain ⟨⟨i,s⟩,rfl⟩ := finProdFinEquiv.surjective u
  obtain ⟨⟨j,t⟩,rfl⟩ := finProdFinEquiv.surjective v
  change algebraMap (ZMod ℓ) R ((bigBasisUnits P).val (blockIndex i s) (blockIndex j t))=
    (bigBasisUnits (numericUnits (R:=R) P)).val (blockIndex i s) (blockIndex j t)
  rw [bigBasisUnits_entry,bigBasisUnits_entry]
  split_ifs <;> simp [numericUnits]

/-- A numerical matrix of determinant one, repeated in every block, is the elementary image
of an element of the Steinberg group. -/
lemma numerical_big_lift (P : (Matrix (Fin N) (Fin N) (ZMod ℓ))ˣ) (hP : P.val.det=1) :
    ∃b : Steinberg (n*N) R,Elementary.representation b=bigBasisUnits (numericUnits (R:=R) P) := by
  have hdet : (bigBasisUnits (n:=n) P).val.det=1 := by rw [bigBasisUnits_det,hP,one_pow]
  obtain ⟨b,hb'⟩ := Elementary.exists_representation_eq (bigBasisUnits (n:=n) P) hdet
  refine ⟨Steinberg.map (algebraMap (ZMod ℓ) R) b,?_⟩
  have he := DFunLike.congr_fun (Elementary.representation_map (n:=n*N) (algebraMap (ZMod ℓ) R)) b
  change Elementary.representation (Steinberg.map (algebraMap (ZMod ℓ) R) b)=_
  simpa only [MonoidHom.comp_apply,hb',bigBasisUnits_map] using he

lemma numeric_conj_scalar (P : (Matrix (Fin N) (Fin N) (ZMod ℓ))ˣ) (a : R) :
    coefficientConj (numericUnits (R:=R) P) (Matrix.scalar (Fin N) a)=Matrix.scalar (Fin N) a := by
  change (numericUnits (R:=R) P).val*Matrix.scalar (Fin N) a*(numericUnits (R:=R) P).inv=_
  have hc := (numeric_scalar_commute (R:=R) P.val a).eq
  change Matrix.scalar (Fin N) a*(numericUnits (R:=R) P).val=(numericUnits (R:=R) P).val*Matrix.scalar (Fin N) a at hc
  rw [←hc,mul_assoc,Units.val_inv,mul_one]

lemma numeric_conj_matrix (P : (Matrix (Fin N) (Fin N) (ZMod ℓ))ˣ)
    (T : Matrix (Fin N) (Fin N) (ZMod ℓ)) :
    coefficientConj (numericUnits (R:=R) P) (numericMatrix (R:=R) T)=numericMatrix (R:=R) (P.val*T*P.inv) := by
  change (algebraMap (ZMod ℓ) R).mapMatrix P.val*(algebraMap (ZMod ℓ) R).mapMatrix T*
    (algebraMap (ZMod ℓ) R).mapMatrix P.inv=(algebraMap (ZMod ℓ) R).mapMatrix (P.val*T*P.inv)
  simp only [map_mul]

lemma matrixEval_conjugacy (P : (Matrix (Fin N) (Fin N) (ZMod ℓ))ˣ)
    (T : Matrix (Fin N) (Fin N) (ZMod ℓ)) :
    (coefficientConj (numericUnits (R:=R) P)).comp (matrixEvalRingHom T)=
      matrixEvalRingHom (R:=R) (P.val*T*P.inv) := by
  apply Polynomial.ringHom_ext
  · intro a
    change coefficientConj (numericUnits (R:=R) P) (Polynomial.eval₂ _ _ (Polynomial.C a))=
      Polynomial.eval₂ _ _ (Polynomial.C a)
    rw [Polynomial.eval₂_C,Polynomial.eval₂_C]
    exact numeric_conj_scalar P a
  · change coefficientConj (numericUnits (R:=R) P) (Polynomial.eval₂ _ _ Polynomial.X)=
      Polynomial.eval₂ _ _ Polynomial.X
    rw [Polynomial.eval₂_X,Polynomial.eval₂_X]
    exact numeric_conj_matrix P T

/-- Conjugate numerical matrices give the same stable evaluation of a kernel element. -/
theorem stable_numerical_similarity (hn : 3 ≤ n)
    (P : (Matrix (Fin N) (Fin N) (ZMod ℓ))ˣ) (hP : P.val.det=1)
    (T : Matrix (Fin N) (Fin N) (ZMod ℓ))
    (u : Steinberg n (Polynomial R)) (hu : Elementary.representation u=1) :
    padSteinberg (matrixSteinbergEval T u)=padSteinberg (matrixSteinbergEval (P.val*T*P.inv) u) := by
  obtain ⟨b,hb⟩ := numerical_big_lift (n:=n) (R:=R) P hP
  have he := stable_basis_change hn (numericUnits (R:=R) P) b hb (Steinberg.map (matrixEvalRingHom T) u)
  rw [Steinberg.map_map,matrixEval_conjugacy] at he
  have hz := stabilized_kernel_central (matrixSteinbergEval T u) (matrixSteinbergEval_kernel T u hu)
  have hc : Commute (padSteinberg b) (padSteinberg (matrixSteinbergEval T u)) :=
    Subgroup.mem_center_iff.mp hz _
  change padSteinberg (b*matrixSteinbergEval T u*b⁻¹)=padSteinberg (matrixSteinbergEval (P.val*T*P.inv) u) at he
  simpa only [map_mul,map_inv,CommutatorCalculus.conj_of_commute hc] using he
end
end Kernel
end AllPrimeGroups
