/-
Generic matrix embeddings and block stabilizers extracted from the pinned OpenAI source:
PeriodicGroups/Matrices/ElementaryGenerators.lean,
PeriodicGroups/Presentation/FinitePresentation.lean, and
PeriodicGroups/Presentation/MatrixStabilizers.lean.
Apache-2.0; see upstream/OpenAI-LICENSE and upstream/provenance.json.
The source proofs are retained; imports and namespace are adapted to avoid importing all Mathlib.
-/
import AllPrimeGroups.GLSection
import Mathlib.LinearAlgebra.Matrix.Action

namespace AllPrimeGroups.MatrixGeometry
noncomputable section
open Classical Matrix
variable {R ι κ : Type*} [Ring R] [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

def elementary (i j : ι) (hij : i ≠ j) (a : R) : (Matrix ι ι R)ˣ where
  val := 1 + Matrix.single i j a
  inv := 1 + Matrix.single i j (-a)
  val_inv := by simp [add_mul, mul_add, hij.symm, ← Matrix.single_neg, add_assoc]
  inv_val := by simp [add_mul, mul_add, hij.symm, ← Matrix.single_neg, add_assoc]

@[simp] lemma elementary_val (i j : ι) (hij : i ≠ j) (a : R) :
    (elementary i j hij a : Matrix ι ι R) = 1 + Matrix.single i j a := rfl

def diagonal (d : ι → Rˣ) : (Matrix ι ι R)ˣ where
  val := Matrix.diagonal (fun i => (d i).val)
  inv := Matrix.diagonal (fun i => (d i).inv)
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal]
    simp
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal]
    simp

@[simp] lemma diagonal_val (d : ι → Rˣ) :
    (diagonal d : Matrix ι ι R) = Matrix.diagonal (fun i => (d i).val) := rfl

@[simp] lemma diagonal_one : diagonal (fun _ : ι => (1 : Rˣ)) = 1 := by
  apply Units.ext
  simp

@[simp] lemma diagonal_mul (d e : ι → Rˣ) : diagonal (fun i => d i * e i) = diagonal d * diagonal e := by
  apply Units.ext
  simp

def singleDiagonal (i : ι) (u : Rˣ) : (Matrix ι ι R)ˣ :=
  diagonal (fun j => if j = i then u else 1)


def relabel (e : ι ≃ κ) : (Matrix ι ι R)ˣ →* (Matrix κ κ R)ˣ :=
  Units.map (Matrix.reindexRingEquiv R e).toMonoidHom

@[simp] lemma relabel_elementary (e : ι ≃ κ) (i j : ι) (hij : i ≠ j) (a : R) :
    relabel e (elementary i j hij a) = elementary (e i) (e j) (e.injective.ne hij) a := by
  apply Units.ext
  ext x y
  simp [relabel, Matrix.reindex_apply, Matrix.submatrix_apply,
    Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, Equiv.eq_symm_apply]

@[simp] lemma relabel_diagonal (e : ι ≃ κ) (d : ι → Rˣ) :
    relabel e (diagonal d) = diagonal (d ∘ e.symm) := by
  apply Units.ext
  simp [relabel, Matrix.reindex_apply, Matrix.submatrix_diagonal_equiv]

@[simp] lemma relabel_singleDiagonal (e : ι ≃ κ) (i : ι) (u : Rˣ) :
    relabel e (singleDiagonal i u) = singleDiagonal (e i) u := by
  rw [singleDiagonal, relabel_diagonal, singleDiagonal]
  congr 1
  funext j
  simp [Equiv.symm_apply_eq]


def blockInclusion : (Matrix ι ι R)ˣ →* (Matrix (ι ⊕ κ) (ι ⊕ κ) R)ˣ where
  toFun u :=
    { val := Matrix.fromBlocks u.val 0 0 1
      inv := Matrix.fromBlocks u.inv 0 0 1
      val_inv := by simp [Matrix.fromBlocks_multiply]
      inv_val := by simp [Matrix.fromBlocks_multiply] }
  map_one' := by apply Units.ext; simp
  map_mul' u v := by apply Units.ext; simp [Matrix.fromBlocks_multiply]

@[simp] lemma blockInclusion_val (u : (Matrix ι ι R)ˣ) :
    (blockInclusion (κ := κ) u : Matrix (ι ⊕ κ) (ι ⊕ κ) R) = Matrix.fromBlocks u.val 0 0 1 := rfl

@[simp] lemma blockInclusion_elementary (i j : ι) (hij : i ≠ j) (a : R) :
    blockInclusion (κ := κ) (elementary i j hij a) =
      elementary (Sum.inl i) (Sum.inl j) (Sum.inl_injective.ne hij) a := by
  apply Units.ext
  ext x y
  cases x <;> cases y <;>
    simp [Matrix.fromBlocks, Matrix.add_apply, Matrix.single_apply, Matrix.one_apply]

@[simp] lemma blockInclusion_diagonal (d : ι → Rˣ) :
    blockInclusion (κ := κ) (diagonal d) = diagonal (Sum.elim d (fun _ => 1)) := by
  apply Units.ext
  ext x y
  cases x <;> cases y <;> simp [Matrix.fromBlocks, Matrix.diagonal_apply, Matrix.one_apply]


def embeddingEquiv (e : ι ↪ κ) : ι ⊕ {k // k ∉ Set.range e} ≃ κ :=
  (Equiv.sumCongr (Equiv.ofInjective e e.injective) (Equiv.refl _)).trans
    (Equiv.Set.sumCompl (Set.range e))

omit [Fintype κ] [DecidableEq ι] in
@[simp] lemma embeddingEquiv_inl (e : ι ↪ κ) (i : ι) : embeddingEquiv e (Sum.inl i) = e i := rfl
omit [Fintype κ] [DecidableEq ι] in
@[simp] lemma embeddingEquiv_inr (e : ι ↪ κ) (i : {k // k ∉ Set.range e}) :
    embeddingEquiv e (Sum.inr i) = i.val := rfl

def embed (e : ι ↪ κ) : (Matrix ι ι R)ˣ →* (Matrix κ κ R)ˣ :=
  (relabel (embeddingEquiv e)).comp (blockInclusion (κ := {k // k ∉ Set.range e}))

@[simp] lemma embed_elementary (e : ι ↪ κ) (i j : ι) (h : i ≠ j) (a : R) :
    embed e (elementary i j h a) = elementary (e i) (e j) (e.injective.ne h) a := by
  simp only [embed,MonoidHom.comp_apply,blockInclusion_elementary,relabel_elementary,
    embeddingEquiv_inl]

lemma blockInclusion_singleDiagonal (i : ι) (u : Rˣ) :
    blockInclusion (κ := κ) (singleDiagonal i u) = singleDiagonal (Sum.inl i) u := by
  rw [singleDiagonal,blockInclusion_diagonal,singleDiagonal]
  congr 1
  funext j
  cases j <;> simp

@[simp] lemma embed_singleDiagonal (e : ι ↪ κ) (i : ι) (u : Rˣ) :
    embed e (singleDiagonal i u) = singleDiagonal (e i) u := by
  simp only [embed,MonoidHom.comp_apply,blockInclusion_singleDiagonal,relabel_singleDiagonal,
    embeddingEquiv_inl]

lemma embed_entry (e : ι ↪ κ) (U : (Matrix ι ι R)ˣ) (i j : ι) :
    (embed e U).val (e i) (e j) = U.val i j := by
  change (Matrix.fromBlocks U.val 0 0 (1 : Matrix {k // k ∉ Set.range e} _ R))
    ((embeddingEquiv e).symm (e i)) ((embeddingEquiv e).symm (e j)) = _
  rw [← embeddingEquiv_inl e i,← embeddingEquiv_inl e j,
    Equiv.symm_apply_apply,Equiv.symm_apply_apply]
  rfl

lemma embed_injective (e : ι ↪ κ) : Function.Injective (embed (R := R) e) := by
  intro U V hh
  apply Units.ext
  ext i j
  simpa only [embed_entry] using congrArg (fun B : (Matrix κ κ R)ˣ => B.val (e i) (e j)) hh

lemma embed_off_column (e : ι ↪ κ) (U : (Matrix ι ι R)ˣ) (j : κ) (hj : j ∉ Set.range e)
    (i : κ) : (embed e U).val i j = (1 : Matrix κ κ R) i j := by
  let j' : {k // k ∉ Set.range e} := ⟨j,hj⟩
  obtain ⟨i',rfl⟩ := (embeddingEquiv e).surjective i
  change (Matrix.fromBlocks U.val 0 0 (1 : Matrix {k // k ∉ Set.range e} _ R))
    ((embeddingEquiv e).symm (embeddingEquiv e i'))
    ((embeddingEquiv e).symm (embeddingEquiv e (Sum.inr j'))) =
      if embeddingEquiv e i' = embeddingEquiv e (Sum.inr j') then 1 else 0
  rw [Equiv.symm_apply_apply,Equiv.symm_apply_apply]
  rcases i' with i' | i'
  · change 0 = if _ then (1 : R) else 0
    exact (ite_eq_right ((embeddingEquiv e).injective.ne (Sum.inl_ne_inr))).symm
  · change (if i' = j' then (1 : R) else 0) = if _ then 1 else 0
    congr 1
    exact propext (((embeddingEquiv e).injective.eq_iff.trans Sum.inr_injective.eq_iff).symm)

lemma embed_off_row (e : ι ↪ κ) (U : (Matrix ι ι R)ˣ) (i : κ) (hi : i ∉ Set.range e)
    (j : κ) : (embed e U).val i j = (1 : Matrix κ κ R) i j := by
  let i' : {k // k ∉ Set.range e} := ⟨i,hi⟩
  obtain ⟨j',rfl⟩ := (embeddingEquiv e).surjective j
  change (Matrix.fromBlocks U.val 0 0 (1 : Matrix {k // k ∉ Set.range e} _ R))
    ((embeddingEquiv e).symm (embeddingEquiv e (Sum.inr i')))
    ((embeddingEquiv e).symm (embeddingEquiv e j')) =
      if embeddingEquiv e (Sum.inr i') = embeddingEquiv e j' then 1 else 0
  rw [Equiv.symm_apply_apply,Equiv.symm_apply_apply]
  rcases j' with j' | j'
  · change 0 = if _ then (1 : R) else 0
    exact (ite_eq_right ((embeddingEquiv e).injective.ne (Sum.inr_ne_inl))).symm
  · change (if i' = j' then (1 : R) else 0) = if _ then 1 else 0
    congr 1
    exact propext (((embeddingEquiv e).injective.eq_iff.trans Sum.inr_injective.eq_iff).symm)

def rectangleLower : (κ × ι → Multiplicative R) →* (Matrix (ι ⊕ κ) (ι ⊕ κ) R)ˣ where
  toFun A :=
    { val := Matrix.fromBlocks 1 0 (Matrix.of (fun i j => (A (i,j)).toAdd)) 1
      inv := Matrix.fromBlocks 1 0 (Matrix.of (fun i j => -(A (i,j)).toAdd)) 1
      val_inv := by
        rw [Matrix.fromBlocks_multiply]
        ext i j
        cases i <;> cases j <;> simp [Matrix.fromBlocks,Matrix.one_apply]
      inv_val := by
        rw [Matrix.fromBlocks_multiply]
        ext i j
        cases i <;> cases j <;> simp [Matrix.fromBlocks,Matrix.one_apply] }
  map_one' := by
    apply Units.ext
    ext i j
    cases i <;> cases j <;> simp [Matrix.fromBlocks,Matrix.one_apply]
  map_mul' A B := by
    apply Units.ext
    simp only [Units.val_mul,Matrix.fromBlocks_multiply,Matrix.mul_one,Matrix.one_mul,
      Matrix.mul_zero,Matrix.zero_mul,add_zero,zero_add]
    congr 1

@[simp] lemma rectangleLower_single (i : κ) (j : ι) (a : R) :
    rectangleLower (Pi.mulSingle (i,j) (Multiplicative.ofAdd a)) =
      elementary (Sum.inr i) (Sum.inl j) Sum.inr_ne_inl a := by
  apply Units.ext
  ext x y
  cases x <;> cases y <;>
    simp [rectangleLower,Pi.mulSingle,Function.update,Matrix.add_apply,
      Matrix.one_apply,Matrix.single_apply,Matrix.fromBlocks,eq_comm,and_comm]
  split_ifs <;> rfl

lemma rectangleLower_mem {P : Subgroup (Matrix (ι ⊕ κ) (ι ⊕ κ) R)ˣ}
    (hP : ∀i j a, elementary (Sum.inr i) (Sum.inl j) Sum.inr_ne_inl a ∈ P)
    (A : κ × ι → Multiplicative R) : rectangleLower A ∈ P := by
  change A ∈ P.comap rectangleLower
  apply Subgroup.pi_mem_of_mulSingle_mem
  rintro ⟨i,j⟩
  change rectangleLower (Pi.mulSingle (i,j) (A (i,j))) ∈ P
  change rectangleLower (Pi.mulSingle (i,j) (Multiplicative.ofAdd ((A (i,j)).toAdd))) ∈ P
  rw [rectangleLower_single]
  exact hP _ _ _

def rightFixer : Subgroup (Matrix (ι ⊕ κ) (ι ⊕ κ) R)ˣ :=
  ⨅ k : κ, MulAction.stabilizer (Matrix (ι ⊕ κ) (ι ⊕ κ) R)ˣ (Pi.single (Sum.inr k) (1 : R) : ι ⊕ κ → R)

lemma mem_rightFixer_iff (U : (Matrix (ι ⊕ κ) (ι ⊕ κ) R)ˣ) :
    U ∈ rightFixer ↔ ∀ i k, U.val i (Sum.inr k) = (1 : Matrix (ι ⊕ κ) (ι ⊕ κ) R) i (Sum.inr k) := by
  simp only [rightFixer,Subgroup.mem_iInf,MulAction.mem_stabilizer_iff]
  constructor
  · intro h i k
    have hh := congrFun (h k) i
    simpa [Units.smul_def,Matrix.mulVec_single_one,Matrix.col,Pi.single_apply,Matrix.one_apply,eq_comm] using hh
  · intro h k
    ext i
    have hh := h i k
    simpa [Units.smul_def,Matrix.mulVec_single_one,Matrix.col,Pi.single_apply,Matrix.one_apply,eq_comm] using hh

lemma rightFixer_shape (U : rightFixer (ι := ι) (κ := κ) (R := R)) :
    U.val.val = Matrix.fromBlocks (U.val.val.submatrix Sum.inl Sum.inl) 0
      (U.val.val.submatrix Sum.inr Sum.inl) 1 := by
  ext i j
  cases j with
  | inl j => cases i <;> rfl
  | inr j =>
    have hh := (mem_rightFixer_iff U.val).mp U.property i j
    cases i <;> simpa [Matrix.fromBlocks,Matrix.one_apply] using hh

def rightProjection : rightFixer (ι := ι) (κ := κ) (R := R) →* (Matrix ι ι R)ˣ where
  toFun U :=
    { val := U.val.val.submatrix Sum.inl Sum.inl
      inv := U.val.inv.submatrix Sum.inl Sum.inl
      val_inv := by
        have he : U.val.val * (U⁻¹).val.val = 1 := U.val.val_inv
        rw [rightFixer_shape U,rightFixer_shape U⁻¹,Matrix.fromBlocks_multiply] at he
        ext i j
        have hh := congrArg (fun A : Matrix (ι ⊕ κ) (ι ⊕ κ) R => A (Sum.inl i) (Sum.inl j)) he
        simpa [Matrix.fromBlocks,Matrix.one_apply] using hh
      inv_val := by
        have he : (U⁻¹).val.val * U.val.val = 1 := U.val.inv_val
        rw [rightFixer_shape U⁻¹,rightFixer_shape U,Matrix.fromBlocks_multiply] at he
        ext i j
        have hh := congrArg (fun A : Matrix (ι ⊕ κ) (ι ⊕ κ) R => A (Sum.inl i) (Sum.inl j)) he
        simpa [Matrix.fromBlocks,Matrix.one_apply] using hh }
  map_one' := by apply Units.ext; ext i j; simp [Matrix.one_apply]
  map_mul' U V := by
    apply Units.ext
    change (U.val.val*V.val.val).submatrix Sum.inl Sum.inl =
      U.val.val.submatrix Sum.inl Sum.inl * V.val.val.submatrix Sum.inl Sum.inl
    ext i j
    change (U.val.val*V.val.val) (Sum.inl i) (Sum.inl j) = _
    conv_lhs => rw [rightFixer_shape U,rightFixer_shape V,Matrix.fromBlocks_multiply]
    simp

lemma rightFixer_decomposition (U : rightFixer (ι := ι) (κ := κ) (R := R)) :
    U.val = blockInclusion (rightProjection U) *
      rectangleLower (fun p : κ × ι => Multiplicative.ofAdd (U.val.val (Sum.inr p.1) (Sum.inl p.2))) := by
  apply Units.ext
  rw [Units.val_mul,blockInclusion_val]
  change U.val.val = Matrix.fromBlocks _ 0 0 1 * Matrix.fromBlocks 1 0 _ 1
  rw [Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_one,Matrix.one_mul,Matrix.mul_zero,Matrix.zero_mul,add_zero,zero_add]
  exact rightFixer_shape U


end
end AllPrimeGroups.MatrixGeometry
