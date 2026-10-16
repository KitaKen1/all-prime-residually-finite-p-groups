/-
It imports the upstream modules through Steinberg/CoefficientQuotients, which must be built
first (`python3 scripts/build_upstream.py`).

Matrix nilpotence of the positive ideal of the word algebra over any commutative ring of
prime characteristic p (manuscript Theorems 17.4 and 18.1). Adapted from OpenAI's
PeriodicGroups/Steinberg/{PresentationModel,CoefficientQuotients}.lean (commit pinned in
upstream/provenance.json; Apache-2.0, see upstream/OpenAI-LICENSE), whose statements assume
characteristic two. The hierarchy, the cut reduction, and the automaton step are the
untouched upstream theorems; only the direct cancellation step and the stopping index change.
-/
import OAI.GroupTheory.PeriodicGroups.Steinberg.CoefficientQuotients
import AllPrimeGroups.PrimeCancellation

namespace AllPrimeGroups.PrimeMatrixNil
open OAI OAI.SourceBurnside OAI.SourceBurnside.SourceMachine
open OAI.SourceBurnside.FiniteTable
open Classical
open scoped BigOperators
noncomputable section

/-- The automaton dimension recurrence is linear in the initial dimension. -/
lemma dimension_scale (c d k : ℕ) (s : ℕ → ℕ) (n : ℕ) :
    HierarchyGrowth.dimension (c * d) k s n = c * HierarchyGrowth.dimension d k s n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [HierarchyGrowth.dimension, ih]; ring

section Tests
variable {D : ℕ} {hD : 2 ≤ D} (A : MachineHierarchy D hD)
variable {h : ℕ} (hh : A.threshold ≤ h) (K : Type*) [CommRing K] {p : ℕ} [CharP K p]

/-- Upstream `direct_step` with the characteristic-p bound (manuscript Lemma 17.1). -/
lemma direct_step (hp : 0 < p) {d b : ℕ} (hb : 100*b*((p-1)*d^2+3)<2^h) :
    A.ChunkVanish hh K d b := by
  intro ι Γ _ _ _ hid label hne hl W
  refine ⟨2*fragmentBound (2^h)+1,?_⟩
  apply PrimeCancellation.direct_vanish_finite hp (M := (p-1)*d^2)
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hid 2)) label hne hl
    (Codec.fields (A.height_pos hh)) Codec.eligibleFields (A.letters hh K)
  · exact Codec.letter_commute (A.threshold_four.trans hh)
  · exact Codec.letter_square (A.threshold_four.trans hh)
  · exact Codec.long_eligible_interval (A.threshold_four.trans hh)
  · exact hb

/-- Upstream `all_letter_tests` in characteristic p (manuscript Theorem 17.4). The stopping
index is taken for the initial dimension scaled by p, which absorbs the factor p - 1. -/
theorem all_letter_tests (hp : 0 < p) (hDbig : 10*(10000+1)*(10+1)<D) (d : ℕ) :
    A.LetterVanish hh K d := by
  let H := D*h
  let size : ℕ → ℕ := fun n=>Fintype.card (Codec.Raw (HierarchyGrowth.height H D n))
  let dim : ℕ → ℕ := HierarchyGrowth.dimension (max 1 d) 10 size
  have hH : 1 ≤ H := Nat.mul_pos (by omega) (A.height_pos hh)
  have hs (n : ℕ) : size n ≤ 2^(10000*HierarchyGrowth.height H D n) := by
    simp [size,Codec.Raw,Fintype.card_fin]
  have hsize (n : ℕ) : 1 ≤ size n := Fintype.card_pos
  have hdim (n : ℕ) : 1 ≤ dim n := by
    induction n with
    | zero => exact le_max_left _ _
    | succ n ih =>
      change 1 ≤ 10*(size n)^10*dim n
      have hs : 0 < (size n)^10 := Nat.pow_pos (hsize n)
      nlinarith
  have hlarge (n : ℕ) : A.threshold ≤ HierarchyGrowth.height H D n := by
    have hn : 1 ≤ D^n := Nat.one_le_pow n D (by omega)
    have hh' := A.next_large hh
    change A.threshold ≤ H*D^n
    exact hh'.trans (Nat.le_mul_of_pos_right H hn)
  obtain ⟨N,hN⟩ := HierarchyGrowth.stopping_index H D (p * max 1 d) 10 10000 size hH hDbig hs
  have hlast : A.ChunkVanish (hlarge N) K (dim N) 10 := by
    apply direct_step A (hlarge N) K hp
    have hd := hdim N
    rw [dimension_scale] at hN
    change 400*10*(p * dim N)^2 < 2^HierarchyGrowth.height H D N at hN
    have h1 : (p - 1) * (dim N)^2 ≤ (p * dim N)^2 := by
      rw [mul_pow]
      exact Nat.mul_le_mul_right _ ((Nat.sub_le p 1).trans (Nat.le_self_pow (by decide) p))
    have h2 : 1 ≤ (p * dim N)^2 := Nat.one_le_pow _ _ (Nat.mul_pos hp hd)
    omega
  have hstep (i : ℕ) (Hup : A.ChunkVanish (hlarge (i+1)) K (dim (i+1)) 10) :
      A.ChunkVanish (hlarge i) K (dim i) 10 := by
    apply A.automaton_step (hlarge i) K (by decide : 0<10)
    apply A.cut_step (hlarge i) K
    simpa only [HierarchyGrowth.height_succ,dim,HierarchyGrowth.dimension,size] using Hup
  have hfirst : A.ChunkVanish (hlarge 0) K (dim 0) 10 := by
    exact Nat.decreasingInduction (motive := fun i _ => A.ChunkVanish (hlarge i) K (dim i) 10)
      (fun i _ hi' => hstep i hi') hlast (Nat.zero_le N)
  have hlower : A.LetterVanish hh K (max 1 d) := by
    apply A.cut_step hh K
    simpa only [HierarchyGrowth.height,pow_zero,mul_one,dim,HierarchyGrowth.dimension,H]
      using hfirst
  intro ι _ _ hi W
  exact hlower ι (hi.trans (le_max_right _ _)) W

theorem all_chunk_tests (hp : 0 < p) (hDbig : 10*(10000+1)*(10+1)<D) (d b : ℕ) (hb : 0<b) :
    A.ChunkVanish hh K d b :=
  A.automaton_step hh K hb (all_letter_tests A hh K hp hDbig _)

end Tests

section Nilpotence
variable {D : ℕ} {hD : 2 ≤ D} (A : MachineHierarchy D hD)
variable {h : ℕ} (hh : A.threshold ≤ h) (K : Type) [CommRing K] {p : ℕ} [CharP K p]

/-- Upstream `word_matrix_sum_nilpotent` in characteristic p (manuscript Proposition 7.1
applied to the hierarchy). -/
theorem word_matrix_sum_nilpotent (hp : 0 < p) (hDbig : 10*(10000+1)*(10+1)<D)
    {ι Γ : Type} [Fintype ι] [DecidableEq ι] [Fintype Γ]
    (label : Γ → List (Codec.Raw h)) (hne : ∀c,label c≠[]) (W : Γ → Matrix ι ι K) :
    IsNilpotent (∑c,MatrixTests.tensor (W c)
      (DirectCancellation.eval (A.letters hh K) (label c))) := by
  let : _root_.Algebra (Polynomial K) (Polynomial (A.Algebra K h hh)) := Polynomial.algebra K _
  let F := (A.table h hh).polynomialCoefficients (K:=K)
  have hF : ∀v : List (Codec.Raw h),F (DirectCancellation.eval (A.letters hh (Polynomial K)) v)=
      Polynomial.C (DirectCancellation.eval (A.letters hh K) v) := by
    intro v
    rw [A.eval_letters,A.eval_letters]
    exact WordAlgebra.Table.polynomialCoefficients_word _ _
  let b : ℕ := 1+∑c,(label c).length
  have hb : 0<b := by dsimp [b];omega
  have hl : ∀c,(label c).length ≤ b := by
    intro c
    have hc := Finset.single_le_sum
      (fun i (_ : i∈(Finset.univ : Finset Γ))=>Nat.zero_le ((label i).length)) (Finset.mem_univ c)
    exact hc.trans (by dsimp [b];omega)
  let P : Γ → Matrix ι ι (Polynomial K) := fun c i j=>Polynomial.monomial 1 (W c i j)
  obtain ⟨N,hN⟩ := all_chunk_tests A hh (Polynomial K) hp hDbig (Fintype.card ι) b hb
    ι Γ le_rfl label hne hl P
  apply WeightedTests.nilpotent_of_eventually_zero_lengthPolynomial (fun c=>(label c).length)
    (fun c=>List.length_pos_iff.mpr (hne c))
  refine ⟨N,fun n hn=>?_⟩
  apply MatrixTests.polynomialMatrix_injective
  rw [map_zero]
  have he := MatrixTests.map_test_polynomial F (A.letters hh (Polynomial K)) (A.letters hh K)
    hF label W n
  exact he.symm.trans ((congrArg F.mapMatrix (hN n hn)).trans (map_zero _))

/-- Upstream `positive_matrix_nilpotent` in characteristic p. -/
theorem positive_matrix_nilpotent (hp : 0 < p) (hDbig : 10*(10000+1)*(10+1)<D)
    {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι (A.Algebra K h hh))
    (hM : ∀i j,M i j∈A.positiveSpan hh K) : IsNilpotent M := by
  let P := {w : List (Codec.Raw h) // w≠[]}
  have H (i j : ι) : ∃q : P →₀ K,
      q.sum (fun w a=>a • DirectCancellation.eval (A.letters hh K) w.val)=M i j :=
    Finsupp.mem_span_range_iff_exists_finsupp.mp (hM i j)
  choose q hq using H
  let Γ := Σi : ι,Σj : ι,{w : P // w∈(q i j).support}
  let label : Γ → List (Codec.Raw h) := fun c=>c.2.2.val.val
  let W : Γ → Matrix ι ι K := fun c=>Matrix.single c.1 c.2.1 (q c.1 c.2.1 c.2.2.val)
  have hz (w : P) : (0:K) • DirectCancellation.eval (A.letters hh K) w.val=0 := by
    exact @zero_smul K (A.Algebra K h hh) inferInstance inferInstance inferInstance _
  have he : (∑c : Γ,MatrixTests.tensor (W c)
      (DirectCancellation.eval (A.letters hh K) (label c)))=M := by
    apply Matrix.ext
    intro i j
    simp only [Matrix.sum_apply,Γ,Fintype.sum_sigma,MatrixTests.tensor,W,label,
      Matrix.single_apply]
    simp only [ite_smul,ite_and,hz,Finset.sum_ite_irrel,Finset.sum_const_zero,
      Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    exact (Finset.sum_coe_sort (q i j).support
      (fun w : P=>(q i j) w • DirectCancellation.eval (A.letters hh K) w.val)).trans (hq i j)
  rw [←he]
  exact word_matrix_sum_nilpotent A hh K hp hDbig label (fun c=>c.2.2.val.property) W

/-- Manuscript Theorem 18.1, matrix nilpotence: every finite matrix over the augmentation
kernel of the word algebra is nilpotent, in every prime characteristic. -/
theorem matrix_nil (hp : 0 < p) (hDbig : 10*(10000+1)*(10+1)<D) (n : ℕ)
    (M : Matrix (Fin n) (Fin n) (A.Algebra K h hh))
    (hM : (A.augmentation hh K).toRingHom.mapMatrix M = 0) : IsNilpotent M := by
  apply positive_matrix_nilpotent A hh K hp hDbig M
  intro i j
  apply A.augmentation_kernel_positive hh K (M i j)
  have hij := congrFun (congrFun hM i) j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.zero_apply] at hij
  exact hij

end Nilpotence

end
end AllPrimeGroups.PrimeMatrixNil
