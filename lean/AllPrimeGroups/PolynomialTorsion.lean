/-
Torsion of polynomial matrix-kernel elements whose value at zero is trivial, adapted from
OpenAI PeriodicGroups/Steinberg/MatrixUnits.lean (commit pinned in upstream/provenance.json;
Apache-2.0, see upstream/OpenAI-LICENSE).
Upstream evaluates at the cyclic shift of size 2^k and obtains some finite order, allowing a
nontrivial ground element over the two-element field. Here the shift has size ℓ^k, the value
at zero is assumed trivial, and the conclusion is the exact exponent ℓ^k
(manuscript Theorem 14.1 at finite rank).
-/
import AllPrimeGroups.StablePermutation
import AllPrimeGroups.CyclicTriangularization

namespace AllPrimeGroups
universe u v w
variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]
namespace Kernel
noncomputable section
open Classical
variable {n : ℕ} {R : Type*} [Ring R] [Algebra (ZMod ℓ) R]

theorem stable_cyclic_evaluation (hn : 3≤n) (k : ℕ)
    (u : Steinberg n (Polynomial R)) (hu : Elementary.representation u=1) :
    padSteinberg (matrixSteinbergEval (cyclicShift (ℓ^k) (ZMod ℓ)) u)=
      padSteinberg (diagonalCopy (N:=ℓ^k) (Steinberg.map (scalarEval (1 : ZMod ℓ)) u)) := by
  obtain ⟨P,hdet,hP⟩ := cyclic_triangularization (ℓ:=ℓ) k
  have hdet' : (P⁻¹).val.det=1 := by
    have h1 : P.val.det*(P⁻¹).val.det=1 := by
      rw [←Matrix.det_mul,←Units.val_mul,mul_inv_cancel,Units.val_one,Matrix.det_one]
    rwa [hdet,one_mul] at h1
  have he := stable_numerical_similarity hn P⁻¹ hdet' (cyclicShift (ℓ^k) (ZMod ℓ)) u hu
  change padSteinberg (matrixSteinbergEval (cyclicShift (ℓ^k) (ZMod ℓ)) u)=
    padSteinberg (matrixSteinbergEval (P.inv*cyclicShift (ℓ^k) (ZMod ℓ)*P.val) u) at he
  rw [hP,triangular_evaluation (one_add_truncated_upper _) 1 (one_add_truncated_diag _) u hu] at he
  exact he

theorem stable_diagonal_evaluations (hn : 3≤n) (l : List (Root n×Polynomial R))
    (hm : 1≤l.length) (d k : ℕ) (hl : ∀pa∈l,pa.2.natDegree≤d)
    (hN : 2*(l.length+1)*max 1 d<ℓ^k)
    (hu : Elementary.representation (rootWord l)=1) :
    padSteinberg (diagonalCopy (N:=ℓ^k) (Steinberg.map (scalarEval (1 : ZMod ℓ)) (rootWord l)))=
      padSteinberg (diagonalCopy (N:=ℓ^k) (Steinberg.map (scalarEval (0 : ZMod ℓ)) (rootWord l))) := by
  rw [←stable_cyclic_evaluation hn k _ hu,wrap_removal l hm d hl hN hu]
  rw [triangular_evaluation truncatedShift_upper 0 truncatedShift_diag _ hu]

theorem stable_word_copy_torsion (hn : 3≤n) (l : List (Root n×Polynomial R))
    (hm : 1≤l.length) (d k : ℕ) (hl : ∀pa∈l,pa.2.natDegree≤d)
    (hN : 2*(l.length+1)*max 1 d<ℓ^k)
    (hu : Elementary.representation (rootWord l)=1)
    (hv : Steinberg.map (scalarEval (0 : ZMod ℓ)) (rootWord l)=1)
    (s : Fin (ℓ^k)) :
    (padSteinberg (copyMap s (Steinberg.map (scalarEval (1 : ZMod ℓ)) (rootWord l))))^(ℓ^k)=1 := by
  have hN2 : 2 ≤ ℓ^k := by
    have h1 : 1 ≤ max 1 d := le_max_left _ _
    have h2 := Nat.mul_le_mul (show 2 ≤ l.length+1 by omega) h1
    nlinarith [h2,hN]
  have hdiag := stable_diagonal_evaluations hn l hm d k hl hN hu
  rw [hv,map_one,map_one] at hdiag
  have hz := scalarEval_kernel (1 : ZMod ℓ) (rootWord l) hu
  rw [stable_diagonalCopy_pow (ℓ:=ℓ) hn hN2 s _ hz] at hdiag
  exact hdiag

theorem polynomial_kernel_copy_torsion (hn : 3≤n)
    (u : Steinberg n (Polynomial R)) (hu : Elementary.representation u=1)
    (hv : Steinberg.map (scalarEval (0 : ZMod ℓ)) u=1) :
    ∃k : ℕ,∃s : Fin (ℓ^k),2 ≤ ℓ^k ∧
      (padSteinberg (copyMap s (Steinberg.map (scalarEval (1 : ZMod ℓ)) u)))^(ℓ^k)=1 := by
  obtain ⟨l,hl⟩ := exists_rootWord u
  let p : Root n := ⟨⟨0,by omega⟩,⟨1,by omega⟩,by intro he;have hh : (0 : ℕ)=1 := congrArg Fin.val he;omega⟩
  let l' := l++[(p,(0 : Polynomial R))]
  have hl' : rootWord l'=u := by simp [l',rootWord,Steinberg.x_zero] at hl ⊢;exact hl
  have hm : 1≤l'.length := by dsimp [l'];simp
  let d := l'.toFinset.sup (fun pa=>pa.2.natDegree)
  have hd : ∀pa∈l',pa.2.natDegree≤d := by
    intro pa hpa
    exact Finset.le_sup (f:=fun pa : Root n×Polynomial R=>pa.2.natDegree) (List.mem_toFinset.mpr hpa)
  let k := 2*(l'.length+1)*max 1 d
  have hk : 2*(l'.length+1)*max 1 d<ℓ^k :=
    Nat.lt_two_pow_self.trans_le (Nat.pow_le_pow_left (Fact.out : ℓ.Prime).two_le k)
  let s : Fin (ℓ^k) := ⟨0,pow_pos (Fact.out : ℓ.Prime).pos k⟩
  have hmat : Elementary.representation (rootWord l')=1 := hl' ▸ hu
  have hval : Steinberg.map (scalarEval (0 : ZMod ℓ)) (rootWord l')=1 := hl' ▸ hv
  have hN2 : 2 ≤ ℓ^k := by
    have h1 : 1 ≤ max 1 d := le_max_left _ _
    have h2 := Nat.mul_le_mul (show 2 ≤ l'.length+1 by omega) h1
    nlinarith [h2,hk]
  have he := stable_word_copy_torsion hn l' hm d k hd hk hmat hval s
  refine ⟨k,s,hN2,?_⟩
  simpa only [hl'] using he

lemma pad_standard {q : ℕ} (hnq : n≤q) (u : Steinberg n R) :
    padSteinberg (Steinberg.coordinateMap (Fin.castLE hnq) (Fin.castLE_injective _) u)=
      Steinberg.coordinateMap (Fin.castLE (hnq.trans (Nat.le_succ q))) (Fin.castLE_injective _) u := by
  have H : padSteinberg.comp (Steinberg.coordinateMap (R:=R) (Fin.castLE hnq) (Fin.castLE_injective _))=
      Steinberg.coordinateMap (Fin.castLE (hnq.trans (Nat.le_succ q))) (Fin.castLE_injective _) := by
    apply Steinberg.hom_ext
    intro p a
    rfl
  exact DFunLike.congr_fun H u

/-- A polynomial matrix-kernel element with trivial value at zero has value at one of
ℓ-power order, after passing to a larger rank by the standard embedding. -/
theorem polynomial_kernel_standard_torsion (hn : 3≤n)
    (u : Steinberg n (Polynomial R)) (hu : Elementary.representation u=1)
    (hv : Steinberg.map (scalarEval (0 : ZMod ℓ)) u=1) :
    ∃q : ℕ,∃hnq : n≤q,∃k : ℕ,
      (Steinberg.coordinateMap (Fin.castLE hnq) (Fin.castLE_injective _)
        (Steinberg.map (scalarEval (1 : ZMod ℓ)) u))^(ℓ^k)=1 := by
  obtain ⟨k,s,hN2,he⟩ := polynomial_kernel_copy_torsion hn u hu hv
  have hnq : n≤n*ℓ^k := by nlinarith
  have hcopy := stable_copy_to_standard (ℓ:=ℓ) hn hN2 s (Steinberg.map (scalarEval (1 : ZMod ℓ)) u)
    (scalarEval_kernel 1 u hu)
  rw [hcopy,pad_standard] at he
  exact ⟨n*ℓ^k+1,hnq.trans (Nat.le_succ _),k,he⟩
end
end Kernel
end AllPrimeGroups
