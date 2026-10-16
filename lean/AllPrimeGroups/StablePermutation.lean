/-
Coordinate copies of matrix-kernel elements agree stably, adapted from OpenAI
PeriodicGroups/Steinberg/MatrixUnits.lean (commit pinned in upstream/provenance.json;
Apache-2.0, see upstream/OpenAI-LICENSE).
Upstream lifts arbitrary permutation matrices over the two-element field. Over `ZMod ℓ` a
permutation matrix lifts to the Steinberg group when the permutation is even, and an even
permutation with the required values always exists once two spare coordinates are
available. Equality of two copies is then deduced from the comparison with the standard
copy, so no separate interchange of blocks is needed.
-/
import AllPrimeGroups.NumericalSimilarity
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Logic.Equiv.Fintype

namespace AllPrimeGroups
universe u v w
variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]
namespace Kernel
noncomputable section
open Classical

section Copies
variable {n N : ℕ} {R : Type*} [Ring R]

def copyMatrixHom (s : Fin N) : Matrix (Fin n) (Fin n) R →* Matrix (Fin (n*N)) (Fin (n*N)) R :=
  (Matrix.reindexRingEquiv R finProdFinEquiv).toMonoidHom.comp
    ((Matrix.blockDiagonalRingHom (Fin n) (Fin N) R).toMonoidHom.comp (MonoidHom.mulSingle (fun _ : Fin N=>Matrix (Fin n) (Fin n) R) s))

def copyUnitsHom (s : Fin N) : (Matrix (Fin n) (Fin n) R)ˣ →* (Matrix (Fin (n*N)) (Fin (n*N)) R)ˣ :=
  Units.map (copyMatrixHom s)

lemma copyUnitsHom_e (s : Fin N) (p : Root n) (a : R) :
    copyUnitsHom s (Elementary.e p a)=Elementary.e (blockPosition p (s,s)) a := by
  apply Units.ext
  apply Matrix.ext
  intro u v
  obtain ⟨⟨i,t⟩,rfl⟩ := finProdFinEquiv.surjective u
  obtain ⟨⟨j,z⟩,rfl⟩ := finProdFinEquiv.surjective v
  change (Matrix.blockDiagonal (Pi.mulSingle s (1+Matrix.single p.row p.col a))).submatrix
    finProdFinEquiv.symm finProdFinEquiv.symm (finProdFinEquiv (i,t)) (finProdFinEquiv (j,z))=
    (1+Matrix.single (blockIndex p.row s) (blockIndex p.col s) a) (finProdFinEquiv (i,t)) (finProdFinEquiv (j,z))
  simp only [Matrix.submatrix_apply,Equiv.symm_apply_apply,Matrix.blockDiagonal_apply,
    Pi.mulSingle_apply,Matrix.add_apply,Matrix.one_apply,Matrix.single_apply,blockIndex]
  by_cases htz : t=z <;> by_cases hts : t=s <;>
    simp_all [Matrix.add_apply,Matrix.one_apply,Matrix.single_apply,Prod.ext_iff,eq_comm,and_comm]

lemma copy_representation (s : Fin N) :
    Elementary.representation.comp (copyMap (n:=n) (R:=R) s)= (copyUnitsHom s).comp Elementary.representation := by
  apply Steinberg.hom_ext
  intro p a
  simp only [MonoidHom.comp_apply,copyMap_x,Elementary.representation_x,copyUnitsHom_e]

lemma copy_kernel (s : Fin N) (u : Steinberg n R) (hu : Elementary.representation u=1) :
    Elementary.representation (copyMap s u)=1 := by
  have he := DFunLike.congr_fun (copy_representation (n:=n) (R:=R) s) u
  simpa only [MonoidHom.comp_apply,hu,map_one] using he

end Copies

section RingMaps
variable {n N : ℕ} {R S : Type*} [Ring R] [Ring S]

lemma pad_ringMap (f : R →+* S) (u : Steinberg n R) :
    Steinberg.map f (padSteinberg u)=padSteinberg (Steinberg.map f u) := by
  have he : (Steinberg.map f).comp padSteinberg=padSteinberg.comp (Steinberg.map (n:=n) f) := by
    apply Steinberg.hom_ext
    intro p a
    simp [padSteinberg,Steinberg.map_x]
  exact DFunLike.congr_fun he u

lemma copy_ringMap (f : R →+* S) (s : Fin N) (u : Steinberg n R) :
    Steinberg.map f (copyMap s u)=copyMap s (Steinberg.map f u) := by
  have he : (Steinberg.map f).comp (copyMap s)=(copyMap s).comp (Steinberg.map (n:=n) f) := by
    apply Steinberg.hom_ext
    intro p a
    simp [Steinberg.map_x]
  exact DFunLike.congr_fun he u

end RingMaps

section Permutations
variable {n m : ℕ} {R : Type*} [Ring R] [hR : Algebra (ZMod ℓ) R]

/-- The permutation matrix of a permutation of the coordinates, over the prime field. -/
def permutationUnits (ℓ : ℕ) {m : ℕ} (σ : Equiv.Perm (Fin m)) :
    (Matrix (Fin m) (Fin m) (ZMod ℓ))ˣ where
  val := σ⁻¹.permMatrix (ZMod ℓ)
  inv := σ.permMatrix (ZMod ℓ)
  val_inv := by rw [←Matrix.permMatrix_mul];simp
  inv_val := by rw [←Matrix.permMatrix_mul];simp

lemma permutationUnits_det (σ : Equiv.Perm (Fin m)) (hσ : Equiv.Perm.sign σ=1) :
    (permutationUnits ℓ σ).val.det=1 := by
  change (σ⁻¹.permMatrix (ZMod ℓ)).det=1
  rw [Matrix.det_permutation,Equiv.Perm.sign_inv,hσ]
  simp

lemma numerical_lift (P : (Matrix (Fin m) (Fin m) (ZMod ℓ))ˣ) (hP : P.val.det=1) :
    ∃b : Steinberg m R,Elementary.representation b=numericUnits (R:=R) P := by
  obtain ⟨b,hb'⟩ := Elementary.exists_representation_eq P hP
  refine ⟨Steinberg.map (algebraMap (ZMod ℓ) R) b,?_⟩
  have he := DFunLike.congr_fun (Elementary.representation_map (n:=m) (algebraMap (ZMod ℓ) R)) b
  simpa only [MonoidHom.comp_apply,hb',numericUnits] using he

lemma permutation_conjugates_e (σ : Equiv.Perm (Fin m)) (p : Root m) (a : R) :
    numericUnits (R:=R) (permutationUnits ℓ σ)*Elementary.e p a*
      (numericUnits (R:=R) (permutationUnits ℓ σ))⁻¹=
      Elementary.e (p.map σ σ.injective) a := by
  apply Units.ext
  change (((σ⁻¹).permMatrix (ZMod ℓ)).map (algebraMap (ZMod ℓ) R))*(1+Matrix.single p.row p.col a)*
    ((σ.permMatrix (ZMod ℓ)).map (algebraMap (ZMod ℓ) R))=1+Matrix.single (σ p.row) (σ p.col) a
  simp only [Equiv.Perm.permMatrix,PEquiv.map_toMatrix,PEquiv.toMatrix_toPEquiv_mul,
    PEquiv.mul_toMatrix_toPEquiv,Equiv.Perm.inv_def]
  ext i j
  simp [Matrix.submatrix_apply,Matrix.add_apply,Matrix.one_apply,Matrix.single_apply,
    ← Equiv.eq_symm_apply]

include hℓ hR in
/-- An even permutation of the coordinates fixes a matrix-kernel element after one
coordinate is added. -/
theorem stable_permutation_fixed (hm : 3 ≤ m) (σ : Equiv.Perm (Fin m))
    (hσ : Equiv.Perm.sign σ=1)
    (u : Steinberg m R) (hu : Elementary.representation u=1) :
    padSteinberg (Steinberg.coordinateMap σ σ.injective u)=padSteinberg u := by
  obtain ⟨b,hb⟩ := numerical_lift (R:=R) (permutationUnits ℓ σ) (permutationUnits_det σ hσ)
  let f := (MulAut.conj b).toMonoidHom
  let g := Steinberg.coordinateMap (R:=R) σ σ.injective
  have he : Elementary.representation.comp f=Elementary.representation.comp g := by
    apply Steinberg.hom_ext
    intro p a
    change Elementary.representation (b*Steinberg.x p a*b⁻¹)=_
    rw [map_mul,map_mul,map_inv,hb,Elementary.representation_x]
    change _=Elementary.representation (Steinberg.x (p.map σ σ.injective) a)
    rw [Elementary.representation_x]
    exact permutation_conjugates_e σ p a
  have hf := DFunLike.congr_fun (stable_uniqueness hm f g (fun v=>DFunLike.congr_fun he v)) u
  have hz := stabilized_kernel_central u hu
  have hc : Commute (padSteinberg b) (padSteinberg u) := Subgroup.mem_center_iff.mp hz _
  change padSteinberg (b*u*b⁻¹)=padSteinberg (Steinberg.coordinateMap σ σ.injective u) at hf
  simpa only [map_mul,map_inv,CommutatorCalculus.conj_of_commute hc] using hf.symm

omit hℓ hR in
lemma coordinateMap_comp (f : Fin n→Fin m) (hf : Function.Injective f) {q : ℕ}
    (g : Fin m→Fin q) (hg : Function.Injective g) :
    (Steinberg.coordinateMap (R:=R) g hg).comp (Steinberg.coordinateMap f hf)=
      Steinberg.coordinateMap (g∘f) (hg.comp hf) := by
  apply Steinberg.hom_ext
  intro p a
  rfl

omit hℓ in
/-- With two spare coordinates, the copy coordinates can be moved to the standard ones by an
even permutation. -/
lemma exists_even_extension {N : ℕ} (hn : 3 ≤ n) (hN : 2 ≤ N) (s : Fin N) (hnm : n ≤ n*N) :
    ∃σ : Equiv.Perm (Fin (n*N)),Equiv.Perm.sign σ=1 ∧
      ∀i : Fin n,σ (blockIndex i s)=Fin.castLE hnm i := by
  let f := fun i : Fin n=>blockIndex i s
  have hf : Function.Injective f := fun i j he=>congrArg Prod.fst (finProdFinEquiv.injective he)
  obtain ⟨σ,hσ⟩ := Equiv.Perm.exists_extending_pair f (Fin.castLE hnm) hf (Fin.castLE_injective _)
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h1 | h1
  · exact ⟨σ,h1,hσ⟩
  · obtain ⟨s',hs'⟩ : ∃s' : Fin N,s≠s' := by
      by_cases h0 : s.val=0
      · refine ⟨⟨1,by omega⟩,fun h=>?_⟩
        have hv : s.val=1 := congrArg Fin.val h
        omega
      · refine ⟨⟨0,by omega⟩,fun h=>?_⟩
        have hv : s.val=0 := congrArg Fin.val h
        omega
    let i₀ : Fin n := ⟨0,by omega⟩
    let i₁ : Fin n := ⟨1,by omega⟩
    have h01 : i₀≠i₁ := by
      intro h
      have hv : (0 : ℕ)=1 := congrArg Fin.val h
      omega
    have hab : blockIndex i₀ s'≠blockIndex i₁ s' := blockIndex_ne h01 s' s'
    refine ⟨σ*Equiv.swap (blockIndex i₀ s') (blockIndex i₁ s'),?_,?_⟩
    · rw [Equiv.Perm.sign_mul,h1,Equiv.Perm.sign_swap hab]
      simp
    · intro i
      have ha : blockIndex i s≠blockIndex i₀ s' := blockIndex_ne_inner i i₀ hs'
      have hb : blockIndex i s≠blockIndex i₁ s' := blockIndex_ne_inner i i₁ hs'
      rw [Equiv.Perm.mul_apply,Equiv.swap_apply_of_ne_of_ne ha hb]
      exact hσ i

include hℓ hR in
/-- A copy of a matrix-kernel element in any block agrees stably with its standard copy. -/
theorem stable_copy_to_standard (hn : 3 ≤ n) {N : ℕ} (hN : 2 ≤ N) (s : Fin N)
    (u : Steinberg n R) (hu : Elementary.representation u=1) :
    padSteinberg (copyMap s u)=
      padSteinberg (Steinberg.coordinateMap (Fin.castLE (show n≤n*N by nlinarith))
        (Fin.castLE_injective _) u) := by
  have hnm : n≤n*N := by nlinarith
  let f := fun i : Fin n=>blockIndex i s
  have hf : Function.Injective f := fun i j he=>congrArg Prod.fst (finProdFinEquiv.injective he)
  obtain ⟨σ,hsign,hσ⟩ := exists_even_extension hn hN s hnm
  have he := stable_permutation_fixed (ℓ:=ℓ) (R:=R) (by nlinarith : 3 ≤ n*N) σ hsign
    (copyMap s u) (copy_kernel s u hu)
  have H : (Steinberg.coordinateMap (R:=R) σ σ.injective).comp (copyMap s)=
      Steinberg.coordinateMap (Fin.castLE hnm) (Fin.castLE_injective _) := by
    change (Steinberg.coordinateMap σ σ.injective).comp (Steinberg.coordinateMap f hf)=_
    rw [coordinateMap_comp]
    have heq : σ∘f=Fin.castLE hnm := funext hσ
    simp only [heq]
  have hU := DFunLike.congr_fun H u
  change Steinberg.coordinateMap σ σ.injective (copyMap s u)=
    Steinberg.coordinateMap (Fin.castLE hnm) (Fin.castLE_injective _) u at hU
  exact he.symm.trans (congrArg padSteinberg hU)

include hℓ hR in
theorem stable_copy_eq (hn : 3≤n) {N : ℕ} (hN : 2 ≤ N) (s t : Fin N) (u : Steinberg n R)
    (hu : Elementary.representation u=1) : padSteinberg (copyMap s u)=padSteinberg (copyMap t u) :=
  (stable_copy_to_standard (ℓ:=ℓ) hn hN s u hu).trans
    (stable_copy_to_standard (ℓ:=ℓ) hn hN t u hu).symm

include hℓ hR in
lemma stable_diagonalCopy_pow (hn : 3≤n) {N : ℕ} (hN : 2 ≤ N) (s : Fin N) (u : Steinberg n R)
    (hu : Elementary.representation u=1) :
    padSteinberg (diagonalCopy (N:=N) u)=padSteinberg (copyMap s u)^N := by
  change padSteinberg (Finset.noncommProd Finset.univ (fun t : Fin N=>copyMap t u) (fun _ _ _ _ h=>copy_commute h u u))=_
  erw [Finset.map_noncommProd]
  have he := Finset.noncommProd_eq_pow_card Finset.univ (fun t : Fin N=>padSteinberg (copyMap t u))
    (fun t ht z hz htz=>(copy_commute htz u u).map padSteinberg)
    (padSteinberg (copyMap s u)) (fun t _=>stable_copy_eq (ℓ:=ℓ) hn hN t s u hu)
  simpa using he

end Permutations

end
end Kernel
end AllPrimeGroups
