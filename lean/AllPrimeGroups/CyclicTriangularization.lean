/-
Triangularization of the cyclic shift of prime-power size by the Pascal matrix, adapted from
OpenAI PeriodicGroups/Steinberg/MatrixUnits.lean (commit pinned in upstream/provenance.json;
Apache-2.0, see upstream/OpenAI-LICENSE).
Upstream treats size 2^k over the two-element field. The same computation works for size
ℓ^k over `ZMod ℓ`, because ℓ divides the binomial coefficients of ℓ^k strictly between the
ends. The Pascal matrix has determinant one.
-/
import AllPrimeGroups.BandFactorization
import Mathlib.Data.Nat.Multiplicity
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

namespace AllPrimeGroups
universe u v w
variable {ℓ : ℕ} [Fact ℓ.Prime]
namespace Kernel
noncomputable section
open Classical
variable {N : ℕ}

def pascalMatrix (ℓ N : ℕ) : Matrix (Fin N) (Fin N) (ZMod ℓ) := fun s t=>(s.val.choose t.val : ZMod ℓ)

lemma pascal_lower : (pascalMatrix ℓ N).IsLowerTriangular := by
  intro s t hst
  change s.val<t.val at hst
  change ((s.val.choose t.val : ℕ) : ZMod ℓ)=0
  rw [Nat.choose_eq_zero_of_lt hst,Nat.cast_zero]

lemma pascal_det : (pascalMatrix ℓ N).det=1 := by
  rw [Matrix.det_of_isLowerTriangular _ pascal_lower]
  simp [pascalMatrix]

omit [Fact ℓ.Prime] in
lemma matrix_mul_truncated {R : Type*} [Ring R] (A : Matrix (Fin N) (Fin N) R) (s t : Fin N) :
    (A*truncatedShift N R) s t=if h : t.val=0 then 0 else A s ⟨t.val-1,by have := t.isLt;omega⟩ := by
  rw [Matrix.mul_apply]
  by_cases ht : t.val=0
  · rw [dite_eq_left ht]
    apply Finset.sum_eq_zero
    intro k _
    have he : k.val+1≠t.val := by omega
    simp [truncatedShift,he]
  · rw [dite_eq_right ht]
    let k : Fin N := ⟨t.val-1,by have := t.isLt;omega⟩
    rw [Finset.sum_eq_single k]
    · have he : k.val+1=t.val := by dsimp [k];omega
      simp [truncatedShift,he,k]
    · intro u _ huk
      have he : u.val+1≠t.val := by
        intro he
        apply huk
        apply Fin.ext
        dsimp [k]
        omega
      simp [truncatedShift,he]
    · simp

omit [Fact ℓ.Prime] in
lemma cyclic_mul_matrix {R : Type*} [Ring R] (hN : 0<N)
    (A : Matrix (Fin N) (Fin N) R) (s t : Fin N) :
    (cyclicShift N R*A) s t=A ⟨(s.val+1)%N,Nat.mod_lt _ hN⟩ t := by
  rw [Matrix.mul_apply]
  let k : Fin N := ⟨(s.val+1)%N,Nat.mod_lt _ hN⟩
  rw [Finset.sum_eq_single k]
  · simp [cyclicShift,k]
  · intro u _ huk
    have he : (s.val+1)%N≠u.val := by intro he;apply huk;apply Fin.ext;exact he.symm
    simp [cyclicShift,he]
  · simp

lemma pascal_times_unipotent (s t : Fin N) :
    (pascalMatrix ℓ N*(1+truncatedShift N (ZMod ℓ))) s t=((s.val+1).choose t.val : ZMod ℓ) := by
  rw [mul_add,mul_one,Matrix.add_apply,matrix_mul_truncated]
  by_cases ht : t.val=0
  · simp [ht,pascalMatrix]
  · rw [dite_eq_right ht]
    change (s.val.choose t.val : ZMod ℓ)+(s.val.choose (t.val-1) : ZMod ℓ)=_
    have hk : t.val=(t.val-1)+1 := by omega
    conv_rhs => rw [hk,Nat.choose_succ_succ',Nat.cast_add]
    rw [←hk,add_comm]

lemma prime_power_choose (k j : ℕ) (hj : j<ℓ^k) :
    ((ℓ^k).choose j : ZMod ℓ)=((0 : ℕ).choose j : ZMod ℓ) := by
  by_cases hz : j=0
  · simp [hz]
  · have hd : ℓ ∣ (ℓ^k).choose j := (Fact.out : ℓ.Prime).dvd_choose_pow hz hj.ne
    have hc : ((ℓ^k).choose j : ZMod ℓ)=0 := (CharP.cast_eq_zero_iff (ZMod ℓ) ℓ _).mpr hd
    rw [hc]
    have hj0 : 0<j := by omega
    rw [Nat.choose_eq_zero_of_lt hj0,Nat.cast_zero]

lemma cyclic_pascal (k : ℕ) :
    cyclicShift (ℓ^k) (ZMod ℓ)*pascalMatrix ℓ (ℓ^k)=
      pascalMatrix ℓ (ℓ^k)*(1+truncatedShift (ℓ^k) (ZMod ℓ)) := by
  ext s t
  rw [cyclic_mul_matrix (pow_pos (Fact.out : ℓ.Prime).pos k),pascal_times_unipotent]
  change (((s.val+1)%(ℓ^k)).choose t.val : ZMod ℓ)=((s.val+1).choose t.val : ZMod ℓ)
  by_cases hs : s.val+1<ℓ^k
  · rw [Nat.mod_eq_of_lt hs]
  · have he : s.val+1=ℓ^k := by have := s.isLt;omega
    rw [he,Nat.mod_self]
    exact (prime_power_choose k t.val t.isLt).symm

/-- The cyclic shift of size ℓ^k is conjugate over `ZMod ℓ`, by a matrix of determinant one,
to an upper triangular matrix with unit diagonal. -/
theorem cyclic_triangularization (k : ℕ) :
    ∃P : (Matrix (Fin (ℓ^k)) (Fin (ℓ^k)) (ZMod ℓ))ˣ, P.val.det=1 ∧
      P.inv*cyclicShift (ℓ^k) (ZMod ℓ)*P.val=1+truncatedShift (ℓ^k) (ZMod ℓ) := by
  have hi : IsUnit (pascalMatrix ℓ (ℓ^k)) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (by rw [pascal_det];exact isUnit_one)
  obtain ⟨P,hP⟩ := hi
  refine ⟨P,by rw [hP,pascal_det],?_⟩
  have he := cyclic_pascal (ℓ:=ℓ) k
  rw [←hP] at he
  calc
    _ = P.inv*(cyclicShift (ℓ^k) (ZMod ℓ)*P.val) := by simp [mul_assoc]
    _ = P.inv*(P.val*(1+truncatedShift (ℓ^k) (ZMod ℓ))) := congrArg (fun A=>P.inv*A) he
    _ = _ := by simp [←mul_assoc]

lemma one_add_truncated_upper (N : ℕ) :
    ((1 : Matrix (Fin N) (Fin N) (ZMod ℓ))+truncatedShift N (ZMod ℓ)).IsUpperTriangular := by
  intro s t hts
  have hne : s≠t := ne_of_gt hts
  simp only [Matrix.add_apply,Matrix.one_apply,ite_eq_right hne,truncatedShift_upper hts,zero_add]

lemma one_add_truncated_diag (N : ℕ) (s : Fin N) :
    ((1 : Matrix (Fin N) (Fin N) (ZMod ℓ))+truncatedShift N (ZMod ℓ)) s s=1 := by
  simp [Matrix.add_apply,truncatedShift_diag]

end
end Kernel
end AllPrimeGroups
