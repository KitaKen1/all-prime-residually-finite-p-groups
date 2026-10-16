import Mathlib.LinearAlgebra.Multilinear.Basis
import Mathlib.LinearAlgebra.Matrix.StdBasis
import Mathlib.GroupTheory.Perm.Finite
import Mathlib.Data.Fintype.Perm
import Mathlib.GroupTheory.Coset.Basic
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Algebra.CharP.Basic

/-! Complete symmetrization in positive characteristic, without alternating signs. -/

namespace AllPrimeGroups

open scoped BigOperators
open Classical
attribute [local instance] Classical.propDecidable

noncomputable section

variable {K : Type*} [CommRing K] {V W : Type*}
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

def symmetrize {ι : Type*} [Fintype ι] (f : MultilinearMap K (fun _ : ι => V) W) :
    MultilinearMap K (fun _ : ι => V) W :=
  ∑ σ : Equiv.Perm ι, f.domDomCongr σ

theorem sum_eq_zero_of_right_invariant {G : Type*} [Group G] [Fintype G]
    (H : Subgroup G) (f : G → W)
    (hinv : ∀ g (h : H), f (g * h) = f g)
    (hzero : ∀ w : W, Nat.card H • w = 0) : ∑ g, f g = 0 := by
  let e : G ≃ (G ⧸ H) × H := {
    toFun := fun g => (QuotientGroup.mk g, ⟨(QuotientGroup.mk g : G ⧸ H).out⁻¹ * g,
      QuotientGroup.eq.mp (Quotient.out_eq' _)⟩)
    invFun := fun qh => qh.1.out * qh.2
    left_inv := by intro g; simp
    right_inv := by
      rintro ⟨q, h⟩
      have hq : (QuotientGroup.mk (q.out * h) : G ⧸ H) = q := by
        rw [QuotientGroup.mk_mul_of_mem _ h.property]
        exact QuotientGroup.out_eq' q
      apply Prod.ext
      · exact hq
      · apply Subtype.ext
        change (QuotientGroup.mk (q.out * h) : G ⧸ H).out⁻¹ * (q.out * h) = h
        rw [hq, inv_mul_cancel_left] }
  rw [← e.symm.sum_comp]
  change (∑ qh : (G ⧸ H) × H, f (qh.1.out * qh.2)) = 0
  simp only [Fintype.sum_prod_type, hinv, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, hzero,
    nsmul_zero]

theorem symmetrize_eq_zero_of_large_fiber {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p : ℕ) [CharP K p] (hp : 0 < p)
    (f : MultilinearMap K (fun _ : ι => V) W) (b : κ → V) (v : ι → κ)
    (k : κ) (hk : p ≤ Fintype.card {i // v i = k}) :
    symmetrize f (fun i => b (v i)) = 0 := by
  let φ : Equiv.Perm {i // v i = k} →* Equiv.Perm ι := Equiv.Perm.ofSubtype
  let H : Subgroup (Equiv.Perm ι) := φ.range
  have hcard : Nat.card H = (Fintype.card {i // v i = k}).factorial := by
    rw [Nat.card_eq_fintype_card, ← Fintype.card_congr (MonoidHom.ofInjective Equiv.Perm.ofSubtype_injective).toEquiv]
    exact Fintype.card_perm
  have hd : p ∣ Nat.card H := hcard ▸ Nat.dvd_factorial hp hk
  have hfiber (τ : H) (i : ι) : v (τ.val i) = v i := by
    obtain ⟨s, hs⟩ := τ.property
    rw [← hs]
    change v (Equiv.Perm.ofSubtype s i) = v i
    by_cases hi : v i = k
    · rw [Equiv.Perm.ofSubtype_apply_of_mem s hi]
      exact (s ⟨i, hi⟩).property.trans hi.symm
    · rw [Equiv.Perm.ofSubtype_apply_of_not_mem s hi]
  let F : Equiv.Perm ι → W := fun σ => f (fun i => b (v (σ⁻¹ i)))
  have hF : ∑ σ, F σ = 0 := by
    apply sum_eq_zero_of_right_invariant H
    · intro σ τ
      apply congrArg f
      funext i
      change b (v (τ.val⁻¹ (σ⁻¹ i))) = b (v (σ⁻¹ i))
      exact congrArg b (hfiber τ⁻¹ _)
    · intro w
      calc
        Nat.card H • w = (Nat.card H : K) • w := (Nat.cast_smul_eq_nsmul K _ _).symm
        _ = 0 := by rw [(CharP.cast_eq_zero_iff K p _).mpr hd, zero_smul]
  have he : (∑ σ : Equiv.Perm ι, F σ) = symmetrize f (fun i => b (v i)) := by
    simp only [symmetrize, sum_apply, MultilinearMap.domDomCongr_apply]
    exact Fintype.sum_equiv (Equiv.inv (Equiv.Perm ι)) F _ (fun _ => rfl)
  exact he ▸ hF

theorem symmetrize_eq_zero {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p : ℕ) [CharP K p] (hp : 0 < p) (b : Module.Basis κ K V)
    (f : MultilinearMap K (fun _ : ι => V) W)
    (hm : (p - 1) * Fintype.card κ < Fintype.card ι) : symmetrize f = 0 := by
  apply Module.Basis.ext_multilinear (fun _ => b)
  intro v
  obtain ⟨k, hk⟩ := Fintype.exists_lt_card_fiber_of_mul_lt_card (n := p - 1) v
    (by simpa only [Nat.mul_comm] using hm)
  have hcard : p ≤ Fintype.card {i // v i = k} := by
    rw [Fintype.card_subtype]
    omega
  simpa using symmetrize_eq_zero_of_large_fiber p hp f b v k hcard

/-- The matrix cancellation lemma needed to replace the characteristic-two argument. -/
theorem matrix_symmetrization_eq_zero {p d m : ℕ} [CharP K p] (hp : 0 < p)
    (X : Fin m → Matrix (Fin d) (Fin d) K) (hm : (p - 1) * d ^ 2 < m) :
    (∑ σ : Equiv.Perm (Fin m), (List.ofFn (X ∘ σ)).prod) = 0 := by
  let f := MultilinearMap.mkPiAlgebraFin K m (Matrix (Fin d) (Fin d) K)
  have hz := symmetrize_eq_zero p hp (Matrix.stdBasis K (Fin d) (Fin d)) f
    (by simpa [Fintype.card_prod, pow_two] using hm)
  have he := congrArg (fun F => F X) hz
  convert he using 1
  simp [symmetrize, MultilinearMap.domDomCongr_apply,
      MultilinearMap.mkPiAlgebraFin_apply, f, Function.comp_def]
  apply Finset.sum_congr
  · ext σ
    simp
  · intro σ _
    rfl

end

end AllPrimeGroups
