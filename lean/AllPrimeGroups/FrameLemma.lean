import AllPrimeGroups.FrameSplit
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Auxiliary facts for the proof of manuscript Lemma 12.2: supports of boundaries and cones, the
position of a label under faces, degrees of appended chains, and the rank of the vectors modulo a
prefix. -/

namespace AllPrimeGroups
namespace Frames

open Submodule Finset Module

variable {K : Type*} [Field K] {W : Type*} [AddCommGroup W] [Module K W] {ι : Type*} {f : ι → W}

theorem mem_support_faces {F G : Frame K f} (h : G ∈ (faces F).support) : ∃ i, G = face F i := by
  classical
  obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp (Finsupp.support_finsetSum h)
  exact ⟨i, Finset.mem_singleton.mp (Finsupp.support_single_subset (Finsupp.support_smul hi))⟩

theorem bd_eq_sum (z : Frame K f →₀ ℤ) : bd z = ∑ F ∈ z.support, z F • faces F := by
  conv_lhs => rw [← Finsupp.sum_single z]
  rw [Finsupp.sum, map_sum]
  simp only [bd_single]

theorem mem_support_bd {z : Frame K f →₀ ℤ} {G : Frame K f} (h : G ∈ (bd z).support) :
    ∃ F ∈ z.support, ∃ i, G = face F i := by
  classical
  rw [bd_eq_sum] at h
  obtain ⟨F, hF, hG⟩ := Finset.mem_biUnion.mp (Finsupp.support_finsetSum h)
  exact ⟨F, hF, mem_support_faces (Finsupp.support_smul hG)⟩

theorem cone_eq_sum (v : ι) (z : Frame K f →₀ ℤ) : cone v z = ∑ F ∈ z.support, z F • coneF v F := by
  conv_lhs => rw [← Finsupp.sum_single z]
  rw [Finsupp.sum, map_sum]
  simp only [cone_single]

theorem deg_cone (v : ι) {k : ℕ} {z : Frame K f →₀ ℤ} (hz : Deg k z) : Deg (k + 1) (cone v z) := by
  classical
  rw [cone_eq_sum]
  apply Deg.sum
  intro F hF
  apply Deg.zsmul
  unfold coneF
  split_ifs with h
  · have := Deg.single (⟨v :: F.1, h⟩ : Frame K f) 1
    rwa [List.length_cons, hz F hF] at this
  · exact Deg.zero _

/-- Faces do not move a label to a later position. -/
theorem PosLe.bd {v : ι} {A : ℕ} {z : Frame K f →₀ ℤ} (hz : PosLe v A z) : PosLe v A (bd z) := by
  intro G hG M₁ M₂ hM
  obtain ⟨F, hF, i, rfl⟩ := mem_support_bd hG
  obtain ⟨hm1, -⟩ := split_of_nodup (face F i).2.1 hM
  have hvF : v ∈ F.1 :=
    List.mem_of_mem_eraseIdx (show v ∈ (face F i).1 from hM ▸ List.mem_append_right M₁ List.mem_cons_self)
  obtain ⟨L₁, L₂, hL⟩ := List.append_of_mem hvF
  obtain ⟨hv1, hv2⟩ := split_of_nodup F.2.1 hL
  have hle := hz F hF L₁ L₂ hL
  simp only [face] at hM
  rw [hL] at hM
  rcases lt_trichotomy i L₁.length with hi | hi | hi
  · rw [List.eraseIdx_append_of_lt_length hi] at hM
    obtain ⟨e, -⟩ := split_unique (fun hv => hv1 (List.mem_of_mem_eraseIdx hv)) hm1 hM
    rw [← e, List.length_eraseIdx_of_lt hi]
    omega
  · subst hi
    rw [List.eraseIdx_append_of_length_le le_rfl, Nat.sub_self, List.eraseIdx_cons_zero] at hM
    have : v ∈ L₁ ++ L₂ := hM ▸ List.mem_append_right M₁ List.mem_cons_self
    rcases List.mem_append.mp this with h' | h'
    · exact absurd h' hv1
    · exact absurd h' hv2
  · rw [List.eraseIdx_append_of_length_le hi.le] at hM
    obtain ⟨j, hj⟩ : ∃ j, i - L₁.length = j + 1 := ⟨i - L₁.length - 1, by omega⟩
    rw [hj, List.eraseIdx_cons_succ] at hM
    obtain ⟨e, -⟩ := split_unique hv1 hm1 hM
    rw [← e]
    exact hle

section Append
variable {κ : Type*} {g : κ → ι} (hg : Function.Injective g)

theorem deg_app (P : List ι) (hP : IsFrame K f P) {j : ℕ}
    {y : Frame K (fq (K := K) (f := f) (g := g) P) →₀ ℤ} (hy : Deg j y) :
    Deg (P.length + j) (app hg P hP y) := by
  classical
  intro F hF
  obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hF)
  simp only [appF, List.length_append, List.length_map]
  rw [hy s hs]

theorem posLe_app {v : ι} {Q : List ι} (hvQ : v ∉ Q) (hP : IsFrame K f (Q ++ [v]))
    (y : Frame K (fq (K := K) (f := f) (g := g) (Q ++ [v])) →₀ ℤ) :
    PosLe v Q.length (app hg (Q ++ [v]) hP y) := by
  classical
  intro F hF L₁ L₂ hL
  have hv1 := (split_of_nodup F.2.1 hL).1
  obtain ⟨s, -, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hF)
  have h1 : (appF hg (Q ++ [v]) hP s).1 = Q ++ v :: s.1.map g := by simp [appF]
  rw [h1] at hL
  obtain ⟨e, -⟩ := split_unique hvQ hv1 hL
  rw [← e]

theorem proj_eq_zero_of_free {v : ι} (P : List ι) (hvP : v ∈ P) (hP : IsFrame K f P)
    (z : Frame K f →₀ ℤ) (hz : ∀ G ∈ z.support, v ∉ G.1) : proj hg P hP z = 0 := by
  ext s
  simp only [proj, Finsupp.comapDomain.addMonoidHom_apply, Finsupp.comapDomain_apply,
    Finsupp.coe_zero, Pi.zero_apply]
  by_contra h
  exact hz _ (Finsupp.mem_support_iff.mpr h) (List.mem_append_left _ hvP)

include hg in
/-- The rank drops by at most the length of the prefix modulo which vectors are taken. -/
theorem finrank_le_fq [Finite ι] {v : ι} (hgr : ∀ x, x ≠ v → x ∈ Set.range g) (P : List ι)
    (hvP : v ∈ P) :
    finrank K (span K (Set.range f)) ≤
      finrank K (span K (Set.range (fq (K := K) (f := f) (g := g) P))) + P.length := by
  classical
  have : Finite κ := Finite.of_injective g hg
  set S := span K (Set.range f)
  set U := span K (f '' {x | x ∈ P})
  have : FiniteDimensional K S := FiniteDimensional.span_of_finite K (Set.finite_range f)
  have : FiniteDimensional K (span K (Set.range (fq (K := K) (f := f) (g := g) P))) :=
    FiniteDimensional.span_of_finite K (Set.finite_range _)
  have hU : U = span K ((P.map f).toFinset : Set W) := by
    rw [show U = span K (f '' {x | x ∈ P}) from rfl]
    congr 1
    ext w
    simp [List.mem_map]
  have : FiniteDimensional K U := by
    rw [hU]
    exact FiniteDimensional.span_finset K _
  let φ : S →ₗ[K] W ⧸ U := U.mkQ ∘ₗ S.subtype
  have hrange : LinearMap.range φ ≤ span K (Set.range (fq (K := K) (f := f) (g := g) P)) := by
    rw [LinearMap.range_comp, Submodule.range_subtype, Submodule.map_span, span_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    by_cases hi : i = v
    · subst hi
      have : U.mkQ (f i) = 0 := by
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact subset_span ⟨i, hvP, rfl⟩
      rw [SetLike.mem_coe, this]
      exact Submodule.zero_mem _
    · obtain ⟨y, rfl⟩ := hgr i hi
      exact subset_span ⟨y, rfl⟩
  have hker : finrank K (LinearMap.ker φ) ≤ finrank K U := by
    have hle : (LinearMap.ker φ).map S.subtype ≤ U := by
      rintro _ ⟨x, hx, rfl⟩
      have hx' : φ x = 0 := hx
      simpa [φ, Submodule.Quotient.mk_eq_zero] using hx'
    have := Submodule.finrank_mono hle
    rwa [Submodule.finrank_map_subtype_eq] at this
  have hU' : finrank K U ≤ P.length := by
    rw [hU]
    exact (finrank_span_finset_le_card _).trans (List.toFinset_card_le _ |>.trans (by simp))
  have h := LinearMap.finrank_range_add_finrank_ker φ
  have h2 := Submodule.finrank_mono hrange
  calc finrank K S = finrank K (LinearMap.range φ) + finrank K (LinearMap.ker φ) := h.symm
    _ ≤ _ := add_le_add h2 (hker.trans hU')

end Append

end Frames
end AllPrimeGroups
