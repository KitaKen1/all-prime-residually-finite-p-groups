import AllPrimeGroups.FrameExactness

/-! The prefix part of a boundary (manuscript Lemma 12.2, associated graded pieces).

Let `P = Q ++ [v]` be a frame ending in `v`. Faces of a frame `P ++ s` that delete an entry of
`P` no longer have prefix `P`, and if every frame of a chain has `v` at position at most `|Q|`, the
only faces with prefix `P` are suffix faces of frames with prefix `P`. Hence reading suffixes after
`P` commutes with the boundary up to the sign `(-1)^{|P|}` (`proj_bd`). -/

namespace AllPrimeGroups
namespace Frames

open Submodule Finset

variable {K : Type*} [Field K] {W : Type*} [AddCommGroup W] [Module K W] {ι : Type*} {f : ι → W}

/-- Every frame of a chain containing `v` has `v` at position at most `A`. -/
def PosLe (v : ι) (A : ℕ) (x : Frame K f →₀ ℤ) : Prop :=
  ∀ F ∈ x.support, ∀ L₁ L₂ : List ι, F.1 = L₁ ++ v :: L₂ → L₁.length ≤ A

theorem split_of_nodup {l : List ι} {v : ι} (hl : l.Nodup) {L₁ L₂ : List ι}
    (h : l = L₁ ++ v :: L₂) : v ∉ L₁ ∧ v ∉ L₂ := by
  subst h
  rw [List.nodup_append] at hl
  exact ⟨fun hv => hl.2.2 v hv v List.mem_cons_self rfl, (List.nodup_cons.mp hl.2.1).1⟩

section Split
variable {κ : Type*} {g : κ → ι} (hg : Function.Injective g) {v : ι}
  (hgv : ∀ y, g y ≠ v) (hgr : ∀ x, x ≠ v → x ∈ Set.range g)
  {Q : List ι} (hvQ : v ∉ Q) (hP : IsFrame K f (Q ++ [v]))

include hgv hvQ in
/-- Deleting an entry of the prefix destroys the prefix. -/
theorem appF_ne_face_pre (s t : Frame K (fq (K := K) (f := f) (g := g) (Q ++ [v]))) {i : ℕ}
    (hi : i < (Q ++ [v]).length) : appF hg (Q ++ [v]) hP t ≠ face (appF hg (Q ++ [v]) hP s) i := by
  intro h
  have h1 := congrArg Subtype.val h
  simp only [appF, face] at h1
  rw [List.eraseIdx_append_of_lt_length hi] at h1
  rw [List.length_append, List.length_singleton] at hi
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | hi
  · rw [List.eraseIdx_append_of_lt_length hi] at h1
    simp only [List.append_assoc, List.singleton_append] at h1
    obtain ⟨e, -⟩ := split_unique hvQ (fun hv => hvQ (List.mem_of_mem_eraseIdx hv)) h1
    have := congrArg List.length e
    rw [List.length_eraseIdx_of_lt hi] at this
    omega
  · subst hi
    rw [List.eraseIdx_append_of_length_le le_rfl, Nat.sub_self, List.eraseIdx_cons_zero,
      List.append_nil] at h1
    simp only [List.append_assoc, List.singleton_append] at h1
    have h2 := List.append_cancel_left h1
    have hv : v ∈ s.1.map g := h2 ▸ List.mem_cons_self
    obtain ⟨y, -, hy⟩ := List.mem_map.mp hv
    exact hgv y hy

include hgr hvQ in
/-- Faces of a frame without prefix `P`, with `v` early enough, do not have prefix `P`. -/
theorem appF_ne_face_other (F : Frame K f) (hF : ∀ s, appF hg (Q ++ [v]) hP s ≠ F)
    (hpos : ∀ L₁ L₂ : List ι, F.1 = L₁ ++ v :: L₂ → L₁.length ≤ Q.length)
    (t : Frame K (fq (K := K) (f := f) (g := g) (Q ++ [v]))) (i : ℕ) :
    appF hg (Q ++ [v]) hP t ≠ face F i := by
  intro h
  have h1 := congrArg Subtype.val h
  simp only [appF, face, List.append_assoc, List.singleton_append] at h1
  have hvF : v ∈ F.1 :=
    List.mem_of_mem_eraseIdx (h1 ▸ List.mem_append_right Q List.mem_cons_self)
  obtain ⟨L₁, L₂, hL⟩ := List.append_of_mem hvF
  obtain ⟨hv1, hv2⟩ := split_of_nodup F.2.1 hL
  have hlen := hpos L₁ L₂ hL
  rw [hL] at h1
  rcases lt_trichotomy i L₁.length with hi | hi | hi
  · rw [List.eraseIdx_append_of_lt_length hi] at h1
    obtain ⟨e, -⟩ := split_unique hvQ (fun hv => hv1 (List.mem_of_mem_eraseIdx hv)) h1
    have := congrArg List.length e
    rw [List.length_eraseIdx_of_lt hi] at this
    omega
  · subst hi
    rw [List.eraseIdx_append_of_length_le le_rfl, Nat.sub_self, List.eraseIdx_cons_zero] at h1
    have : v ∈ L₁ ++ L₂ := h1 ▸ List.mem_append_right Q List.mem_cons_self
    rcases List.mem_append.mp this with h' | h'
    · exact hv1 h'
    · exact hv2 h'
  · rw [List.eraseIdx_append_of_length_le hi.le] at h1
    obtain ⟨j, hj⟩ : ∃ j, i - L₁.length = j + 1 := ⟨i - L₁.length - 1, by omega⟩
    rw [hj, List.eraseIdx_cons_succ] at h1
    obtain ⟨e, -⟩ := split_unique hvQ hv1 h1
    have hL2 : ∀ x ∈ L₂, x ∈ Set.range g := fun x hx => hgr x (fun e' => hv2 (e' ▸ hx))
    obtain ⟨l', hl'⟩ := exists_map_eq hL2
    have hFl : F.1 = (Q ++ [v]) ++ l'.map g := by
      rw [hL, ← e, hl']
      simp [List.append_assoc]
    have hF' : IsFrame K f ((Q ++ [v]) ++ l'.map g) := hFl ▸ F.2
    exact hF ⟨l', IsFrame.of_append hg hF'⟩ (Subtype.ext hFl.symm)

include hgr hvQ in
theorem proj_faces_other (F : Frame K f) (hF : ∀ s, appF hg (Q ++ [v]) hP s ≠ F)
    (hpos : ∀ L₁ L₂ : List ι, F.1 = L₁ ++ v :: L₂ → L₁.length ≤ Q.length) :
    proj hg (Q ++ [v]) hP (faces F) = 0 := by
  rw [faces, map_sum]
  apply Finset.sum_eq_zero
  intro i _
  rw [map_zsmul, proj_single_of_notMem hg _ hP _
    (fun t => appF_ne_face_other hg hgr hvQ hP F hF hpos t i), smul_zero]

include hgv hgr hvQ in
/-- Reading suffixes after `P` commutes with the boundary up to sign. -/
theorem proj_bd (x : Frame K f →₀ ℤ) (hx : PosLe v Q.length x) :
    proj hg (Q ++ [v]) hP (bd x) = (-1 : ℤ) ^ (Q.length + 1) • bd (proj hg (Q ++ [v]) hP x) := by
  classical
  induction x using Finsupp.induction with
  | zero => simp
  | single_add F n z hF hn ih =>
    have hz : PosLe v Q.length z := by
      intro G hG
      apply hx
      have hGF : G ≠ F := fun e => hF (e ▸ hG)
      have e1 : (Finsupp.single F n + z) G = z G := by simp [Ne.symm hGF]
      rw [Finsupp.mem_support_iff, e1]
      exact Finsupp.mem_support_iff.mp hG
    have hFpos : ∀ L₁ L₂ : List ι, F.1 = L₁ ++ v :: L₂ → L₁.length ≤ Q.length := hx F (by
      have hz0 : z F = 0 := Finsupp.notMem_support_iff.mp hF
      rw [Finsupp.mem_support_iff, Finsupp.add_apply, Finsupp.single_eq_same, hz0, add_zero]
      exact hn)
    rw [map_add, map_add, map_add, map_add, ih hz, smul_add]
    congr 1
    rw [bd_single, map_zsmul]
    by_cases hex : ∃ s, appF hg (Q ++ [v]) hP s = F
    · obtain ⟨s, rfl⟩ := hex
      have hl : (Q ++ [v]).length = Q.length + 1 := by simp
      rw [proj_faces_appF hg _ hP s (fun i hi t => appF_ne_face_pre hg hgv hvQ hP s t hi), hl,
        proj_single_appF, bd_single, smul_comm]
    · have hex' : ∀ s, appF hg (Q ++ [v]) hP s ≠ F := fun s e => hex ⟨s, e⟩
      rw [proj_faces_other hg hgr hvQ hP F hex' hFpos, smul_zero,
        proj_single_of_notMem hg _ hP F hex', map_zero, smul_zero]

end Split

end Frames
end AllPrimeGroups
