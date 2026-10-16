import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finsupp.Basic

/-! The augmented ordered frame complex (manuscript Section 12, before Lemma 12.2).

Labels `ι` carry vectors `f : ι → W`. An ordered frame is a list of distinct labels whose vectors
are linearly independent; every ordering is a separate generator, and the empty list is the
augmentation. Chains of all degrees are finitely supported integer functions on frames, and the
boundary deletes entries with alternating signs. Prepending a label whose vector is independent of
a frame is a chain homotopy (`bd_cone`). -/

namespace AllPrimeGroups
namespace Frames

open Submodule Finset

variable (K : Type*) [Field K] {W : Type*} [AddCommGroup W] [Module K W] {ι : Type*} (f : ι → W)

/-- Ordered frames: lists of distinct labels with linearly independent vectors. -/
def IsFrame (l : List ι) : Prop := l.Nodup ∧ LinearIndepOn K f {x | x ∈ l}

/-- Ordered frames. -/
abbrev Frame := {l : List ι // IsFrame K f l}

variable {K f}

theorem IsFrame.sublist {l l' : List ι} (h : IsFrame K f l) (hs : List.Sublist l' l) : IsFrame K f l' :=
  ⟨h.1.sublist hs, h.2.mono (fun _ hx => hs.subset hx)⟩

theorem IsFrame.eraseIdx {l : List ι} (h : IsFrame K f l) (i : ℕ) : IsFrame K f (l.eraseIdx i) :=
  h.sublist (List.eraseIdx_sublist l i)

theorem isFrame_nil : IsFrame K f ([] : List ι) := by
  refine ⟨List.nodup_nil, ?_⟩
  have : {x : ι | x ∈ ([] : List ι)} = ∅ := by
    ext x
    simp
  rw [this]
  exact linearIndepOn_empty K f

theorem isFrame_cons {v : ι} {l : List ι} :
    IsFrame K f (v :: l) ↔ v ∉ l ∧ IsFrame K f l ∧ f v ∉ span K (f '' {x | x ∈ l}) := by
  have hs : {x : ι | x ∈ v :: l} = insert v {x | x ∈ l} := by
    ext x
    simp
  unfold IsFrame
  rw [hs, List.nodup_cons]
  constructor
  · rintro ⟨⟨hv, hl⟩, hi⟩
    have hv' : v ∉ {x : ι | x ∈ l} := hv
    rw [linearIndepOn_insert hv'] at hi
    exact ⟨hv, ⟨hl, hi.1⟩, hi.2⟩
  · rintro ⟨hv, ⟨hl, hi⟩, hs⟩
    have hv' : v ∉ {x : ι | x ∈ l} := hv
    exact ⟨⟨hv, hl⟩, (linearIndepOn_insert hv').mpr ⟨hi, hs⟩⟩

/-! ### The boundary -/

/-- A face of a frame. -/
def face (F : Frame K f) (i : ℕ) : Frame K f := ⟨F.1.eraseIdx i, F.2.eraseIdx i⟩

/-- The alternating sum of the faces of a frame. -/
noncomputable def faces (F : Frame K f) : Frame K f →₀ ℤ :=
  ∑ i ∈ range F.1.length, (-1 : ℤ) ^ i • Finsupp.single (face F i) 1

/-- The boundary. -/
noncomputable def bd : (Frame K f →₀ ℤ) →+ (Frame K f →₀ ℤ) :=
  Finsupp.liftAddHom (fun F => zmultiplesHom _ (faces F))

theorem bd_single (F : Frame K f) (n : ℤ) : bd (Finsupp.single F n) = n • faces F := by
  simp [bd]

theorem List.eraseIdx_eraseIdx_of_le {α : Type*} :
    ∀ (l : List α) (i j : ℕ), i ≤ j → (l.eraseIdx i).eraseIdx j = (l.eraseIdx (j + 1)).eraseIdx i
  | [], _, _, _ => by simp
  | a :: l, 0, j, _ => by simp
  | a :: l, i + 1, j + 1, h => by
    simp only [List.eraseIdx_cons_succ]
    rw [List.eraseIdx_eraseIdx_of_le l i j (by omega)]
  | _ :: _, _ + 1, 0, h => absurd h (by omega)

/-- Alternating double sums of double deletions vanish. -/
theorem alt_double_sum {M : Type*} [AddCommGroup M] (n : ℕ) (e : ℕ → ℕ → M)
    (he : ∀ i j, i ≤ j → j < n → e i j = e (j + 1) i) :
    ∑ i ∈ range (n + 1), ∑ j ∈ range n, ((-1 : ℤ) ^ (i + j)) • e i j = 0 := by
  rw [← Finset.sum_product']
  refine Finset.sum_involution (fun p _ => if p.1 ≤ p.2 then (p.2 + 1, p.1) else (p.2, p.1 - 1))
    ?_ ?_ ?_ ?_
  · rintro ⟨i, j⟩ hp
    simp only [Finset.mem_product, Finset.mem_range] at hp
    by_cases hij : i ≤ j
    · simp only [hij, ↓reduceIte]
      rw [← he i j hij hp.2, show j + 1 + i = (i + j) + 1 by omega, pow_succ]
      simp
    · simp only [hij, ↓reduceIte]
      have hi : 1 ≤ i := by omega
      rw [he j (i - 1) (by omega) (by omega), show i - 1 + 1 = i by omega,
        show i + j = (j + (i - 1)) + 1 by omega, pow_succ]
      simp
  · rintro ⟨i, j⟩ _ _
    by_cases hij : i ≤ j
    · simp only [hij, ↓reduceIte, ne_eq, Prod.mk.injEq]
      omega
    · simp only [hij, ↓reduceIte, ne_eq, Prod.mk.injEq]
      omega
  · rintro ⟨i, j⟩ hp
    simp only [Finset.mem_product, Finset.mem_range] at hp ⊢
    by_cases hij : i ≤ j
    · simp only [hij, ↓reduceIte]
      omega
    · simp only [hij, ↓reduceIte]
      omega
  · rintro ⟨i, j⟩ _
    by_cases hij : i ≤ j
    · have h2 : ¬ j + 1 ≤ i := by omega
      simp only [hij, h2, ↓reduceIte, Nat.add_sub_cancel]
    · have h2 : j ≤ i - 1 := by omega
      have h3 : i - 1 + 1 = i := by omega
      simp only [hij, h2, ↓reduceIte, h3]

theorem bd_faces (F : Frame K f) : bd (faces F) = 0 := by
  obtain ⟨l, hl⟩ := F
  rcases l with _ | ⟨a, l⟩
  · simp [faces]
  · have hlen : ∀ i ∈ range (a :: l).length, (face ⟨a :: l, hl⟩ i).1.length = l.length := by
      intro i hi
      simp only [face]
      rw [List.length_eraseIdx_of_lt (by simpa using hi)]
      simp
    simp only [faces, map_sum, map_zsmul, bd_single, smul_sum, smul_smul]
    rw [Finset.sum_congr rfl (fun i hi => by rw [hlen i hi])]
    have := alt_double_sum (M := Frame K f →₀ ℤ) l.length
      (fun i j => Finsupp.single (face (face ⟨a :: l, hl⟩ i) j) 1) (by
        intro i j hij hj
        congr 1
        apply Subtype.ext
        exact List.eraseIdx_eraseIdx_of_le _ i j hij)
    simpa only [List.length_cons, pow_add, one_mul] using this

theorem bd_bd (z : Frame K f →₀ ℤ) : bd (bd z) = 0 := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]
  | single F n => rw [bd_single, map_zsmul, bd_faces, smul_zero]

/-! ### Prepending a label -/

/-- Prepending a label to a frame, when the result is a frame. -/
noncomputable def coneF (v : ι) (F : Frame K f) : Frame K f →₀ ℤ := by
  classical
  exact if h : IsFrame K f (v :: F.1) then Finsupp.single ⟨v :: F.1, h⟩ 1 else 0

/-- Prepending a label. -/
noncomputable def cone (v : ι) : (Frame K f →₀ ℤ) →+ (Frame K f →₀ ℤ) :=
  Finsupp.liftAddHom (fun F => zmultiplesHom _ (coneF v F))

theorem cone_single (v : ι) (F : Frame K f) (n : ℤ) :
    cone v (Finsupp.single F n) = n • coneF v F := by
  simp [cone]

theorem coneF_of (v : ι) (F : Frame K f) (h : IsFrame K f (v :: F.1)) :
    coneF v F = Finsupp.single ⟨v :: F.1, h⟩ 1 := by
  simp [coneF, h]

/-- Frames to which `v` can be prepended. -/
def Free (v : ι) (F : Frame K f) : Prop := IsFrame K f (v :: F.1)

theorem Free.face {v : ι} {F : Frame K f} (h : Free v F) (i : ℕ) : Free v (face F i) := by
  unfold Free at h ⊢
  exact h.sublist (List.Sublist.cons_cons v (List.eraseIdx_sublist _ i))

theorem bd_cone_single (v : ι) (F : Frame K f) (h : Free v F) :
    bd (coneF v F) = Finsupp.single F 1 - cone v (faces F) := by
  rw [coneF_of v F h, bd_single, one_smul, faces]
  obtain ⟨l, hl⟩ := F
  simp only [List.length_cons]
  rw [Finset.sum_range_succ']
  have h0 : face (⟨v :: l, h⟩ : Frame K f) 0 = ⟨l, hl⟩ := Subtype.ext rfl
  rw [h0, pow_zero, one_smul, add_comm, faces, map_sum]
  simp only [sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [map_zsmul, cone_single, one_smul, coneF_of v _ ((show Free v (⟨l, hl⟩ : Frame K f) from h).face i),
    pow_succ, mul_neg_one, neg_smul]
  rfl

/-- Prepending is a chain homotopy on chains of frames to which `v` can be prepended. -/
theorem bd_cone (v : ι) (z : Frame K f →₀ ℤ) (hz : ∀ F ∈ z.support, Free v F) :
    bd (cone v z) = z - cone v (bd z) := by
  classical
  induction z using Finsupp.induction with
  | zero => simp
  | single_add F n z hF hn ih =>
    have hz' : ∀ G ∈ z.support, Free v G := by
      intro G hG
      apply hz
      have hGF : G ≠ F := fun e => hF (e ▸ hG)
      have e1 : (Finsupp.single F n + z) G = z G := by
        simp [Ne.symm hGF]
      rw [Finsupp.mem_support_iff, e1]
      exact Finsupp.mem_support_iff.mp hG
    have hFv : Free v F := hz F (by
      have hz0 : z F = 0 := Finsupp.notMem_support_iff.mp hF
      rw [Finsupp.mem_support_iff, Finsupp.add_apply, Finsupp.single_eq_same, hz0, add_zero]
      exact hn)
    rw [show bd (cone v (Finsupp.single F n + z)) = n • bd (coneF v F) + bd (cone v z) by
      rw [map_add, cone_single, map_add, map_zsmul]]
    rw [ih hz', bd_cone_single v F hFv, map_add, bd_single, map_add, map_zsmul, smul_sub,
      Finsupp.smul_single_one]
    abel

end Frames
end AllPrimeGroups
