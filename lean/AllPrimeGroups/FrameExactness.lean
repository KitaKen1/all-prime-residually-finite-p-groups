import AllPrimeGroups.FrameComplex

/-! Tools for manuscript Lemma 12.2: relabelling frames along injections, and splitting frames at a
label `v` into a prefix ending in `v` and a suffix independent modulo the prefix.

For a frame `P`, `app P` appends suffixes, which are frames of the labels other than `v` with
vectors taken modulo the span of `P`, and `proj P` reads them back. If every frame of a chain `x`
has `v` at position at most `|P| - 1`, then the part of `∂x` with prefix `P` is, up to the sign
`(-1)^{|P|}`, the boundary of the part of `x` with prefix `P` (`proj_bd`). -/

namespace AllPrimeGroups
namespace Frames

open Submodule Finset

variable {K : Type*} [Field K] {W : Type*} [AddCommGroup W] [Module K W] {ι : Type*} {f : ι → W}

/-! ### Degrees -/

/-- Chains of one length. -/
def Deg (k : ℕ) (z : Frame K f →₀ ℤ) : Prop := ∀ F ∈ z.support, F.1.length = k

theorem Deg.zero (k : ℕ) : Deg k (0 : Frame K f →₀ ℤ) := by
  intro F hF
  simp at hF

theorem Deg.add {k : ℕ} {x y : Frame K f →₀ ℤ} (hx : Deg k x) (hy : Deg k y) : Deg k (x + y) := by
  classical
  intro F hF
  exact (Finset.mem_union.mp (Finsupp.support_add hF)).elim (hx F) (hy F)

theorem Deg.neg {k : ℕ} {x : Frame K f →₀ ℤ} (hx : Deg k x) : Deg k (-x) := by
  intro F hF
  rw [Finsupp.support_neg] at hF
  exact hx F hF

theorem Deg.sub {k : ℕ} {x y : Frame K f →₀ ℤ} (hx : Deg k x) (hy : Deg k y) : Deg k (x - y) := by
  rw [sub_eq_add_neg]
  exact hx.add hy.neg

theorem Deg.zsmul {k : ℕ} {x : Frame K f →₀ ℤ} (hx : Deg k x) (n : ℤ) : Deg k (n • x) :=
  fun F hF => hx F (Finsupp.support_smul hF)

theorem Deg.single (F : Frame K f) (n : ℤ) : Deg F.1.length (Finsupp.single F n) := by
  intro G hG
  rw [Finset.mem_singleton.mp (Finsupp.support_single_subset hG)]

theorem Deg.sum {α : Type*} {k : ℕ} {s : Finset α} {g : α → Frame K f →₀ ℤ}
    (h : ∀ a ∈ s, Deg k (g a)) : Deg k (∑ a ∈ s, g a) := by
  classical
  intro F hF
  obtain ⟨a, ha, hF'⟩ := Finset.mem_biUnion.mp (Finsupp.support_finsetSum hF)
  exact h a ha F hF'

theorem Deg.faces (F : Frame K f) : Deg (F.1.length - 1) (faces F) := by
  apply Deg.sum
  intro i hi
  apply Deg.zsmul
  have := Deg.single (face F i) 1
  rwa [show (face F i).1.length = F.1.length - 1 from
    List.length_eraseIdx_of_lt (Finset.mem_range.mp hi)] at this

theorem Deg.bd {k : ℕ} {z : Frame K f →₀ ℤ} (hz : Deg (k + 1) z) : Deg k (bd z) := by
  classical
  induction z using Finsupp.induction with
  | zero => simp [Deg.zero]
  | single_add F n z hF hn ih =>
    have hF' : F.1.length = k + 1 := hz F (by
      have hz0 : z F = 0 := Finsupp.notMem_support_iff.mp hF
      rw [Finsupp.mem_support_iff, Finsupp.add_apply, Finsupp.single_eq_same, hz0, add_zero]
      exact hn)
    have hz' : Deg (k + 1) z := by
      intro G hG
      apply hz
      have hGF : G ≠ F := fun e => hF (e ▸ hG)
      have e1 : (Finsupp.single F n + z) G = z G := by simp [Ne.symm hGF]
      rw [Finsupp.mem_support_iff, e1]
      exact Finsupp.mem_support_iff.mp hG
    rw [map_add, bd_single]
    refine Deg.add (Deg.zsmul ?_ n) (ih hz')
    have := Deg.faces F
    rwa [hF', Nat.add_sub_cancel] at this

/-! ### Lists split at a label -/

theorem split_unique {α : Type*} {v : α} :
    ∀ {L₁ L₂ M₁ M₂ : List α}, v ∉ L₁ → v ∉ M₁ → L₁ ++ v :: L₂ = M₁ ++ v :: M₂ → L₁ = M₁ ∧ L₂ = M₂
  | [], L₂, [], M₂, _, _, h => by simpa using h
  | [], L₂, m :: M₁, M₂, _, hM, h => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
    exact absurd (h.1 ▸ List.mem_cons_self) hM
  | a :: L₁, L₂, [], M₂, hL, _, h => by
    simp only [List.cons_append, List.nil_append, List.cons.injEq] at h
    exact absurd (h.1 ▸ List.mem_cons_self) hL
  | a :: L₁, L₂, b :: M₁, M₂, hL, hM, h => by
    simp only [List.cons_append, List.cons.injEq] at h
    obtain ⟨e1, e2⟩ := split_unique (fun hv => hL (List.mem_cons_of_mem a hv))
      (fun hv => hM (List.mem_cons_of_mem b hv)) h.2
    exact ⟨by rw [h.1, e1], e2⟩

/-! ### Relabelling along an injection -/

section Relabel
variable {κ : Type*} {g : κ → ι} (hg : Function.Injective g)
include hg

theorem IsFrame.map {l : List κ} (h : IsFrame K (f ∘ g) l) : IsFrame K f (l.map g) := by
  refine ⟨h.1.map hg, ?_⟩
  have e : {x | x ∈ l.map g} = g '' {x | x ∈ l} := by
    ext x
    simp [List.mem_map]
  rw [e]
  exact h.2.image_of_comp g f

theorem IsFrame.of_map {l : List κ} (h : IsFrame K f (l.map g)) : IsFrame K (f ∘ g) l := by
  refine ⟨h.1.of_map g, ?_⟩
  have e : {x | x ∈ l.map g} = g '' {x | x ∈ l} := by
    ext x
    simp [List.mem_map]
  have h2 := h.2
  rw [e] at h2
  exact h2.comp_of_image hg.injOn

/-- Relabelling a frame along an injection. -/
def Frame.relabel (F : Frame K (f ∘ g)) : Frame K f := ⟨F.1.map g, F.2.map hg⟩

theorem Frame.relabel_injective : Function.Injective (Frame.relabel (K := K) (f := f) hg) := by
  intro F G h
  apply Subtype.ext
  exact (List.map_injective_iff.mpr hg) (congrArg Subtype.val h)

/-- Relabelling chains along an injection. -/
noncomputable def relabelC : (Frame K (f ∘ g) →₀ ℤ) →+ (Frame K f →₀ ℤ) :=
  Finsupp.mapDomain.addMonoidHom (Frame.relabel hg)

theorem relabelC_single (F : Frame K (f ∘ g)) (n : ℤ) :
    relabelC hg (Finsupp.single F n) = Finsupp.single (F.relabel hg) n :=
  Finsupp.mapDomain_single

theorem relabelC_injective : Function.Injective (relabelC (K := K) (f := f) hg) :=
  Finsupp.mapDomain_injective (Frame.relabel_injective hg)

theorem face_relabel (F : Frame K (f ∘ g)) (i : ℕ) : face (F.relabel hg) i = (face F i).relabel hg :=
  Subtype.ext (List.eraseIdx_map g F.1 i)

theorem bd_relabelC (z : Frame K (f ∘ g) →₀ ℤ) : bd (relabelC hg z) = relabelC hg (bd z) := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single F n =>
    have hl : (F.relabel hg).1.length = F.1.length := List.length_map _
    rw [relabelC_single, bd_single, bd_single, map_zsmul, faces, faces, hl, map_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [map_zsmul, relabelC_single, face_relabel]

theorem deg_relabelC {k : ℕ} {z : Frame K (f ∘ g) →₀ ℤ} (hz : Deg k z) : Deg k (relabelC hg z) := by
  classical
  intro F hF
  obtain ⟨G, hG, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hF)
  exact (List.length_map _).trans (hz G hG)

theorem deg_of_relabelC {k : ℕ} {z : Frame K (f ∘ g) →₀ ℤ} (hz : Deg k (relabelC hg z)) : Deg k z := by
  intro F hF
  have : F.relabel hg ∈ (relabelC hg z).support := by
    rw [Finsupp.mem_support_iff, relabelC, Finsupp.mapDomain.addMonoidHom_apply,
      Finsupp.mapDomain_apply_of_injective (Frame.relabel_injective hg)]
    exact Finsupp.mem_support_iff.mp hF
  exact (List.length_map _).symm.trans (hz _ this)

omit hg in
theorem exists_map_eq {l : List ι} (h : ∀ x ∈ l, x ∈ Set.range g) : ∃ l' : List κ, l'.map g = l := by
  induction l with
  | nil => exact ⟨[], rfl⟩
  | cons a l ih =>
    obtain ⟨b, hb⟩ := h a List.mem_cons_self
    obtain ⟨l', hl'⟩ := ih (fun x hx => h x (List.mem_cons_of_mem a hx))
    exact ⟨b :: l', by simp [hb, hl']⟩

/-- Chains whose labels lie in the image come from relabelled chains. -/
theorem exists_relabelC (z : Frame K f →₀ ℤ) (hz : ∀ F ∈ z.support, ∀ x ∈ F.1, x ∈ Set.range g) :
    ∃ z', relabelC hg z' = z := by
  classical
  induction z using Finsupp.induction with
  | zero => exact ⟨0, map_zero _⟩
  | single_add F n z hF hn ih =>
    have hz' : ∀ G ∈ z.support, ∀ x ∈ G.1, x ∈ Set.range g := by
      intro G hG
      apply hz
      have hGF : G ≠ F := fun e => hF (e ▸ hG)
      have e1 : (Finsupp.single F n + z) G = z G := by simp [Ne.symm hGF]
      rw [Finsupp.mem_support_iff, e1]
      exact Finsupp.mem_support_iff.mp hG
    have hFr : ∀ x ∈ F.1, x ∈ Set.range g := hz F (by
      have hz0 : z F = 0 := Finsupp.notMem_support_iff.mp hF
      rw [Finsupp.mem_support_iff, Finsupp.add_apply, Finsupp.single_eq_same, hz0, add_zero]
      exact hn)
    obtain ⟨z', hz'⟩ := ih hz'
    obtain ⟨l', hl'⟩ := exists_map_eq hFr
    have hF' : IsFrame K (f ∘ g) l' := IsFrame.of_map hg (hl' ▸ F.2)
    refine ⟨Finsupp.single ⟨l', hF'⟩ n + z', ?_⟩
    rw [map_add, relabelC_single, hz']
    congr 2
    exact Subtype.ext hl'

end Relabel

/-! ### Prefixes and suffixes -/

section Append
variable {κ : Type*} {g : κ → ι} (hg : Function.Injective g)

/-- Vectors modulo the span of a prefix. -/
abbrev fq (P : List ι) : κ → W ⧸ span K (f '' {x | x ∈ P}) :=
  (span K (f '' {x | x ∈ P})).mkQ ∘ f ∘ g

theorem set_append (P : List ι) (s : List κ) :
    {x | x ∈ P ++ s.map g} = {x | x ∈ P} ∪ g '' {y | y ∈ s} := by
  ext x
  simp only [Set.mem_ofPred_eq, List.mem_append, List.mem_map, Set.mem_union, Set.mem_image]

include hg

theorem IsFrame.append {P : List ι} (hP : IsFrame K f P) {s : List κ}
    (hs : IsFrame K (fq (K := K) (f := f) (g := g) P) s) : IsFrame K f (P ++ s.map g) := by
  have hdisj : ∀ x ∈ P, ∀ y ∈ s, x ≠ g y := by
    intro x hx y hy e
    have h0 : (fq (K := K) (f := f) (g := g) P) y = 0 := by
      simp only [fq, Function.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      rw [← e]
      exact subset_span ⟨x, hx, rfl⟩
    exact hs.2.ne_zero hy h0
  refine ⟨?_, ?_⟩
  · rw [List.nodup_append]
    refine ⟨hP.1, hs.1.map hg, ?_⟩
    intro x hx y hy
    obtain ⟨y', hy', rfl⟩ := List.mem_map.mp hy
    exact hdisj x hx y' hy'
  · rw [set_append, linearIndepOn_union_iff_quotient]
    · exact ⟨hP.2, hs.2.image_of_comp g _⟩
    · rw [Set.disjoint_left]
      rintro x hx ⟨y, hy, rfl⟩
      exact hdisj _ hx y hy rfl

theorem IsFrame.of_append {P : List ι} {s : List κ} (h : IsFrame K f (P ++ s.map g)) :
    IsFrame K (fq (K := K) (f := f) (g := g) P) s := by
  have hnd := h.1
  rw [List.nodup_append] at hnd
  refine ⟨hnd.2.1.of_map g, ?_⟩
  have h2 := h.2
  have hdisj : Disjoint {x | x ∈ P} (g '' {y | y ∈ s}) := by
    rw [Set.disjoint_left]
    rintro x hx ⟨y, hy, rfl⟩
    exact hnd.2.2 _ hx _ (List.mem_map_of_mem hy) rfl
  rw [set_append, linearIndepOn_union_iff_quotient hdisj] at h2
  exact h2.2.comp_of_image hg.injOn

variable (P : List ι) (hP : IsFrame K f P)

/-- Appending a suffix to a prefix. -/
def appF (s : Frame K (fq (K := K) (f := f) (g := g) P)) : Frame K f :=
  ⟨P ++ s.1.map g, hP.append hg s.2⟩

theorem appF_injective : Function.Injective (appF hg P hP) := by
  intro s t h
  apply Subtype.ext
  exact (List.map_injective_iff.mpr hg) (List.append_cancel_left (congrArg Subtype.val h))

/-- Appending suffixes to a prefix, on chains. -/
noncomputable def app : (Frame K (fq (K := K) (f := f) (g := g) P) →₀ ℤ) →+ (Frame K f →₀ ℤ) :=
  Finsupp.mapDomain.addMonoidHom (appF hg P hP)

/-- Reading the suffixes of the frames with a given prefix. -/
noncomputable def proj : (Frame K f →₀ ℤ) →+ (Frame K (fq (K := K) (f := f) (g := g) P) →₀ ℤ) :=
  Finsupp.comapDomain.addMonoidHom (appF_injective hg P hP)

theorem app_single (s : Frame K (fq (K := K) (f := f) (g := g) P)) (n : ℤ) :
    app hg P hP (Finsupp.single s n) = Finsupp.single (appF hg P hP s) n :=
  Finsupp.mapDomain_single

theorem proj_app (z : Frame K (fq (K := K) (f := f) (g := g) P) →₀ ℤ) :
    proj hg P hP (app hg P hP z) = z :=
  Finsupp.comapDomain_mapDomain _ (appF_injective hg P hP) z

theorem proj_single_appF (s : Frame K (fq (K := K) (f := f) (g := g) P)) (n : ℤ) :
    proj hg P hP (Finsupp.single (appF hg P hP s) n) = Finsupp.single s n := by
  rw [← app_single, proj_app]

theorem proj_single_of_notMem (F : Frame K f) (hF : ∀ s, appF hg P hP s ≠ F) (n : ℤ) :
    proj hg P hP (Finsupp.single F n) = 0 := by
  classical
  ext s
  simp only [proj, Finsupp.comapDomain.addMonoidHom_apply, Finsupp.comapDomain_apply,
    Finsupp.coe_zero, Pi.zero_apply]
  rw [Finsupp.single_apply]
  simp [Ne.symm (hF s)]

theorem proj_faces_appF (s : Frame K (fq (K := K) (f := f) (g := g) P))
    (hpre : ∀ i < P.length, ∀ t, appF hg P hP t ≠ face (appF hg P hP s) i) :
    proj hg P hP (faces (appF hg P hP s)) = (-1 : ℤ) ^ P.length • faces s := by
  have hl : (appF hg P hP s).1.length = P.length + s.1.length := by
    simp [appF]
  rw [faces, hl, Finset.sum_range_add, map_add, map_sum, map_sum]
  rw [Finset.sum_eq_zero (fun i hi => by
    rw [map_zsmul, proj_single_of_notMem hg P hP _ (hpre i (Finset.mem_range.mp hi)), smul_zero]),
    zero_add, faces, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hface : face (appF hg P hP s) (P.length + j) = appF hg P hP (face s j) := by
    apply Subtype.ext
    simp only [face, appF]
    rw [List.eraseIdx_append_of_length_le (by omega), Nat.add_sub_cancel_left, List.eraseIdx_map]
  rw [hface, map_zsmul, proj_single_appF, pow_add, mul_smul]

end Append

end Frames
end AllPrimeGroups
