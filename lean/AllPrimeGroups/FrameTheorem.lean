import AllPrimeGroups.FrameLemma

/-! Manuscript Lemma 12.2: the augmented ordered frame complex of a finite labeled collection of
vectors spanning a space of dimension `r` is exact in degrees at most `r - 2`
(`exact_of_finrank`).

Induction on the number of labels. Choose a label `v`. The relative part is killed one prefix at a
time (`rel`): for the frames with `v` at the largest position `A`, the suffixes after a prefix
`P = Q ++ [v]` form a cycle of the vectors modulo `P`, of smaller label count and rank at least
`r - |P|`; filling it removes that prefix. What remains avoids `v`: it is filled by induction if `v`
lies in the span of the other labels, and by prepending `v` otherwise. -/

namespace AllPrimeGroups
namespace Frames

open Submodule Finset Module

variable {K : Type*} [Field K]

section Closure
variable {W : Type*} [AddCommGroup W] [Module K W] {ι : Type*} {f : ι → W}

/-- No frame of the chain contains `v`. -/
def NoV (v : ι) (x : Frame K f →₀ ℤ) : Prop := ∀ F ∈ x.support, v ∉ F.1

theorem supp_add {x y : Frame K f →₀ ℤ} {F : Frame K f} (h : F ∈ (x + y).support) :
    F ∈ x.support ∨ F ∈ y.support := by
  classical
  exact Finset.mem_union.mp (Finsupp.support_add h)

theorem supp_sub {x y : Frame K f →₀ ℤ} {F : Frame K f} (h : F ∈ (x - y).support) :
    F ∈ x.support ∨ F ∈ y.support := by
  rw [sub_eq_add_neg] at h
  rcases supp_add h with h | h
  · exact Or.inl h
  · rw [Finsupp.support_neg] at h
    exact Or.inr h

theorem PosLe.sub {v : ι} {A : ℕ} {x y : Frame K f →₀ ℤ} (hx : PosLe v A x) (hy : PosLe v A y) :
    PosLe v A (x - y) := fun F hF => (supp_sub hF).elim (hx F) (hy F)

theorem PosLe.zsmul {v : ι} {A : ℕ} {x : Frame K f →₀ ℤ} (hx : PosLe v A x) (n : ℤ) :
    PosLe v A (n • x) := fun F hF => hx F (Finsupp.support_smul hF)

theorem NoV.sub {v : ι} {x y : Frame K f →₀ ℤ} (hx : NoV v x) (hy : NoV v y) : NoV v (x - y) :=
  fun F hF => (supp_sub hF).elim (hx F) (hy F)

theorem smul_neg_one_pow_eq_zero {M : Type*} [AddCommGroup M] {n : ℕ} {z : M}
    (h : (-1 : ℤ) ^ n • z = 0) : z = 0 := by
  have := congrArg (fun w => (-1 : ℤ) ^ n • w) h
  simp only [smul_smul, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_smul,
    smul_zero] at this
  exact this

end Closure

/-! ### The relative part -/

section Rel
variable {W : Type*} [AddCommGroup W] [Module K W] {ι : Type*} {f : ι → W}
  {κ : Type*} {g : κ → ι} (hg : Function.Injective g) {v : ι}
  (hgv : ∀ y, g y ≠ v) (hgr : ∀ x, x ≠ v → x ∈ Set.range g) (k : ℕ)
  (H : ∀ (Q : List ι) (_ : v ∉ Q) (_ : IsFrame K f (Q ++ [v])), Q.length < k →
    ∀ z : Frame K (fq (K := K) (f := f) (g := g) (Q ++ [v])) →₀ ℤ, Deg (k - Q.length - 1) z →
      (k - Q.length - 1 = 0 ∨ bd z = 0) → ∃ y, Deg (k - Q.length) y ∧ bd y = z)

/-- Frames with `v` at position exactly `A`. -/
def AtPos (v : ι) (A : ℕ) (F : Frame K f) : Prop :=
  ∃ L₁ L₂ : List ι, F.1 = L₁ ++ v :: L₂ ∧ L₁.length = A

include hgv in
/-- The boundary of appended chains has `v` at position `|Q|` only with prefix `Q ++ [v]`. -/
theorem prefix_of_mem_bd_app {Q : List ι} (hvQ : v ∉ Q) (hP : IsFrame K f (Q ++ [v]))
    (y : Frame K (fq (K := K) (f := f) (g := g) (Q ++ [v])) →₀ ℤ) {G : Frame K f}
    (hG : G ∈ (bd (app hg (Q ++ [v]) hP y)).support) {Q' M₂ : List ι} (hGQ : G.1 = Q' ++ v :: M₂)
    (hlen : Q'.length = Q.length) : Q' = Q := by
  classical
  obtain ⟨F, hF, i, rfl⟩ := mem_support_bd hG
  obtain ⟨s, -, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hF)
  have hvQ' := (split_of_nodup (face (appF hg (Q ++ [v]) hP s) i).2.1 hGQ).1
  simp only [face, appF, List.append_assoc, List.singleton_append] at hGQ
  rcases lt_trichotomy i Q.length with hi | hi | hi
  · rw [List.eraseIdx_append_of_lt_length hi] at hGQ
    obtain ⟨e, -⟩ := split_unique (fun hv => hvQ (List.mem_of_mem_eraseIdx hv)) hvQ' hGQ
    have := congrArg List.length e
    rw [List.length_eraseIdx_of_lt hi] at this
    omega
  · subst hi
    rw [List.eraseIdx_append_of_length_le le_rfl, Nat.sub_self, List.eraseIdx_cons_zero] at hGQ
    have : v ∈ Q ++ s.1.map g := hGQ ▸ List.mem_append_right Q' List.mem_cons_self
    rcases List.mem_append.mp this with h' | h'
    · exact absurd h' hvQ
    · obtain ⟨y, -, hy⟩ := List.mem_map.mp h'
      exact absurd hy (hgv y)
  · rw [List.eraseIdx_append_of_length_le hi.le] at hGQ
    obtain ⟨j, hj⟩ : ∃ j, i - Q.length = j + 1 := ⟨i - Q.length - 1, by omega⟩
    rw [hj, List.eraseIdx_cons_succ] at hGQ
    exact (split_unique hvQ hvQ' hGQ).1.symm

include hg hgv hgr H in
/-- Manuscript Lemma 12.2, relative vanishing: a chain whose boundary avoids `v` is homologous to a
chain avoiding `v`. -/
theorem rel (A : ℕ) : ∀ x : Frame K f →₀ ℤ, Deg k x →
    (∀ F ∈ x.support, ∀ L₁ L₂ : List ι, F.1 = L₁ ++ v :: L₂ → L₁.length < A) → NoV v (bd x) →
    ∃ y, Deg (k + 1) y ∧ NoV v (x - bd y) := by
  classical
  induction A with
  | zero =>
    intro x _ hpos _
    refine ⟨0, Deg.zero _, ?_⟩
    intro F hF hv
    rw [map_zero, sub_zero] at hF
    obtain ⟨L₁, L₂, hL⟩ := List.append_of_mem hv
    exact absurd (hpos F hF L₁ L₂ hL) (Nat.not_lt_zero _)
  | succ A ihA =>
    suffices hmain : ∀ n : ℕ, ∀ x : Frame K f →₀ ℤ,
        (x.support.filter (AtPos v A)).card ≤ n → Deg k x → PosLe v A x → NoV v (bd x) →
        ∃ y, Deg (k + 1) y ∧ NoV v (x - bd y) by
      intro x hx hpos hb
      exact hmain _ x le_rfl hx (fun F hF L₁ L₂ hL => Nat.lt_succ_iff.mp (hpos F hF L₁ L₂ hL)) hb
    intro n
    induction n with
    | zero =>
      intro x hcard hx hpos hb
      apply ihA x hx _ hb
      intro F hF L₁ L₂ hL
      have hle := hpos F hF L₁ L₂ hL
      rcases Nat.lt_or_eq_of_le hle with h | h
      · exact h
      · have : F ∈ x.support.filter (AtPos v A) := Finset.mem_filter.mpr ⟨hF, L₁, L₂, hL, h⟩
        rw [Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)] at this
        exact absurd this (Finset.notMem_empty _)
    | succ n ihn =>
      intro x hcard hx hpos hb
      by_cases hempty : x.support.filter (AtPos v A) = ∅
      · exact ihn x (by rw [hempty]; simp) hx hpos hb
      obtain ⟨F₀, hF₀⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
      obtain ⟨hF₀s, Q, L₂, hQ, hQlen⟩ := Finset.mem_filter.mp hF₀
      obtain ⟨hvQ, -⟩ := split_of_nodup F₀.2.1 hQ
      have hP : IsFrame K f (Q ++ [v]) := F₀.2.sublist (by
        rw [hQ, show Q ++ v :: L₂ = (Q ++ [v]) ++ L₂ by simp]
        exact List.sublist_append_left _ _)
      have hAk : A < k := by
        have := hx F₀ hF₀s
        rw [hQ, List.length_append, List.length_cons] at this
        omega
      set xP := proj hg (Q ++ [v]) hP x with hxP
      have hxPd : Deg (k - Q.length - 1) xP := by
        intro s hs
        have hmem : appF hg (Q ++ [v]) hP s ∈ x.support := by
          rw [Finsupp.mem_support_iff]
          have := Finsupp.mem_support_iff.mp hs
          simpa [xP, proj, Finsupp.comapDomain_apply] using this
        have := hx _ hmem
        simp only [appF, List.length_append, List.length_map, List.length_singleton] at this
        omega
      have hposx : PosLe v Q.length x := hQlen ▸ hpos
      have hcyc : bd xP = 0 := by
        have h1 := proj_bd hg hgv hgr hvQ hP x hposx
        rw [proj_eq_zero_of_free hg (Q ++ [v]) (by simp) hP _ hb] at h1
        exact smul_neg_one_pow_eq_zero h1.symm
      obtain ⟨yP, hyPd, hyP⟩ := H Q hvQ hP (hQlen ▸ hAk) xP hxPd (Or.inr hcyc)
      set x' := x - (-1 : ℤ) ^ (Q.length + 1) • bd (app hg (Q ++ [v]) hP yP) with hx'
      have happd : Deg (k + 1) (app hg (Q ++ [v]) hP yP) := by
        have := deg_app hg (Q ++ [v]) hP hyPd
        rwa [List.length_append, List.length_singleton,
          show Q.length + 1 + (k - Q.length) = k + 1 by omega] at this
      have hx'd : Deg k x' := hx.sub ((Deg.bd happd).zsmul _)
      have hx'pos : PosLe v A x' := hpos.sub
        ((hQlen ▸ (posLe_app hg hvQ hP yP).bd : PosLe v A _).zsmul _)
      have hx'b : bd x' = bd x := by
        rw [hx', map_sub, map_zsmul, bd_bd, smul_zero, sub_zero]
      have hprojx' : proj hg (Q ++ [v]) hP x' = 0 := by
        rw [hx', map_sub, map_zsmul,
          proj_bd hg hgv hgr hvQ hP _ (posLe_app hg hvQ hP yP), proj_app, hyP, smul_smul,
          ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_smul, sub_self]
      -- frames of `x'` at position `A` are frames of `x` other than those with prefix `Q ++ [v]`
      have hsub : x'.support.filter (AtPos v A) ⊆ (x.support.filter (AtPos v A)).erase F₀ := by
        intro G hG
        obtain ⟨hGs, Q', M₂, hGQ, hQ'len⟩ := Finset.mem_filter.mp hG
        have hQ'ne : Q' ≠ Q := by
          intro e
          subst e
          obtain ⟨hvQ', hvM⟩ := split_of_nodup G.2.1 hGQ
          have hM : ∀ x ∈ M₂, x ∈ Set.range g := fun x hx => hgr x (fun e' => hvM (e' ▸ hx))
          obtain ⟨t, ht⟩ := exists_map_eq hM
          have hGl : G.1 = (Q' ++ [v]) ++ t.map g := by rw [hGQ, ht]; simp
          have hGt : IsFrame K f ((Q' ++ [v]) ++ t.map g) := hGl ▸ G.2
          have hs := Finsupp.ext_iff.mp hprojx' ⟨t, IsFrame.of_append hg hGt⟩
          simp only [proj, Finsupp.comapDomain.addMonoidHom_apply, Finsupp.comapDomain_apply,
            Finsupp.coe_zero, Pi.zero_apply] at hs
          have hGeq : appF hg (Q' ++ [v]) hP ⟨t, IsFrame.of_append hg hGt⟩ = G :=
            Subtype.ext hGl.symm
          rw [hGeq] at hs
          exact Finsupp.mem_support_iff.mp hGs hs
        have hGx : G ∈ x.support := by
          rcases supp_sub hGs with h | h
          · exact h
          · exact absurd (prefix_of_mem_bd_app hg hgv hvQ hP yP (Finsupp.support_smul h) hGQ
              (hQ'len.trans hQlen.symm)) hQ'ne
        refine Finset.mem_erase.mpr ⟨?_, Finset.mem_filter.mpr ⟨hGx, Q', M₂, hGQ, hQ'len⟩⟩
        intro hGF
        apply hQ'ne
        rw [hGF] at hGQ
        exact (split_unique (split_of_nodup F₀.2.1 hGQ).1 hvQ (hGQ.symm.trans hQ)).1
      have hcard' : (x'.support.filter (AtPos v A)).card ≤ n := by
        have := Finset.card_le_card hsub
        rw [Finset.card_erase_of_mem hF₀] at this
        omega
      obtain ⟨y', hy'd, hy'⟩ := ihn x' hcard' hx'd hx'pos (hx'b ▸ hb)
      refine ⟨(-1 : ℤ) ^ (Q.length + 1) • app hg (Q ++ [v]) hP yP + y', (happd.zsmul _).add hy'd, ?_⟩
      have e : x - bd ((-1 : ℤ) ^ (Q.length + 1) • app hg (Q ++ [v]) hP yP + y') = x' - bd y' := by
        rw [hx', map_add, map_zsmul]
        abel
      rw [e]
      exact hy'

end Rel

/-! ### The theorem -/

theorem exists_ne_zero_of_finrank_pos {W : Type*} [AddCommGroup W] [Module K W] {ι : Type*}
    {f : ι → W} (h : 0 < finrank K (span K (Set.range f))) : ∃ u, f u ≠ 0 := by
  by_contra hc
  simp only [not_exists, not_not] at hc
  have h0 : span K (Set.range f) = ⊥ := by
    rw [Submodule.span_eq_bot]
    rintro _ ⟨u, rfl⟩
    exact hc u
  rw [h0, finrank_bot] at h
  exact lt_irrefl _ h

universe u w

theorem exact_aux (N : ℕ) : ∀ {ι : Type u} [Finite ι] {W : Type w} [AddCommGroup W] [Module K W]
    (f : ι → W), Nat.card ι = N → ∀ k : ℕ, k + 1 ≤ finrank K (span K (Set.range f)) →
    ∀ z : Frame K f →₀ ℤ, Deg k z → (k = 0 ∨ bd z = 0) → ∃ y, Deg (k + 1) y ∧ bd y = z := by
  induction N using Nat.strong_induction_on with
  | _ N IH =>
  intro ι _ W _ _ f hN k hk z hz hcyc
  classical
  obtain ⟨u, hu⟩ := exists_ne_zero_of_finrank_pos (K := K) (f := f) (by omega)
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · have hnil : IsFrame K f ([] : List ι) := isFrame_nil
    have hu1 : IsFrame K f [u] := isFrame_cons.mpr ⟨List.not_mem_nil, hnil, by simpa using hu⟩
    refine ⟨z ⟨[], hnil⟩ • Finsupp.single ⟨[u], hu1⟩ 1,
      (Deg.single (⟨[u], hu1⟩ : Frame K f) 1).zsmul _, ?_⟩
    rw [map_zsmul, bd_single, one_smul]
    have hfaces : faces (⟨[u], hu1⟩ : Frame K f) = Finsupp.single ⟨[], hnil⟩ 1 := by
      rw [faces, show ([u] : List ι).length = 1 from rfl, Finset.sum_range_one, pow_zero, one_smul]
      rfl
    rw [hfaces, Finsupp.smul_single_one]
    ext G
    by_cases hG : G = ⟨[], hnil⟩
    · subst hG
      simp
    · have hzG : z G = 0 := by
        by_contra h
        have := hz G (Finsupp.mem_support_iff.mpr h)
        exact hG (Subtype.ext (List.length_eq_zero_iff.mp this))
      rw [hzG, Finsupp.single_apply]
      simp [Ne.symm hG]
  · have hb : bd z = 0 := hcyc.resolve_left (by omega)
    have hg : Function.Injective (Subtype.val : {i : ι // i ≠ u} → ι) := Subtype.val_injective
    have hgv : ∀ y : {i : ι // i ≠ u}, (y : ι) ≠ u := fun y => y.2
    have hgr : ∀ x, x ≠ u → x ∈ Set.range (Subtype.val : {i : ι // i ≠ u} → ι) :=
      fun x hx => ⟨⟨x, hx⟩, rfl⟩
    have hcard : Nat.card {i : ι // i ≠ u} < N :=
      hN ▸ Finite.card_subtype_lt (p := fun i => i ≠ u) (x := u) (by simp)
    have H : ∀ (Q : List ι) (_ : u ∉ Q) (_ : IsFrame K f (Q ++ [u])), Q.length < k →
        ∀ z' : Frame K (fq (K := K) (f := f) (g := (Subtype.val : {i : ι // i ≠ u} → ι))
          (Q ++ [u])) →₀ ℤ, Deg (k - Q.length - 1) z' → (k - Q.length - 1 = 0 ∨ bd z' = 0) →
          ∃ y, Deg (k - Q.length) y ∧ bd y = z' := by
      intro Q _ _ hQk z' hz' hc'
      have hrank := finrank_le_fq (K := K) (f := f) hg hgr (Q ++ [u]) (by simp)
      rw [List.length_append, List.length_singleton] at hrank
      obtain ⟨y, hy, hby⟩ := IH (Nat.card {i : ι // i ≠ u}) hcard
        (fq (K := K) (f := f) (g := (Subtype.val : {i : ι // i ≠ u} → ι)) (Q ++ [u])) rfl
        (k - Q.length - 1) (by omega) z' hz' hc'
      exact ⟨y, by rwa [show k - Q.length - 1 + 1 = k - Q.length by omega] at hy, hby⟩
    obtain ⟨y₁, hy₁, hfree⟩ := rel hg hgv hgr k H k z hz (fun F hF L₁ L₂ hL => by
        have := hz F hF
        rw [hL, List.length_append, List.length_cons] at this
        omega)
      (by
        rw [hb]
        intro F hF
        simp at hF)
    set z₁ := z - bd y₁ with hz₁
    have hz₁d : Deg k z₁ := hz.sub (Deg.bd hy₁)
    have hz₁b : bd z₁ = 0 := by rw [hz₁, map_sub, hb, bd_bd, sub_zero]
    obtain ⟨z', hz'⟩ := exists_relabelC hg z₁
      (fun F hF x hx => hgr x (fun e => hfree F hF (e ▸ hx)))
    by_cases hv : f u ∈ span K (Set.range (f ∘ (Subtype.val : {i : ι // i ≠ u} → ι)))
    · have hspan : span K (Set.range f) =
          span K (Set.range (f ∘ (Subtype.val : {i : ι // i ≠ u} → ι))) := by
        apply le_antisymm
        · rw [span_le]
          rintro _ ⟨i, rfl⟩
          by_cases hi : i = u
          · subst hi
            exact hv
          · exact subset_span ⟨⟨i, hi⟩, rfl⟩
        · apply span_mono
          rintro _ ⟨y, rfl⟩
          exact ⟨y.1, rfl⟩
      have hz'd : Deg k z' := deg_of_relabelC hg (hz' ▸ hz₁d)
      have hz'b : bd z' = 0 :=
        relabelC_injective hg (by rw [← bd_relabelC, hz', hz₁b, map_zero])
      obtain ⟨y', hy'd, hy'⟩ := IH (Nat.card {i : ι // i ≠ u}) hcard
        (f ∘ (Subtype.val : {i : ι // i ≠ u} → ι)) rfl k (by rw [← hspan]; exact hk) z' hz'd
        (Or.inr hz'b)
      refine ⟨y₁ + relabelC hg y', hy₁.add (deg_relabelC hg hy'd), ?_⟩
      rw [map_add, bd_relabelC, hy', hz', hz₁]
      abel
    · have hfr : ∀ F ∈ z₁.support, Free u F := by
        intro F hF
        refine isFrame_cons.mpr ⟨hfree F hF, F.2, fun hmem => hv ?_⟩
        refine span_mono ?_ hmem
        rintro _ ⟨x, hx, rfl⟩
        exact ⟨⟨x, fun e => hfree F hF (e ▸ hx)⟩, rfl⟩
      refine ⟨y₁ + cone u z₁, hy₁.add (deg_cone u hz₁d), ?_⟩
      rw [map_add, bd_cone u z₁ hfr, hz₁b, map_zero, sub_zero, hz₁]
      abel

/-- Manuscript Lemma 12.2 for finitely many labels: cycles of degree at most `r - 2` bound, where
`r` is the dimension spanned by the vectors. -/
theorem exact_of_finrank {ι : Type u} [Finite ι] {W : Type w} [AddCommGroup W] [Module K W]
    (f : ι → W) (k : ℕ) (hk : k + 1 ≤ finrank K (span K (Set.range f))) (z : Frame K f →₀ ℤ)
    (hz : Deg k z) (hcyc : k = 0 ∨ bd z = 0) : ∃ y, Deg (k + 1) y ∧ bd y = z :=
  exact_aux _ f rfl k hk z hz hcyc

/-- Manuscript Lemma 12.2 for arbitrary labels containing `r` labels with independent vectors. -/
theorem exact_of_independent {ι : Type u} {W : Type w} [AddCommGroup W] [Module K W] (f : ι → W)
    {r : ℕ} (b : Fin r → ι) (hb : LinearIndependent K (f ∘ b)) (k : ℕ) (hk : k + 1 ≤ r)
    (z : Frame K f →₀ ℤ) (hz : Deg k z) (hcyc : k = 0 ∨ bd z = 0) :
    ∃ y, Deg (k + 1) y ∧ bd y = z := by
  classical
  let S : Finset ι := z.support.biUnion (fun F => F.1.toFinset) ∪ Finset.univ.image b
  have hg : Function.Injective (Subtype.val : S → ι) := Subtype.val_injective
  obtain ⟨zS, hzS⟩ := exists_relabelC hg z (fun F hF x hx =>
    ⟨⟨x, Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨F, hF, List.mem_toFinset.mpr hx⟩)⟩, rfl⟩)
  let b' : Fin r → S := fun i =>
    ⟨b i, Finset.mem_union_right _ (Finset.mem_image_of_mem b (Finset.mem_univ i))⟩
  have hb' : LinearIndependent K ((f ∘ (Subtype.val : S → ι)) ∘ b') := hb
  have : FiniteDimensional K (span K (Set.range (f ∘ (Subtype.val : S → ι)))) :=
    FiniteDimensional.span_of_finite K (Set.finite_range _)
  have hrank : r ≤ finrank K (span K (Set.range (f ∘ (Subtype.val : S → ι)))) := by
    calc r = finrank K (span K (Set.range ((f ∘ (Subtype.val : S → ι)) ∘ b'))) := by
          rw [finrank_span_eq_card hb', Fintype.card_fin]
      _ ≤ _ := Submodule.finrank_mono (span_mono (Set.range_comp_subset_range _ _))
  obtain ⟨yS, hyS, hbS⟩ := exact_of_finrank (f ∘ (Subtype.val : S → ι)) k (hk.trans hrank) zS
    (deg_of_relabelC hg (hzS ▸ hz))
    (hcyc.imp id (fun h => relabelC_injective hg (by rw [← bd_relabelC, hzS, h, map_zero])))
  exact ⟨relabelC hg yS, deg_relabelC hg hyS, by rw [bd_relabelC, hbS, hzS]⟩

end Frames
end AllPrimeGroups
