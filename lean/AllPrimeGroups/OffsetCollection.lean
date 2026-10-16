import AllPrimeGroups.LongRepresentatives
import AllPrimeGroups.SeparationCriterion

/-! Collection of the cyclic evaluation by phase offsets (manuscript Proposition 21.2, its
group-theoretic part).

Words carry start and end phases modulo m with `τ w = σ w + |w|`. Assume that a product of two
words vanishes when the end phase of the first differs from the start phase of the second, and
that opposite roots commute when their parameters have such a vanishing product and mismatched
outer phases (the zero alternative of manuscript Lemma 20.2). Then the graded evaluation at the
cyclic shift of size m of a root word in such words is the product, over the m offsets a, of the
words `∏ x_{(i,σ(w)+a),(j,τ(w)+a)}(w)`. Each of them is a coordinate permutation of the offset
zero word, so stably the evaluation is the m-th power of the offset zero word.

That the offset zero word represents the original element is manuscript Lemma 21.1. It is not
proved here, and none of the hypotheses above is proved here for the constructed algebra. -/

namespace AllPrimeGroups
noncomputable section

section Interchange
variable {G : Type*} [Group G]

/-- Two products over the same list can be merged entrywise when entries with different indices
commute. -/
theorem list_prod_mul_prod {κ : Type*} (K : List κ) (hK : K.Nodup) (x y : κ → G)
    (h : ∀ a ∈ K, ∀ b ∈ K, a ≠ b → Commute (x a) (y b)) :
    (K.map x).prod * (K.map y).prod = (K.map (fun a => x a * y a)).prod := by
  induction K with
  | nil => simp
  | cons a K ih =>
    rw [List.nodup_cons] at hK
    have hc : Commute (K.map x).prod (y a) := by
      apply Commute.list_prod_left
      intro g hg
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hg
      exact h b (List.mem_cons.mpr (Or.inr hb)) a (List.mem_cons.mpr (Or.inl rfl))
        (fun he => hK.1 (he ▸ hb))
    have ih' := ih hK.2 (fun a ha b hb hab =>
      h a (List.mem_cons.mpr (Or.inr ha)) b (List.mem_cons.mpr (Or.inr hb)) hab)
    simp only [List.map_cons, List.prod_cons]
    rw [← ih']
    calc x a * (K.map x).prod * (y a * (K.map y).prod)
        = x a * (((K.map x).prod * y a) * (K.map y).prod) := by simp only [mul_assoc]
      _ = x a * ((y a * (K.map x).prod) * (K.map y).prod) := by rw [hc.eq]
      _ = x a * y a * ((K.map x).prod * (K.map y).prod) := by simp only [mul_assoc]

/-- A double product can be interchanged when entries in different columns commute. -/
theorem list_prod_interchange {ι κ : Type*} (L : List ι) (K : List κ) (hK : K.Nodup)
    (f : ι → κ → G)
    (hf : ∀ i ∈ L, ∀ j ∈ L, ∀ a ∈ K, ∀ b ∈ K, a ≠ b → Commute (f i a) (f j b)) :
    (L.map (fun i => (K.map (f i)).prod)).prod =
      (K.map (fun a => (L.map (fun i => f i a)).prod)).prod := by
  induction L with
  | nil => simp
  | cons i L ih =>
    have ih' := ih (fun i hi j hj => hf i (List.mem_cons.mpr (Or.inr hi)) j
      (List.mem_cons.mpr (Or.inr hj)))
    simp only [List.map_cons, List.prod_cons]
    rw [ih']
    apply list_prod_mul_prod K hK (f i) (fun a => (L.map (fun j => f j a)).prod)
    intro a ha b hb hab
    apply Commute.list_prod_right
    intro g hg
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hg
    exact hf i (List.mem_cons.mpr (Or.inl rfl)) j (List.mem_cons.mpr (Or.inr hj)) a ha b hb hab

end Interchange

namespace Kernel
open Classical

section Roots
variable {k : ℕ} {R : Type*} [Ring R]

theorem root_eq {A B : Root k} (h₁ : A.row = B.row) (h₂ : A.col = B.col) : A = B := by
  obtain ⟨i, j, _⟩ := A
  obtain ⟨i', j', _⟩ := B
  dsimp only at h₁ h₂
  subst h₁
  subst h₂
  rfl

/-- Two roots commute when the products of their parameters vanish in each order that the
Steinberg relations can see, and when they commute in the opposite position. -/
theorem commute_roots (A B : Root k) (a b : R)
    (h₁ : A.col = B.row → A.row ≠ B.col → a * b = 0)
    (h₂ : A.row = B.col → A.col ≠ B.row → b * a = 0)
    (h₃ : A.col = B.row → A.row = B.col → Commute (Steinberg.x A a) (Steinberg.x B b)) :
    Commute (Steinberg.x A a) (Steinberg.x B b) := by
  by_cases hc : A.col = B.row
  · by_cases hr : A.row = B.col
    · exact h₃ hc hr
    · have h0 := h₁ hc hr
      obtain ⟨i, j, hij⟩ := A
      obtain ⟨j', l, hjl⟩ := B
      dsimp only at hc hr h0
      subst hc
      rw [← bracket_eq_one_iff, Steinberg.x_mul i j l hij hjl hr a b, h0, Steinberg.x_zero]
  · by_cases hr : A.row = B.col
    · have h0 := h₂ hr hc
      obtain ⟨i, j, hij⟩ := A
      obtain ⟨l, i', hli⟩ := B
      dsimp only at hc hr h0
      subst hr
      apply Commute.symm
      rw [← bracket_eq_one_iff, Steinberg.x_mul l i j hli hij (Ne.symm hc) b a, h0,
        Steinberg.x_zero]
    · exact Steinberg.x_commute A B hc hr a b

/-- A root and a root in the opposite position. -/
theorem commute_opposite (A B : Root k) (a b : R) (hc : A.col = B.row) (hr : A.row = B.col)
    (h : Commute (Steinberg.x A a) (Steinberg.x ⟨A.col, A.row, A.ne.symm⟩ b)) :
    Commute (Steinberg.x A a) (Steinberg.x B b) := by
  obtain ⟨i, j, hij⟩ := A
  obtain ⟨j', i', hji⟩ := B
  dsimp only at hc hr h
  subst hc
  subst hr
  exact h

end Roots

section Blocks
variable {ℓ : ℕ} [Fact ℓ.Prime] {n m : ℕ} {R : Type*} [Ring R] [Algebra (ZMod ℓ) R]

theorem blockIndex_inner_eq {i j : Fin n} {s t : Fin m} (h : blockIndex i s = blockIndex j t) :
    s = t :=
  congrArg Prod.snd (finProdFinEquiv.injective h)

theorem blockRoot_list_sum (p : Root n) (l : List (Matrix (Fin m) (Fin m) R)) :
    blockRoot p l.sum = (l.map (blockRoot p)).prod := by
  induction l with
  | nil => simp [blockRoot_zero]
  | cons A l ih => simp [List.sum_cons, blockRoot_add, ih]

variable [NeZero m]

/-- The evaluation of a monomial at the cyclic shift as a sum over offsets. -/
theorem cyclic_monomial_eq_sum (w : R) (s t : Fin m) (b : ℕ) (hst : t = s + Fin.ofNat m b) :
    matrixEval (cyclicShift m (ZMod ℓ)) (Polynomial.monomial b w) =
      ((List.finRange m).map (fun a => Matrix.single (s + a) (t + a) w)).sum := by
  ext u v
  rw [cyclic_eval_monomial (ℓ := ℓ) (NeZero.pos m), ← Fin.sum_univ_def, Matrix.sum_apply]
  simp only [Matrix.single_apply]
  rw [Finset.sum_eq_single (u - s)]
  · have hu : s + (u - s) = u := by abel
    have hv : t + (u - s) = u + Fin.ofNat m b := by rw [hst]; abel
    have hiff : u + Fin.ofNat m b = v ↔ (u.val + b) % m = v.val := by
      rw [Fin.ext_iff, Fin.val_add, Fin.val_ofNat, Nat.add_mod_mod]
    simp only [hu, hv, true_and, hiff]
  · intro a _ ha
    have hne : s + a ≠ u := by
      intro he
      apply ha
      rw [← he]
      abel
    simp [hne]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The block root of a cyclic monomial evaluation is the product of its offset factors. -/
theorem blockRoot_cyclic_monomial (p : Root n) (w : R) (s t : Fin m) (b : ℕ)
    (hst : t = s + Fin.ofNat m b) :
    blockRoot p (matrixEval (cyclicShift m (ZMod ℓ)) (Polynomial.monomial b w)) =
      ((List.finRange m).map (fun a => Steinberg.x (blockPosition p (s + a, t + a)) w)).prod := by
  rw [cyclic_monomial_eq_sum (ℓ := ℓ) w s t b hst, blockRoot_list_sum, List.map_map]
  congr 1
  apply List.map_congr_left
  intro a _
  exact blockRoot_single p (s + a) (t + a) w

end Blocks

theorem rootWord_cons {n : ℕ} {R : Type*} [Ring R] (qa : Root n × R) (l : List (Root n × R)) :
    rootWord (qa :: l) = Steinberg.x qa.1 qa.2 * rootWord l := by
  simp [rootWord]

theorem map_rootWord {n : ℕ} {R S : Type*} [Ring R] [Ring S] (f : R →+* S)
    (l : List (Root n × R)) :
    Steinberg.map f (rootWord l) = rootWord (l.map (fun qa => (qa.1, f qa.2))) := by
  induction l with
  | nil => simp [rootWord]
  | cons qa l ih =>
    rw [List.map_cons, rootWord_cons, rootWord_cons, map_mul, Steinberg.map_x, ih]

/-- Start and end phases modulo m on a set of words, with the end phase equal to the start
phase plus the length, and vanishing of products with mismatched middle phases. -/
structure CyclicPhases (R : Type*) [Ring R] (m : ℕ) [NeZero m] where
  W : Set R
  σ : R → Fin m
  τ : R → Fin m
  len : R → ℕ
  len_phase : ∀ w ∈ W, τ w = σ w + Fin.ofNat m (len w)
  mul_eq_zero : ∀ w ∈ W, ∀ w' ∈ W, τ w ≠ σ w' → w * w' = 0

namespace CyclicPhases
variable {ℓ : ℕ} [Fact ℓ.Prime] {n m : ℕ} [NeZero m] {R : Type*} [Ring R]
variable (P : CyclicPhases R m)

/-- The factor of a root in a given offset. -/
def offsetFactor (a : Fin m) (qa : Root n × R) : Steinberg (n * m) R :=
  Steinberg.x (blockPosition qa.1 (P.σ qa.2 + a, P.τ qa.2 + a)) qa.2

/-- The word of a given offset. -/
def offsetWord (l : List (Root n × R)) (a : Fin m) : Steinberg (n * m) R :=
  (l.map (P.offsetFactor a)).prod

/-- The opposite-root hypothesis: the zero alternative of manuscript Lemma 20.2. -/
def OppositeCommute (k : ℕ) : Prop :=
  ∀ (i j : Fin k) (hij : i ≠ j), ∀ w ∈ P.W, ∀ w' ∈ P.W, P.σ w ≠ P.τ w' → w * w' = 0 →
    Commute (Steinberg.x ⟨i, j, hij⟩ w) (Steinberg.x ⟨j, i, hij.symm⟩ w')

theorem offsetFactor_commute (hopp : P.OppositeCommute (n * m)) (qa qb : Root n × R)
    (ha : qa.2 ∈ P.W) (hb : qb.2 ∈ P.W) {a b : Fin m} (hab : a ≠ b) :
    Commute (P.offsetFactor a qa) (P.offsetFactor b qb) := by
  apply commute_roots
  · intro hc _
    apply P.mul_eq_zero _ ha _ hb
    have he : P.τ qa.2 + a = P.σ qb.2 + b := blockIndex_inner_eq hc
    intro h
    rw [h] at he
    exact hab (add_left_cancel he)
  · intro hr _
    apply P.mul_eq_zero _ hb _ ha
    have he : P.σ qa.2 + a = P.τ qb.2 + b := blockIndex_inner_eq hr
    intro h
    rw [← h] at he
    exact hab (add_left_cancel he)
  · intro hc hr
    apply commute_opposite _ _ _ _ hc hr
    apply hopp _ _ _ _ ha _ hb
    · have he : P.σ qa.2 + a = P.τ qb.2 + b := blockIndex_inner_eq hr
      intro h
      rw [h] at he
      exact hab (add_left_cancel he)
    · apply P.mul_eq_zero _ ha _ hb
      have he : P.τ qa.2 + a = P.σ qb.2 + b := blockIndex_inner_eq hc
      intro h
      rw [h] at he
      exact hab (add_left_cancel he)

variable [Algebra (ZMod ℓ) R]

/-- The graded evaluation at the cyclic shift is the product of the offset words. -/
theorem cyclic_eval_eq_offsets (γ : R →+* Polynomial R)
    (hγ : ∀ w ∈ P.W, γ w = Polynomial.monomial (P.len w) w)
    (hopp : P.OppositeCommute (n * m)) (l : List (Root n × R)) (hl : ∀ qa ∈ l, qa.2 ∈ P.W) :
    matrixSteinbergEval (cyclicShift m (ZMod ℓ)) (Steinberg.map γ (rootWord l)) =
      ((List.finRange m).map (P.offsetWord l)).prod := by
  rw [map_rootWord, rootWord, map_list_prod, List.map_map, List.map_map]
  calc _ = (l.map (fun qa => ((List.finRange m).map (fun a => P.offsetFactor a qa)).prod)).prod := by
        congr 1
        apply List.map_congr_left
        intro qa hqa
        simp only [Function.comp_apply, matrixSteinbergEval_x, hγ qa.2 (hl qa hqa)]
        exact blockRoot_cyclic_monomial (ℓ := ℓ) qa.1 qa.2 (P.σ qa.2) (P.τ qa.2) (P.len qa.2)
          (P.len_phase qa.2 (hl qa hqa))
    _ = ((List.finRange m).map (fun a => (l.map (fun qa => P.offsetFactor a qa)).prod)).prod :=
        list_prod_interchange l (List.finRange m) (List.nodup_finRange m)
          (fun qa a => P.offsetFactor a qa) (fun qa hqa qb hqb a _ b _ hab =>
            P.offsetFactor_commute hopp qa qb (hl qa hqa) (hl qb hqb) hab)
    _ = _ := rfl

/-- Shifting all inner indices by `b`. -/
def innerShift (b : Fin m) : Equiv.Perm (Fin (n * m)) :=
  finProdFinEquiv.symm.trans
    ((Equiv.prodCongr (Equiv.refl (Fin n)) (Equiv.addRight b)).trans finProdFinEquiv)

theorem innerShift_blockIndex (b : Fin m) (i : Fin n) (s : Fin m) :
    innerShift b (blockIndex i s) = blockIndex i (s + b) := by
  simp [innerShift, blockIndex]

/-- The offset words are coordinate permutations of each other. -/
theorem offsetWord_shift (l : List (Root n × R)) (a b : Fin m) :
    Steinberg.coordinateMap (innerShift b) (innerShift b).injective (P.offsetWord l a) =
      P.offsetWord l (a + b) := by
  rw [offsetWord, offsetWord, map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro qa _
  simp only [Function.comp, offsetFactor, Steinberg.coordinateMap_x]
  congr 1
  apply root_eq
  · change innerShift b (blockIndex qa.1.row (P.σ qa.2 + a)) = blockIndex qa.1.row _
    rw [innerShift_blockIndex, add_assoc]
  · change innerShift b (blockIndex qa.1.col (P.τ qa.2 + a)) = blockIndex qa.1.col _
    rw [innerShift_blockIndex, add_assoc]

end CyclicPhases
end Kernel

namespace Stable
variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime] {R : Type*} [Ring R] [hR : Algebra (ZMod ℓ) R]

include hℓ hR in
/-- Every permutation of the coordinates fixes a matrix-kernel element stably. -/
theorem of_coordinatePerm {k : ℕ} (hk : 3 ≤ k) (π : Equiv.Perm (Fin k)) (u : Steinberg k R)
    (hu : Elementary.representation u = 1) :
    of R k (Steinberg.coordinateMap π π.injective u) = of R k u := by
  have hkk : k ≤ k + 2 := by omega
  have hf : Function.Injective (Fin.castLE hkk) := Fin.castLE_injective hkk
  obtain ⟨ρ, hρ⟩ := Equiv.Perm.exists_extending_pair (Fin.castLE hkk) (Fin.castLE hkk ∘ π) hf
    (hf.comp π.injective)
  have hc : (⟨k, by omega⟩ : Fin (k + 2)) ≠ ⟨k + 1, by omega⟩ := by
    intro h
    have hv : k = k + 1 := congrArg Fin.val h
    omega
  have hf₀ (i : Fin k) : Fin.castLE hkk i ≠ ⟨k, by omega⟩ := by
    intro h
    have hv : i.val = k := congrArg Fin.val h
    omega
  have hf₁ (i : Fin k) : Fin.castLE hkk i ≠ ⟨k + 1, by omega⟩ := by
    intro h
    have hv : i.val = k + 1 := congrArg Fin.val h
    omega
  obtain ⟨ρ', hsign, hρ'⟩ : ∃ ρ' : Equiv.Perm (Fin (k + 2)),
      Equiv.Perm.sign ρ' = 1 ∧ ∀ i, ρ' (Fin.castLE hkk i) = Fin.castLE hkk (π i) := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign ρ) with h1 | h1
    · exact ⟨ρ, h1, hρ⟩
    · refine ⟨ρ * Equiv.swap ⟨k, by omega⟩ ⟨k + 1, by omega⟩, ?_, ?_⟩
      · rw [Equiv.Perm.sign_mul, h1, Equiv.Perm.sign_swap hc]
        simp
      · intro i
        rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne (hf₀ i) (hf₁ i)]
        exact hρ i
  have hvz := of_castLE R hkk u
  have hv : Elementary.representation
      (Steinberg.coordinateMap (Fin.castLE hkk) (Fin.castLE_injective hkk) u) = 1 := by
    apply finite_matrix_kernel R (k + 2)
    rw [hvz, representation_of, hu, map_one]
  have he := Kernel.stable_permutation_fixed (ℓ := ℓ) (R := R) (by omega : 3 ≤ k + 2) ρ' hsign
    _ hv
  have hcomp : Steinberg.coordinateMap ρ' ρ'.injective
      (Steinberg.coordinateMap (Fin.castLE hkk) (Fin.castLE_injective hkk) u) =
      Steinberg.coordinateMap (Fin.castLE hkk) (Fin.castLE_injective hkk)
        (Steinberg.coordinateMap π π.injective u) := by
    have H : (Steinberg.coordinateMap (R := R) ρ' ρ'.injective).comp
        (Steinberg.coordinateMap (Fin.castLE hkk) (Fin.castLE_injective hkk)) =
        (Steinberg.coordinateMap (Fin.castLE hkk) (Fin.castLE_injective hkk)).comp
          (Steinberg.coordinateMap π π.injective) := by
      apply Steinberg.hom_ext
      intro p a
      simp only [MonoidHom.comp_apply, Steinberg.coordinateMap_x]
      congr 1
      exact Kernel.root_eq (hρ' p.row) (hρ' p.col)
    exact DFunLike.congr_fun H u
  calc of R k (Steinberg.coordinateMap π π.injective u)
      = of R (k + 2) (Steinberg.coordinateMap (Fin.castLE hkk) (Fin.castLE_injective hkk)
          (Steinberg.coordinateMap π π.injective u)) := (of_castLE R hkk _).symm
    _ = of R (k + 2 + 1) (Kernel.padSteinberg (Steinberg.coordinateMap (Fin.castLE hkk)
          (Fin.castLE_injective hkk) (Steinberg.coordinateMap π π.injective u))) :=
        (Chain.of_step (steinbergStep R) (k + 2) _).symm
    _ = of R (k + 2 + 1) (Kernel.padSteinberg (Steinberg.coordinateMap (Fin.castLE hkk)
          (Fin.castLE_injective hkk) u)) := by rw [← hcomp, he]
    _ = of R (k + 2) (Steinberg.coordinateMap (Fin.castLE hkk) (Fin.castLE_injective hkk) u) :=
        Chain.of_step (steinbergStep R) (k + 2) _
    _ = of R k u := hvz

/-- Manuscript Proposition 21.2 up to Lemma 21.1: stably, the graded cyclic evaluation of a
root word in phased words is the m-th power of its offset zero word. -/
theorem cyclic_eval_eq_offset_pow {n m : ℕ} [NeZero m] (P : Kernel.CyclicPhases R m)
    (hnm : 3 ≤ n * m) (γ : R →+* Polynomial R)
    (hγ : ∀ w ∈ P.W, γ w = Polynomial.monomial (P.len w) w)
    (hopp : P.OppositeCommute (n * m)) (l : List (Root n × R)) (hl : ∀ qa ∈ l, qa.2 ∈ P.W)
    (h0 : Elementary.representation (P.offsetWord l 0) = 1) :
    of R (n * m) (Kernel.matrixSteinbergEval (Kernel.cyclicShift m (ZMod ℓ))
      (Steinberg.map γ (Kernel.rootWord l))) = of R (n * m) (P.offsetWord l 0) ^ m := by
  rw [P.cyclic_eval_eq_offsets (ℓ := ℓ) γ hγ hopp l hl, map_list_prod, List.map_map]
  have hall : ∀ a ∈ List.finRange m, (of R (n * m) ∘ P.offsetWord l) a =
      of R (n * m) (P.offsetWord l 0) := by
    intro a _
    have hs := P.offsetWord_shift l 0 a
    rw [zero_add] at hs
    show of R (n * m) (P.offsetWord l a) = _
    rw [← hs]
    exact of_coordinatePerm (ℓ := ℓ) hnm _ _ h0
  rw [List.map_congr_left hall, List.map_const', List.prod_replicate, List.length_finRange]

end Stable
end
end AllPrimeGroups
