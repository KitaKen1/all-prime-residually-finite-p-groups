import AllPrimeGroups.CorrectionFaithful

/-! Phase relocation (manuscript Lemma 21.1) and stable separation from phase gradings.

Give the coordinate `(i, s)` the phase s. Through the frame of ones, the block root of a word w
is the product of the roots from every `(i, r)` to `(j, τ(w))`. The factor with `r = σ(w)` is the
root of the standard frame; the others are wrong-row roots and lie in the correction subgroup,
which consistent roots normalize. Collecting the correction factors to the right writes the
evaluation through the frame of ones as the evaluation through the standard frame times an
element of the correction subgroup. Both evaluations have identity matrix, so that element has
identity matrix and is trivial by faithfulness. Together with the moves between frames this is
manuscript Lemma 21.1, and with Theorem 22.2 in general form it gives stable separation from
the following data for arbitrarily large moduli prime to ℓ: a phase grading, the two cases of
manuscript Lemma 20.2, linear independence of the words, and truncation generators that factor
into long words. -/

namespace AllPrimeGroups
noncomputable section
namespace Kernel
open Classical

/-- The phase of a coordinate of a block matrix: its inner index. -/
def innerPhase (n m : ℕ) (x : Fin (n * m)) : Fin m := (finProdFinEquiv.symm x).2

theorem innerPhase_blockIndex {n m : ℕ} (i : Fin n) (s : Fin m) :
    innerPhase n m (blockIndex i s) = s := by
  rw [innerPhase, blockIndex, Equiv.symm_apply_apply]

/-- In a list without repetition, a product of pairwise commuting factors starts with any of its
factors. -/
theorem prod_map_eq_mul_filter {α G : Type*} [Group G] [DecidableEq α] (L : List α) (hL : L.Nodup)
    {a : α} (ha : a ∈ L) (f : α → G) (hf : (L.map f).Pairwise Commute) :
    (L.map f).prod = f a * ((L.filter (fun b => b != a)).map f).prod := by
  rw [← hL.erase_eq_filter a, ← List.prod_cons, ← List.map_cons]
  exact ((List.perm_cons_erase ha).map f).prod_eq' hf

namespace PhaseGrading
variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime] {R : Type*} [Ring R] [hR : Algebra (ZMod ℓ) R]
variable {m : ℕ} [NeZero m] (G : PhaseGrading ℓ R m) {n : ℕ}

theorem relocate_ones_eq {w : R} (hw : w ∈ G.W) :
    G.relocate (Frame.ones ℓ m) w =
      ((List.finRange m).map (fun r => Matrix.single r (G.τ w) w)).sum := by
  rw [G.relocate_word _ hw, ← Fin.sum_univ_def]
  ext a b
  rw [Matrix.sum_apply, Finset.sum_eq_single a]
  · simp only [Frame.block, Frame.ones, Matrix.smul_apply, Matrix.map_apply,
      Matrix.vecMulVec_apply, Matrix.single_apply, smul_eq_mul, one_mul, Pi.single_apply]
    by_cases hb : b = G.τ w
    · simp [hb]
    · simp [hb, Ne.symm hb]
  · intro r _ hr
    simp [hr]
  · intro h
    exact absurd (Finset.mem_univ a) h

theorem blockRoot_ones (q : Root n) {w : R} (hw : w ∈ G.W) :
    blockRoot q (G.relocate (Frame.ones ℓ m) w) =
      ((List.finRange m).map (fun r => Steinberg.x (blockPosition q (r, G.τ w)) w)).prod := by
  rw [G.relocate_ones_eq hw, blockRoot_list_sum, List.map_map]
  congr 1
  apply List.map_congr_left
  intro r _
  exact blockRoot_single q r (G.τ w) w

/-- The block root through the frame of ones is the consistent root times an element of the
correction subgroup. -/
theorem blockRoot_ones_split (q : Root n) {w : R} (hw : w ∈ G.W) :
    ∃ y ∈ G.correction (innerPhase n m),
      blockRoot q (G.relocate (Frame.ones ℓ m) w) =
        Steinberg.x (blockPosition q (G.σ w, G.τ w)) w * y := by
  refine ⟨(((List.finRange m).filter (fun r => r != G.σ w)).map
    (fun r => Steinberg.x (blockPosition q (r, G.τ w)) w)).prod, ?_, ?_⟩
  · apply Subgroup.list_prod_mem
    intro g hg
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hg
    have hr' : r ≠ G.σ w := by simpa using (List.of_mem_filter hr)
    exact G.wrongRoot_mem (innerPhase n m) (blockPosition q (r, G.τ w)).ne hw
      (by rw [show (blockPosition q (r, G.τ w)).row = blockIndex q.row r from rfl,
        innerPhase_blockIndex]; exact hr')
      (by rw [show (blockPosition q (r, G.τ w)).col = blockIndex q.col (G.τ w) from rfl,
        innerPhase_blockIndex])
  · rw [G.blockRoot_ones q hw]
    apply prod_map_eq_mul_filter _ (List.nodup_finRange m) (List.mem_finRange _)
    apply List.pairwise_of_forall_mem_list
    intro x hx y hy
    obtain ⟨r, _, rfl⟩ := List.mem_map.mp hx
    obtain ⟨r', _, rfl⟩ := List.mem_map.mp hy
    exact Steinberg.x_commute _ _ (blockIndex_ne q.ne.symm _ _) (blockIndex_ne q.ne _ _) _ _

/-- The evaluation through the frame of ones is the evaluation through the standard frame times
an element of the correction subgroup. -/
theorem frameWord_ones_eq_std_mul (hK : 5 ≤ n * m) (l : List (Root n × R))
    (hl : ∀ qa ∈ l, qa.2 ∈ G.W) :
    ∃ u ∈ G.correction (innerPhase n m),
      G.frameWord (Frame.ones ℓ m) l = G.frameWord (Frame.std ℓ m) l * u := by
  induction l with
  | nil => exact ⟨1, Subgroup.one_mem _, by simp [frameWord]⟩
  | cons qa l ih =>
    have hw : qa.2 ∈ G.W := hl qa (List.mem_cons.mpr (Or.inl rfl))
    obtain ⟨u, hu, he⟩ := ih (fun qb hqb => hl qb (List.mem_cons.mpr (Or.inr hqb)))
    obtain ⟨y, hy, hsplit⟩ := G.blockRoot_ones_split qa.1 hw
    have hS : G.frameWord (Frame.std ℓ m) l ∈ Subgroup.normalizer
        (G.correction (innerPhase n m) : Set (Steinberg (n * m) R)) := by
      rw [frameWord]
      apply Subgroup.list_prod_mem
      intro g hg
      obtain ⟨qb, hqb, rfl⟩ := List.mem_map.mp hg
      have hwb : qb.2 ∈ G.W := hl qb (List.mem_cons.mpr (Or.inr hqb))
      rw [G.relocate_single _ hwb (G.σ qb.2) (G.τ qb.2) rfl rfl, blockRoot_single]
      exact G.root_mem_normalizer (innerPhase n m) hK (blockPosition qb.1 _).ne hwb
        (by rw [show (blockPosition qb.1 (G.σ qb.2, G.τ qb.2)).col =
          blockIndex qb.1.col (G.τ qb.2) from rfl, innerPhase_blockIndex])
    set S := G.frameWord (Frame.std ℓ m) l with hSdef
    have hconj : S⁻¹ * y * S ∈ G.correction (innerPhase n m) := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hS) y).mp hy
      simpa only [inv_inv] using this
    refine ⟨(S⁻¹ * y * S) * u, Subgroup.mul_mem _ hconj hu, ?_⟩
    have hstd : blockRoot qa.1 (G.relocate (Frame.std ℓ m) qa.2) =
        Steinberg.x (blockPosition qa.1 (G.σ qa.2, G.τ qa.2)) qa.2 := by
      rw [G.relocate_single _ hw (G.σ qa.2) (G.τ qa.2) rfl rfl, blockRoot_single]
    simp only [frameWord, List.map_cons, List.prod_cons] at he ⊢
    rw [he, hsplit, hstd]
    change _ * y * (S * u) = _ * S * (S⁻¹ * y * S * u)
    group

/-- Manuscript Lemma 21.1 in rank at least three: the offset zero word of a root word in phased
words with identity matrix represents the same stable element. -/
theorem relocates_of_three (hm : 2 ≤ m) (hopp : ∀ k, 3 ≤ k → G.OppositeCommute k)
    (hind : ∀ k, 3 ≤ k → G.CutIndependent k)
    (hli : LinearIndependent (ZMod ℓ) (fun w : G.W => (w : R))) (hn : 3 ≤ n)
    (l : List (Root n × R)) (hl : ∀ qa ∈ l, qa.2 ∈ G.W)
    (h : Elementary.representation (rootWord l) = 1) :
    Stable.of R (n * m) (G.offsetWord l 0) = Stable.of R n (rootWord l) := by
  have hK : 5 ≤ n * m := by nlinarith
  obtain ⟨u, hu, he⟩ := G.frameWord_ones_eq_std_mul hK l hl
  have h1 := G.frameWord_kernel (Frame.ones ℓ m) l hl h
  have h2 := G.frameWord_kernel (Frame.std ℓ m) l hl h
  have hrep : Elementary.representation u = 1 := by
    rw [he, map_mul, h2, one_mul] at h1
    exact h1
  have hu1 := G.correction_faithful (innerPhase n m) hK (hopp _ (le_trans (by norm_num) hK))
    (hind _ (le_trans (by norm_num) hK)) hli hu hrep
  rw [hu1, mul_one, G.frameWord_std l hl] at he
  rw [← he]
  exact G.stable_frameWord_ones_eq hn hm l hl h

omit [NeZero m] in
theorem blockIndex_castLE {n n' : ℕ} (hn : n ≤ n') (hnm : n * m ≤ n' * m) (i : Fin n)
    (s : Fin m) :
    blockIndex (Fin.castLE hn i) s = Fin.castLE hnm (blockIndex i s) := by
  apply Fin.ext
  simp [blockIndex]

/-- Manuscript Lemma 21.1. -/
theorem relocates (hm : 2 ≤ m) (hopp : ∀ k, 3 ≤ k → G.OppositeCommute k)
    (hind : ∀ k, 3 ≤ k → G.CutIndependent k)
    (hli : LinearIndependent (ZMod ℓ) (fun w : G.W => (w : R))) : G.Relocates := by
  intro n l hl h
  have hn : n ≤ n + 3 := by omega
  have hnm : n * m ≤ (n + 3) * m := Nat.mul_le_mul_right m hn
  let l' := l.map (fun qa => (qa.1.map (Fin.castLE hn) (Fin.castLE_injective hn), qa.2))
  have hl' : ∀ qa ∈ l', qa.2 ∈ G.W := by
    intro qa hqa
    obtain ⟨qb, hqb, rfl⟩ := List.mem_map.mp hqa
    exact hl qb hqb
  have hroot : rootWord l' =
      Steinberg.coordinateMap (Fin.castLE hn) (Fin.castLE_injective hn) (rootWord l) :=
    (rootWord_coordinateMap _ _ l).symm
  have hoff : G.offsetWord l' 0 = Steinberg.coordinateMap (Fin.castLE hnm)
      (Fin.castLE_injective hnm) (G.offsetWord l 0) := by
    rw [CyclicPhases.offsetWord, CyclicPhases.offsetWord, map_list_prod, List.map_map,
      List.map_map]
    congr 1
  have hrep' : Elementary.representation (rootWord l') = 1 := by
    apply Stable.finite_matrix_kernel R (n + 3)
    rw [hroot, Stable.of_castLE, Stable.representation_of, h, map_one]
  have key := G.relocates_of_three hm hopp hind hli (by omega) l' hl' hrep'
  rw [hoff, Stable.of_castLE, hroot, Stable.of_castLE] at key
  exact key

end PhaseGrading
end Kernel

namespace Stable
variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime] {R : Type*} [Ring R] [hR : Algebra (ZMod ℓ) R]

/-- Stable separation (manuscript Theorem 22.2) from phase gradings. An element of the stable
matrix kernel with trivial reduction is trivial if, for arbitrarily large moduli prime to ℓ,
there is a phase grading whose words satisfy both cases of manuscript Lemma 20.2 in rank at
least three, are linearly independent and are homogeneous for the grading, and the element is
killed by a quotient whose generators factor into long words. -/
theorem eq_one_of_phaseGradings (ε : R →+* ZMod ℓ) (γ : R →+* Polynomial R)
    (h1 : (Kernel.scalarEval (1 : ZMod ℓ)).comp γ = RingHom.id R)
    (h0 : (Kernel.scalarEval (0 : ZMod ℓ)).comp γ = (algebraMap (ZMod ℓ) R).comp ε)
    (z : StableSteinberg R) (hz : representation R z = 1) (hε : map ε z = 1)
    (hphase : ∀ B : ℕ, ∃ (m : ℕ) (G : Kernel.PhaseGrading ℓ R (m + 2)) (S : Set R),
      B < m + 2 ∧ (m + 2).Coprime ℓ ∧
      (∀ w ∈ G.W, γ w = Polynomial.monomial (G.len w) w) ∧
      (∀ k, 3 ≤ k → G.OppositeCommute k) ∧ (∀ k, 3 ≤ k → G.CutIndependent k) ∧
      LinearIndependent (ZMod ℓ) (fun w : G.W => (w : R)) ∧
      (∀ a ∈ S, ∃ b c : R, a = b * c ∧ (∀ r : R, r * b ∈ AddSubgroup.closure G.W) ∧
        ∀ r : R, c * r ∈ AddSubgroup.closure G.W) ∧
      map (SteinbergQuotient.coeffIdeal S).ringCon.mk' z = 1) :
    z = 1 := by
  apply eq_one_of_phases ε γ h1 h0 z hz hε
  intro B
  obtain ⟨m, G, S, hBm, hcop, hγ, hopp, hind, hli, hS, hzS⟩ := hphase B
  exact ⟨m + 1, G.toCyclicPhases, S, hBm, hcop, hγ, hopp,
    G.relocates (by omega) hopp hind hli, hS, hzS⟩

end Stable
end
end AllPrimeGroups
