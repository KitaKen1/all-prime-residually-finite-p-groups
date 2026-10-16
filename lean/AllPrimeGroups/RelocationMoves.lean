import AllPrimeGroups.RelocationFrames

/-! Moving between frames (manuscript Lemma 21.1, the steps before the correction subgroup).

Three frames of size m are compared, for a root word in phased words with identity matrix:

* the copy frame, all columns `e_0` and all rows `e_0`: its block evaluation is the coordinate
  copy of the word in inner index zero, which is stably the original element;
* the spread frame, columns `e_0` and rows `e_0` for phase zero and `e_0 + e_t` otherwise: the
  added roots run from inner index zero to the other inner indices, so they lie in a faithful
  strip normalized by the copied roots, and the two evaluations are equal;
* the frame of ones, columns `e_0 + ... + e_{m-1}` and rows `e_t`: it is the spread frame
  conjugated by a numerical matrix of determinant one, so the evaluations agree stably.

The remaining step, from the frame of ones to the standard frame, needs the correction subgroup
of manuscript Lemma 20.3 and is not done here. -/

namespace AllPrimeGroups
noncomputable section
namespace Kernel
open Classical

section Vectors
variable {ℓ m : ℕ} (R : Type*) [Ring R] [Algebra (ZMod ℓ) R]

theorem vecMulVec_single_map (a b : Fin m) :
    (Matrix.vecMulVec (Pi.single a (1 : ZMod ℓ)) (Pi.single b 1)).map (algebraMap (ZMod ℓ) R) =
      Matrix.single a b 1 := by
  ext i j
  simp only [Matrix.map_apply, Matrix.vecMulVec_apply, Pi.single_apply, Matrix.single_apply]
  by_cases hi : i = a
  · subst hi
    by_cases hj : j = b
    · subst hj
      simp
    · simp [hj, Ne.symm hj]
  · simp [hi, Ne.symm hi]

end Vectors

namespace Frame
variable {ℓ m : ℕ}

/-- The standard frame: the unit vectors of the phases. -/
def std (ℓ m : ℕ) : Frame ℓ m m where
  col s := Pi.single s 1
  row t := Pi.single t 1
  pair t := by simp [dotProduct_single]

/-- The frame placing every phase at one coordinate. -/
def copy (ℓ : ℕ) {m : ℕ} (s₀ : Fin m) : Frame ℓ m m where
  col _ := Pi.single s₀ 1
  row _ := Pi.single s₀ 1
  pair _ := by simp [dotProduct_single]

/-- Columns `e_0`; rows `e_0` for phase zero and `e_0 + e_t` otherwise. -/
def spread (ℓ m : ℕ) [NeZero m] : Frame ℓ m m where
  col _ := Pi.single 0 1
  row t := if t = 0 then Pi.single 0 1 else Pi.single 0 1 + Pi.single t 1
  pair t := by
    split_ifs with ht
    · simp [dotProduct_single]
    · simp [dotProduct_single, Ne.symm ht]

/-- Columns `e_0 + ... + e_{m-1}` and rows `e_t`. -/
def ones (ℓ m : ℕ) : Frame ℓ m m where
  col _ := fun _ => 1
  row t := Pi.single t 1
  pair t := by simp [single_dotProduct]

end Frame

namespace PhaseGrading
variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime] {R : Type*} [Ring R] [hR : Algebra (ZMod ℓ) R]
variable {m : ℕ} [NeZero m] (G : PhaseGrading ℓ R m) {n : ℕ}

theorem relocate_single (F : Frame ℓ m m) {w : R} (hw : w ∈ G.W) (a b : Fin m)
    (hc : F.col (G.σ w) = Pi.single a 1) (hr : F.row (G.τ w) = Pi.single b 1) :
    G.relocate F w = Matrix.single a b w := by
  rw [G.relocate_word F hw, Frame.block, hc, hr, vecMulVec_single_map, Matrix.smul_single,
    smul_eq_mul, mul_one]

/-- Through the standard frame, the block evaluation is the offset zero word. -/
theorem frameWord_std (l : List (Root n × R)) (hl : ∀ qa ∈ l, qa.2 ∈ G.W) :
    G.frameWord (Frame.std ℓ m) l = G.offsetWord l 0 := by
  rw [frameWord, CyclicPhases.offsetWord]
  congr 1
  apply List.map_congr_left
  intro qa hqa
  rw [G.relocate_single _ (hl qa hqa) (G.σ qa.2) (G.τ qa.2) rfl rfl, blockRoot_single,
    CyclicPhases.offsetFactor, add_zero, add_zero]

/-- Through a copy frame, the block evaluation is a block copy. -/
theorem frameWord_copy (s₀ : Fin m) (l : List (Root n × R)) (hl : ∀ qa ∈ l, qa.2 ∈ G.W) :
    G.frameWord (Frame.copy ℓ s₀) l = copyMap s₀ (rootWord l) := by
  rw [frameWord, rootWord, map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro qa hqa
  rw [G.relocate_single _ (hl qa hqa) s₀ s₀ rfl rfl, blockRoot_single, Function.comp_apply,
    copyMap_x]

include hℓ hR in
/-- The copy frame represents the original element stably. -/
theorem stable_frameWord_copy (hn : 3 ≤ n) (hm : 2 ≤ m) (l : List (Root n × R))
    (hl : ∀ qa ∈ l, qa.2 ∈ G.W) (h : Elementary.representation (rootWord l) = 1) :
    Stable.of R (n * m) (G.frameWord (Frame.copy ℓ 0) l) = Stable.of R n (rootWord l) := by
  have hnm : n ≤ n * m := by nlinarith
  rw [G.frameWord_copy 0 l hl]
  calc Stable.of R (n * m) (copyMap 0 (rootWord l))
      = Stable.of R (n * m + 1) (padSteinberg (copyMap 0 (rootWord l))) :=
        (Chain.of_step (steinbergStep R) (n * m) _).symm
    _ = Stable.of R (n * m + 1) (padSteinberg (Steinberg.coordinateMap (Fin.castLE hnm)
          (Fin.castLE_injective _) (rootWord l))) := by
        rw [stable_copy_to_standard (ℓ := ℓ) hn hm (0 : Fin m) (rootWord l) h]
    _ = Stable.of R (n * m) (Steinberg.coordinateMap (Fin.castLE hnm)
          (Fin.castLE_injective _) (rootWord l)) :=
        Chain.of_step (steinbergStep R) (n * m) _
    _ = Stable.of R n (rootWord l) := Stable.of_castLE R hnm _

/-- The block root of a word through the spread frame: its copy in inner index zero, followed
by a root from inner index zero to the end phase when that phase is not zero. -/
theorem blockRoot_spread (q : Root n) {w : R} (hw : w ∈ G.W) :
    blockRoot q (G.relocate (Frame.spread ℓ m) w) =
      Steinberg.x (blockPosition q (0, 0)) w *
        (if G.τ w = 0 then 1 else Steinberg.x (blockPosition q (0, G.τ w)) w) := by
  by_cases ht : G.τ w = 0
  · have hr : (Frame.spread ℓ m).row (G.τ w) = Pi.single 0 1 := by simp [Frame.spread, ht]
    rw [G.relocate_single _ hw 0 0 rfl hr, blockRoot_single]
    simp [ht]
  · have hr : (Frame.spread ℓ m).row (G.τ w) = Pi.single 0 1 + Pi.single (G.τ w) 1 := by
      simp [Frame.spread, ht]
    rw [G.relocate_word _ hw, Frame.block, hr]
    change blockRoot q (w • (Matrix.vecMulVec (Pi.single 0 1)
      (Pi.single 0 1 + Pi.single (G.τ w) 1)).map (algebraMap (ZMod ℓ) R)) = _
    rw [Matrix.vecMulVec_add, Matrix.map_add (algebraMap (ZMod ℓ) R)
      (map_add (algebraMap (ZMod ℓ) R)), vecMulVec_single_map, vecMulVec_single_map, smul_add,
      Matrix.smul_single, Matrix.smul_single, smul_eq_mul, mul_one, blockRoot_add,
      blockRoot_single, blockRoot_single]
    simp [ht]

/-- Coordinates of inner index zero. -/
def zeroBlock (n m : ℕ) [NeZero m] : Finset (Fin (n * m)) :=
  Finset.univ.image (fun i : Fin n => blockIndex i (0 : Fin m))

/-- Coordinates of nonzero inner index. -/
def nonzeroBlock (n m : ℕ) [NeZero m] : Finset (Fin (n * m)) :=
  Finset.univ.filter (fun x => (finProdFinEquiv.symm x).2 ≠ (0 : Fin m))

theorem zeroBlock_disjoint : Disjoint (zeroBlock n m) (nonzeroBlock n m) := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
  apply (Finset.mem_filter.mp hx').2
  change (finProdFinEquiv.symm (finProdFinEquiv (i, (0 : Fin m)))).2 = 0
  rw [Equiv.symm_apply_apply]

theorem blockIndex_mem_zeroBlock (i : Fin n) : blockIndex i (0 : Fin m) ∈ zeroBlock n m :=
  Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩

theorem blockIndex_mem_nonzeroBlock (i : Fin n) {t : Fin m} (ht : t ≠ 0) :
    blockIndex i t ∈ nonzeroBlock n m := by
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  change (finProdFinEquiv.symm (finProdFinEquiv (i, t))).2 ≠ 0
  rw [Equiv.symm_apply_apply]
  exact ht

/-- The spread frame differs from the copy frame by an element of the strip from inner index
zero to the other inner indices. -/
theorem frameWord_spread_eq (l : List (Root n × R)) (hl : ∀ qa ∈ l, qa.2 ∈ G.W) :
    ∃ s ∈ Strip (R := R) (zeroBlock n m) (nonzeroBlock n m) zeroBlock_disjoint,
      G.frameWord (Frame.spread ℓ m) l = G.frameWord (Frame.copy ℓ 0) l * s := by
  induction l with
  | nil => exact ⟨1, Subgroup.one_mem _, by simp [frameWord]⟩
  | cons qa l ih =>
    have hw : qa.2 ∈ G.W := hl qa (List.mem_cons.mpr (Or.inl rfl))
    obtain ⟨s, hs, he⟩ := ih (fun qb hqb => hl qb (List.mem_cons.mpr (Or.inr hqb)))
    set g := G.frameWord (Frame.copy ℓ 0) l with hg
    have hgN : g ∈ Subgroup.normalizer
        (Strip (R := R) (zeroBlock n m) (nonzeroBlock n m) zeroBlock_disjoint :
          Set (Steinberg (n * m) R)) := by
      rw [hg, frameWord]
      apply Subgroup.list_prod_mem
      intro y hy
      obtain ⟨qb, hqb, rfl⟩ := List.mem_map.mp hy
      rw [G.relocate_single _ (hl qb (List.mem_cons.mpr (Or.inr hqb))) 0 0 rfl rfl,
        blockRoot_single]
      exact side_root_normalizes _ _ _ _
        (Or.inl ⟨blockIndex_mem_zeroBlock _, blockIndex_mem_zeroBlock _⟩) _
    let e : Steinberg (n * m) R :=
      if G.τ qa.2 = 0 then 1 else Steinberg.x (blockPosition qa.1 (0, G.τ qa.2)) qa.2
    have heS : e ∈ Strip (R := R) (zeroBlock n m) (nonzeroBlock n m) zeroBlock_disjoint := by
      by_cases ht : G.τ qa.2 = 0
      · simp only [e, ht, ↓reduceIte]
        exact Subgroup.one_mem _
      · simp only [e, ht, ↓reduceIte]
        exact Subgroup.subset_closure
          ⟨(⟨_, blockIndex_mem_zeroBlock qa.1.row⟩, ⟨_, blockIndex_mem_nonzeroBlock qa.1.col ht⟩),
            qa.2, rfl⟩
    have hconj : g⁻¹ * e * g ∈
        Strip (R := R) (zeroBlock n m) (nonzeroBlock n m) zeroBlock_disjoint := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgN) e).mp heS
      simpa only [inv_inv] using this
    refine ⟨(g⁻¹ * e * g) * s, Subgroup.mul_mem _ hconj hs, ?_⟩
    have hcopy : blockRoot qa.1 (G.relocate (Frame.copy ℓ 0) qa.2) =
        Steinberg.x (blockPosition qa.1 (0, 0)) qa.2 := by
      rw [G.relocate_single _ hw 0 0 rfl rfl, blockRoot_single]
    simp only [frameWord, List.map_cons, List.prod_cons] at he ⊢
    rw [he, G.blockRoot_spread qa.1 hw, hcopy]
    change _ * e * (g * s) = _ * g * (g⁻¹ * e * g * s)
    group

include hℓ hR in
/-- The spread frame and the copy frame give the same element. -/
theorem frameWord_spread (l : List (Root n × R)) (hl : ∀ qa ∈ l, qa.2 ∈ G.W)
    (h : Elementary.representation (rootWord l) = 1) :
    G.frameWord (Frame.spread ℓ m) l = G.frameWord (Frame.copy ℓ 0) l := by
  obtain ⟨s, hs, he⟩ := G.frameWord_spread_eq l hl
  have h1 := G.frameWord_kernel (Frame.spread ℓ m) l hl h
  have h0 := G.frameWord_kernel (Frame.copy ℓ 0) l hl h
  have hs1 : Elementary.representation s = 1 := by
    rw [he, map_mul, h0, one_mul] at h1
    exact h1
  rw [he, strip_faithful _ _ _ hs hs1, mul_one]

end PhaseGrading

section Spread
variable {ℓ : ℕ} {m : ℕ} [NeZero m]

/-- The strictly lower part of the spread matrix: ones in column zero below the diagonal. -/
def spreadNil (ℓ m : ℕ) [NeZero m] : Matrix (Fin m) (Fin m) (ZMod ℓ) :=
  Matrix.of fun t k => if t ≠ 0 ∧ k = 0 then 1 else 0

theorem spreadNil_mul_self : spreadNil ℓ m * spreadNil ℓ m = 0 := by
  ext t k
  simp only [Matrix.mul_apply, spreadNil, Matrix.of_apply, Matrix.zero_apply]
  apply Finset.sum_eq_zero
  intro j _
  by_cases hj : j = 0 <;> simp [hj]

/-- The spread matrix, whose rows are those of the spread frame. -/
def spreadUnits (ℓ m : ℕ) [NeZero m] : (Matrix (Fin m) (Fin m) (ZMod ℓ))ˣ where
  val := 1 + spreadNil ℓ m
  inv := 1 - spreadNil ℓ m
  val_inv := by rw [add_mul, one_mul, mul_sub, mul_one, spreadNil_mul_self, sub_zero]; abel
  inv_val := by rw [sub_mul, one_mul, mul_add, mul_one, spreadNil_mul_self, add_zero]; abel

theorem spreadUnits_det : (spreadUnits ℓ m).val.det = 1 := by
  have hlow : (spreadUnits ℓ m).val.BlockTriangular OrderDual.toDual := by
    intro i j hij
    have hij' : i < j := hij
    have hj : j ≠ 0 := by
      intro h
      rw [h, Fin.lt_def, Fin.val_zero] at hij'
      exact Nat.not_lt_zero _ hij'
    simp [spreadUnits, spreadNil, ne_of_lt hij', hj]
  rw [Matrix.det_of_isLowerTriangular _ hlow]
  apply Finset.prod_eq_one
  intro i _
  simp [spreadUnits, spreadNil]

theorem spreadUnits_row (t : Fin m) : (spreadUnits ℓ m).val t = (Frame.spread ℓ m).row t := by
  funext k
  by_cases ht : t = 0
  · subst ht
    by_cases hk : k = 0
    · simp [spreadUnits, spreadNil, Frame.spread, hk]
    · simp [spreadUnits, spreadNil, Frame.spread, hk, Ne.symm hk]
  · by_cases hk : k = 0
    · simp [spreadUnits, spreadNil, Frame.spread, ht, hk]
    · by_cases htk : t = k
      · subst htk
        simp [spreadUnits, spreadNil, Frame.spread, ht]
      · simp [spreadUnits, spreadNil, Frame.spread, ht, hk, htk, Ne.symm htk]

theorem spreadUnits_col_zero (t : Fin m) : (spreadUnits ℓ m).val t 0 = 1 := by
  by_cases ht : t = 0
  · simp [spreadUnits, spreadNil, ht]
  · simp [spreadUnits, spreadNil, ht]

/-- The spread matrix conjugates the blocks of the spread frame to those of the frame of ones. -/
theorem spreadUnits_conj_block (s t : Fin m) :
    (spreadUnits ℓ m).val * Matrix.vecMulVec ((Frame.spread ℓ m).col s) ((Frame.spread ℓ m).row t) =
      Matrix.vecMulVec ((Frame.ones ℓ m).col s) ((Frame.ones ℓ m).row t) * (spreadUnits ℓ m).val := by
  rw [← spreadUnits_row]
  ext a b
  change ∑ k, (spreadUnits ℓ m).val a k *
      ((Pi.single (0 : Fin m) (1 : ZMod ℓ) : Fin m → ZMod ℓ) k * (spreadUnits ℓ m).val t b) =
    ∑ k, ((1 : ZMod ℓ) * (Pi.single t (1 : ZMod ℓ) : Fin m → ZMod ℓ) k) *
      (spreadUnits ℓ m).val k b
  rw [Finset.sum_eq_single (0 : Fin m), Finset.sum_eq_single t]
  · rw [spreadUnits_col_zero]
    simp
  · intro k _ hk
    simp [hk]
  · simp
  · intro k _ hk
    simp [hk]
  · simp

end Spread

namespace PhaseGrading
variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime] {R : Type*} [Ring R] [hR : Algebra (ZMod ℓ) R]
variable {m : ℕ} [NeZero m] (G : PhaseGrading ℓ R m) {n : ℕ}

theorem relocate_ones_conj {w : R} (hw : w ∈ G.W) :
    coefficientConj (numericUnits (R := R) (spreadUnits ℓ m)) (G.relocate (Frame.spread ℓ m) w) =
      G.relocate (Frame.ones ℓ m) w := by
  rw [G.relocate_word _ hw, G.relocate_word _ hw]
  change (numericUnits (R := R) (spreadUnits ℓ m)).val *
      (w • (Frame.spread ℓ m).block R (G.σ w) (G.τ w)) *
      (numericUnits (R := R) (spreadUnits ℓ m)).inv = _
  have hcomm : (numericUnits (R := R) (spreadUnits ℓ m)).val *
      (Frame.spread ℓ m).block R (G.σ w) (G.τ w) =
      (Frame.ones ℓ m).block R (G.σ w) (G.τ w) * (numericUnits (R := R) (spreadUnits ℓ m)).val := by
    change (spreadUnits ℓ m).val.map (algebraMap (ZMod ℓ) R) *
        (Matrix.vecMulVec _ _).map (algebraMap (ZMod ℓ) R) =
      (Matrix.vecMulVec _ _).map (algebraMap (ZMod ℓ) R) *
        (spreadUnits ℓ m).val.map (algebraMap (ZMod ℓ) R)
    rw [← Matrix.map_mul, ← Matrix.map_mul, spreadUnits_conj_block]
  have hnum : (numericUnits (R := R) (spreadUnits ℓ m)).val * (w • Frame.block R (Frame.spread ℓ m) (G.σ w) (G.τ w)) =
      w • ((numericUnits (R := R) (spreadUnits ℓ m)).val * Frame.block R (Frame.spread ℓ m) (G.σ w) (G.τ w)) := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    change algebraMap (ZMod ℓ) R _ * (w * _) = w * (algebraMap (ZMod ℓ) R _ * _)
    rw [← mul_assoc, ← mul_assoc, Algebra.commutes]
  rw [hnum, hcomm, Matrix.smul_mul, mul_assoc,
    (numericUnits (R := R) (spreadUnits ℓ m)).val_inv, mul_one]

include hℓ hR in
/-- The frame of ones and the spread frame give the same stable element. -/
theorem stable_frameWord_ones (hn : 3 ≤ n) (l : List (Root n × R)) (hl : ∀ qa ∈ l, qa.2 ∈ G.W)
    (h : Elementary.representation (rootWord l) = 1) :
    Stable.of R (n * m) (G.frameWord (Frame.ones ℓ m) l) =
      Stable.of R (n * m) (G.frameWord (Frame.spread ℓ m) l) := by
  obtain ⟨b, hb⟩ := numerical_big_lift (n := n) (R := R) (spreadUnits ℓ m) spreadUnits_det
  have he := stable_basis_change hn (numericUnits (R := R) (spreadUnits ℓ m)) b hb
    (rootWord (l.map (fun qa => (qa.1, G.relocate (Frame.spread ℓ m) qa.2))))
  have hu : Steinberg.map (coefficientConj (numericUnits (R := R) (spreadUnits ℓ m)))
      (rootWord (l.map (fun qa => (qa.1, G.relocate (Frame.spread ℓ m) qa.2)))) =
      rootWord (l.map (fun qa => (qa.1, G.relocate (Frame.ones ℓ m) qa.2))) := by
    rw [map_rootWord, List.map_map]
    congr 1
    apply List.map_congr_left
    intro qa hqa
    simp only [Function.comp_apply, G.relocate_ones_conj (hl qa hqa)]
  rw [hu, ← G.frameWord_eq_blockMap, ← G.frameWord_eq_blockMap] at he
  have hk := G.frameWord_kernel (Frame.spread ℓ m) l hl h
  have hz := stabilized_kernel_central _ hk
  have hc : Commute (padSteinberg b) (padSteinberg (G.frameWord (Frame.spread ℓ m) l)) :=
    Subgroup.mem_center_iff.mp hz _
  simp only [map_mul, map_inv, CommutatorCalculus.conj_of_commute hc] at he
  have h1 := congrArg (Stable.of R (n * m + 1)) he
  rw [show Stable.of R (n * m + 1) (padSteinberg (G.frameWord (Frame.spread ℓ m) l)) =
      Stable.of R (n * m) (G.frameWord (Frame.spread ℓ m) l) from
      Chain.of_step (steinbergStep R) (n * m) _,
    show Stable.of R (n * m + 1) (padSteinberg (G.frameWord (Frame.ones ℓ m) l)) =
      Stable.of R (n * m) (G.frameWord (Frame.ones ℓ m) l) from
      Chain.of_step (steinbergStep R) (n * m) _] at h1
  exact h1.symm

include hℓ hR in
/-- Manuscript Lemma 21.1 up to the correction subgroup: through the frame of ones, the block
evaluation of a root word in phased words with identity matrix represents the original element
stably. -/
theorem stable_frameWord_ones_eq (hn : 3 ≤ n) (hm : 2 ≤ m) (l : List (Root n × R))
    (hl : ∀ qa ∈ l, qa.2 ∈ G.W) (h : Elementary.representation (rootWord l) = 1) :
    Stable.of R (n * m) (G.frameWord (Frame.ones ℓ m) l) = Stable.of R n (rootWord l) := by
  rw [G.stable_frameWord_ones hn l hl h, G.frameWord_spread l hl h,
    G.stable_frameWord_copy hn hm l hl h]

end PhaseGrading
end Kernel
end
end AllPrimeGroups
