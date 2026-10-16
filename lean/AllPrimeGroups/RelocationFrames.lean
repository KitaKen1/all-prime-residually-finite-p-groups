import AllPrimeGroups.PhaseSeparation

/-! Relocation through numerical frames (manuscript Lemma 21.1, its matrix part).

A frame consists of numerical columns `u_s` and rows `v_t` indexed by the phases, with
`v_t u_t = 1`. Given phases with additive projections `π_{s,t}` onto phase components and an
augmentation ε that kills the words, the additive map

  `a ↦ ε(a) + Σ_{s,t} π_{s,t}(a) u_s v_t`

sends a word w to `u_{σ(w)} v_{τ(w)} w`. It is multiplicative on the scalars plus the additive
span of the words, because a nonzero product of words has matching middle phases and inherits
the outer ones. Hence the block evaluation of a root word in words with identity matrix again has
identity matrix. This is the manuscript's homomorphism `ρ : F_p ⊕ R_{≥M} → M_ℓ(R)`; no
Steinberg group of a subring and no injectivity is used.

For the constructed algebra the projections come from the word basis; that instance is not made
here. -/

namespace AllPrimeGroups
noncomputable section
namespace Kernel
open Classical

/-- Phases together with an augmentation killing the words, additive projections onto phase
components, and closure of the words under nonzero products. -/
structure PhaseGrading (ℓ : ℕ) (R : Type*) [Ring R] [Algebra (ZMod ℓ) R] (m : ℕ) [NeZero m]
    extends CyclicPhases R m where
  ε : R →+* ZMod ℓ
  ε_word : ∀ w ∈ W, ε w = 0
  proj : Fin m → Fin m → R →+ R
  proj_word : ∀ s t, ∀ w ∈ W, proj s t w = if σ w = s ∧ τ w = t then w else 0
  proj_one : ∀ s t, proj s t 1 = 0
  mul_mem : ∀ w ∈ W, ∀ w' ∈ W, w * w' ≠ 0 →
    w * w' ∈ W ∧ σ (w * w') = σ w ∧ τ (w * w') = τ w'

/-- Numerical columns and rows indexed by phases; each row pairs to one with the column of the
same phase. -/
structure Frame (ℓ m K : ℕ) where
  col : Fin m → Fin K → ZMod ℓ
  row : Fin m → Fin K → ZMod ℓ
  pair : ∀ t, row t ⬝ᵥ col t = 1

namespace Frame
variable {ℓ m K : ℕ} (R : Type*) [Ring R] [Algebra (ZMod ℓ) R]

/-- The numerical matrix `u_s v_t` of a pair of phases. -/
def block (F : Frame ℓ m K) (s t : Fin m) : Matrix (Fin K) (Fin K) R :=
  (Matrix.vecMulVec (F.col s) (F.row t)).map (algebraMap (ZMod ℓ) R)

theorem block_mul_block (F : Frame ℓ m K) (s t t' : Fin m) :
    F.block R s t * F.block R t t' = F.block R s t' := by
  simp only [block]
  rw [← Matrix.map_mul, Matrix.vecMulVec_mul_vecMulVec, F.pair, one_smul]

theorem block_mul_smul (F : Frame ℓ m K) (s t : Fin m) (b : R)
    (B : Matrix (Fin K) (Fin K) R) :
    F.block R s t * (b • B) = b • (F.block R s t * B) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, block,
    Matrix.map_apply]
  apply Finset.sum_congr rfl
  intro k _
  rw [← mul_assoc, ← mul_assoc, Algebra.commutes]

end Frame

theorem algebraMap_zmod_eq_intCast {ℓ : ℕ} {R : Type*} [Ring R] [Algebra (ZMod ℓ) R]
    (c : ZMod ℓ) : algebraMap (ZMod ℓ) R c = ((ZMod.cast c : ℤ) : R) := by
  rw [← map_intCast (algebraMap (ZMod ℓ) R), ZMod.intCast_zmod_cast]

namespace PhaseGrading
variable {ℓ : ℕ} {R : Type*} [Ring R] [Algebra (ZMod ℓ) R]
variable {m : ℕ} [NeZero m] (G : PhaseGrading ℓ R m) {K : ℕ}

/-- The relocation map of a frame. It is additive on the whole ring. -/
def relocate (F : Frame ℓ m K) : R →+ Matrix (Fin K) (Fin K) R where
  toFun a := Matrix.scalar (Fin K) (algebraMap (ZMod ℓ) R (G.ε a)) +
    ∑ st : Fin m × Fin m, G.proj st.1 st.2 a • F.block R st.1 st.2
  map_zero' := by simp
  map_add' a b := by
    simp only [map_add, add_smul, Finset.sum_add_distrib]
    abel

theorem relocate_apply (F : Frame ℓ m K) (a : R) :
    G.relocate F a = Matrix.scalar (Fin K) (algebraMap (ZMod ℓ) R (G.ε a)) +
      ∑ st : Fin m × Fin m, G.proj st.1 st.2 a • F.block R st.1 st.2 := rfl

theorem relocate_word (F : Frame ℓ m K) {w : R} (hw : w ∈ G.W) :
    G.relocate F w = w • F.block R (G.σ w) (G.τ w) := by
  rw [relocate_apply, G.ε_word w hw, map_zero, map_zero, zero_add,
    Fintype.sum_eq_single (G.σ w, G.τ w)]
  · simp [G.proj_word _ _ w hw]
  · intro st hst
    have h : ¬ (G.σ w = st.1 ∧ G.τ w = st.2) := fun h => hst (Prod.ext h.1.symm h.2.symm)
    simp [G.proj_word _ _ w hw, h]

theorem proj_algebraMap (s t : Fin m) (c : ZMod ℓ) :
    G.proj s t (algebraMap (ZMod ℓ) R c) = 0 := by
  rw [algebraMap_zmod_eq_intCast, ← zsmul_one, map_zsmul, G.proj_one, smul_zero]

theorem ε_algebraMap (c : ZMod ℓ) : G.ε (algebraMap (ZMod ℓ) R c) = c := by
  have h : G.ε.comp (algebraMap (ZMod ℓ) R) = RingHom.id (ZMod ℓ) := Subsingleton.elim _ _
  exact DFunLike.congr_fun h c

theorem relocate_algebraMap (F : Frame ℓ m K) (c : ZMod ℓ) :
    G.relocate F (algebraMap (ZMod ℓ) R c) = Matrix.scalar (Fin K) (algebraMap (ZMod ℓ) R c) := by
  rw [relocate_apply, G.ε_algebraMap]
  simp [G.proj_algebraMap]

theorem relocate_one (F : Frame ℓ m K) : G.relocate F 1 = 1 := by
  have h := G.relocate_algebraMap F 1
  rw [map_one (algebraMap (ZMod ℓ) R), map_one (Matrix.scalar (Fin K))] at h
  exact h

theorem relocate_algebraMap_mul (F : Frame ℓ m K) (c : ZMod ℓ) (a : R) :
    G.relocate F (algebraMap (ZMod ℓ) R c * a) =
      Matrix.scalar (Fin K) (algebraMap (ZMod ℓ) R c) * G.relocate F a := by
  rw [algebraMap_zmod_eq_intCast, ← zsmul_eq_mul, map_zsmul, Matrix.scalar_apply,
    ← Matrix.smul_eq_diagonal_mul, Int.cast_smul_eq_zsmul]

theorem relocate_mul_algebraMap (F : Frame ℓ m K) (a : R) (c : ZMod ℓ) :
    G.relocate F (a * algebraMap (ZMod ℓ) R c) =
      G.relocate F a * Matrix.scalar (Fin K) (algebraMap (ZMod ℓ) R c) := by
  rw [← Algebra.commutes, G.relocate_algebraMap_mul]
  exact (Matrix.scalar_commute _ (fun r => Algebra.commutes c r) _).eq

/-- On words the relocation map is multiplicative. -/
theorem relocate_mul_word (F : Frame ℓ m K) {w w' : R} (hw : w ∈ G.W) (hw' : w' ∈ G.W) :
    G.relocate F (w * w') = G.relocate F w * G.relocate F w' := by
  rw [G.relocate_word F hw, G.relocate_word F hw', Matrix.smul_mul, Frame.block_mul_smul,
    smul_smul]
  by_cases h0 : w * w' = 0
  · rw [h0, map_zero, zero_smul]
  · obtain ⟨hmem, hσ, hτ⟩ := G.mul_mem w hw w' hw' h0
    have hmid : G.τ w = G.σ w' := by
      by_contra hne
      exact h0 (G.mul_eq_zero w hw w' hw' hne)
    rw [G.relocate_word F hmem, hσ, hτ, hmid, Frame.block_mul_block]

theorem ε_closure {x : R} (hx : x ∈ AddSubgroup.closure G.W) : G.ε x = 0 := by
  induction hx using AddSubgroup.closure_induction with
  | mem w hw => exact G.ε_word w hw
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | neg x _ hx => rw [map_neg, hx, neg_zero]

theorem mul_closure {x y : R} (hx : x ∈ AddSubgroup.closure G.W)
    (hy : y ∈ AddSubgroup.closure G.W) : x * y ∈ AddSubgroup.closure G.W := by
  induction hx using AddSubgroup.closure_induction with
  | mem w hw =>
    induction hy using AddSubgroup.closure_induction with
    | mem w' hw' =>
      by_cases h0 : w * w' = 0
      · rw [h0]
        exact zero_mem _
      · exact AddSubgroup.subset_closure (G.mul_mem w hw w' hw' h0).1
    | zero =>
      rw [mul_zero]
      exact zero_mem _
    | add y z _ _ hy hz =>
      rw [mul_add]
      exact add_mem hy hz
    | neg y _ hy =>
      rw [mul_neg]
      exact neg_mem hy
  | zero =>
    rw [zero_mul]
    exact zero_mem _
  | add x z _ _ hx hz =>
    rw [add_mul]
    exact add_mem hx hz
  | neg x _ hx =>
    rw [neg_mul]
    exact neg_mem hx

/-- On the additive span of the words the relocation map is multiplicative. -/
theorem relocate_mul_closure (F : Frame ℓ m K) {x y : R} (hx : x ∈ AddSubgroup.closure G.W)
    (hy : y ∈ AddSubgroup.closure G.W) :
    G.relocate F (x * y) = G.relocate F x * G.relocate F y := by
  induction hx using AddSubgroup.closure_induction with
  | mem w hw =>
    induction hy using AddSubgroup.closure_induction with
    | mem w' hw' => exact G.relocate_mul_word F hw hw'
    | zero => simp
    | add y z _ _ hy hz => rw [mul_add, map_add, map_add, hy, hz, mul_add]
    | neg y _ hy => rw [mul_neg, map_neg, map_neg, hy, mul_neg]
  | zero => simp
  | add x z _ _ hx hz => rw [add_mul, map_add, map_add, hx, hz, add_mul]
  | neg x _ hx => rw [neg_mul, map_neg, map_neg, hx, neg_mul]

/-- Scalars plus the additive span of the words. -/
def InA (a : R) : Prop :=
  ∃ (c : ZMod ℓ) (x : R), x ∈ AddSubgroup.closure G.W ∧ a = algebraMap (ZMod ℓ) R c + x

theorem inA_algebraMap (c : ZMod ℓ) : G.InA (algebraMap (ZMod ℓ) R c) :=
  ⟨c, 0, zero_mem _, (add_zero _).symm⟩

theorem inA_zero : G.InA 0 := ⟨0, 0, zero_mem _, by simp⟩

theorem inA_one : G.InA 1 := ⟨1, 0, zero_mem _, by simp⟩

theorem inA_word {w : R} (hw : w ∈ G.W) : G.InA w :=
  ⟨0, w, AddSubgroup.subset_closure hw, by simp⟩

theorem inA_add {a b : R} (ha : G.InA a) (hb : G.InA b) : G.InA (a + b) := by
  obtain ⟨c, x, hx, rfl⟩ := ha
  obtain ⟨d, y, hy, rfl⟩ := hb
  refine ⟨c + d, x + y, add_mem hx hy, ?_⟩
  rw [map_add]
  abel

theorem algebraMap_mul_mem (c : ZMod ℓ) {x : R} (hx : x ∈ AddSubgroup.closure G.W) :
    algebraMap (ZMod ℓ) R c * x ∈ AddSubgroup.closure G.W := by
  rw [algebraMap_zmod_eq_intCast, ← zsmul_eq_mul]
  exact AddSubgroup.zsmul_mem _ hx _

theorem inA_mul {a b : R} (ha : G.InA a) (hb : G.InA b) : G.InA (a * b) := by
  obtain ⟨c, x, hx, rfl⟩ := ha
  obtain ⟨d, y, hy, rfl⟩ := hb
  refine ⟨c * d, algebraMap (ZMod ℓ) R c * y + x * algebraMap (ZMod ℓ) R d + x * y,
    add_mem (add_mem (G.algebraMap_mul_mem c hy) ?_) (G.mul_closure hx hy), ?_⟩
  · rw [← Algebra.commutes]
    exact G.algebraMap_mul_mem d hx
  · rw [map_mul]
    noncomm_ring

theorem inA_sum {ι : Type*} (s : Finset ι) (f : ι → R) (hf : ∀ i ∈ s, G.InA (f i)) :
    G.InA (∑ i ∈ s, f i) := by
  exact Finset.sum_induction f G.InA (fun _ _ => G.inA_add) G.inA_zero hf

/-- On scalars plus the span of the words the relocation map is multiplicative. -/
theorem relocate_mul (F : Frame ℓ m K) {a b : R} (ha : G.InA a) (hb : G.InA b) :
    G.relocate F (a * b) = G.relocate F a * G.relocate F b := by
  obtain ⟨c, x, hx, rfl⟩ := ha
  obtain ⟨d, y, hy, rfl⟩ := hb
  have e : (algebraMap (ZMod ℓ) R c + x) * (algebraMap (ZMod ℓ) R d + y) =
      algebraMap (ZMod ℓ) R c * algebraMap (ZMod ℓ) R d + algebraMap (ZMod ℓ) R c * y +
        x * algebraMap (ZMod ℓ) R d + x * y := by
    noncomm_ring
  rw [e]
  simp only [map_add, G.relocate_algebraMap_mul, G.relocate_algebraMap, G.relocate_mul_algebraMap,
    G.relocate_mul_closure F hx hy, add_mul, mul_add]
  abel

theorem map_mul_of_inA (F : Frame ℓ m K) {n : ℕ} {X Y : Matrix (Fin n) (Fin n) R}
    (hX : ∀ i j, G.InA (X i j)) (hY : ∀ i j, G.InA (Y i j)) :
    (X * Y).map (G.relocate F) = X.map (G.relocate F) * Y.map (G.relocate F) := by
  refine Matrix.ext fun i j => ?_
  simp only [Matrix.map_apply, Matrix.mul_apply, map_sum]
  apply Finset.sum_congr rfl
  intro k _
  exact G.relocate_mul F (hX i k) (hY k j)

theorem map_relocate_one (F : Frame ℓ m K) {n : ℕ} :
    (1 : Matrix (Fin n) (Fin n) R).map (G.relocate F) = 1 :=
  Matrix.map_one _ (map_zero _) (G.relocate_one F)

theorem map_relocate_e (F : Frame ℓ m K) {n : ℕ} (p : Root n) (a : R) :
    ((Elementary.e p a).val).map (G.relocate F) = (Elementary.e p (G.relocate F a)).val := by
  change (1 + Matrix.single p.row p.col a).map (G.relocate F) =
    1 + Matrix.single p.row p.col (G.relocate F a)
  rw [Matrix.map_add (G.relocate F) (map_add (G.relocate F)), G.map_relocate_one F,
    Matrix.map_single p.row p.col a (G.relocate F)]

theorem inA_e {n : ℕ} (p : Root n) {w : R} (hw : w ∈ G.W) (i j : Fin n) :
    G.InA ((Elementary.e p w).val i j) := by
  change G.InA ((1 + Matrix.single p.row p.col w) i j)
  rw [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  apply G.inA_add
  · split_ifs
    · exact G.inA_one
    · exact G.inA_zero
  · split_ifs
    · exact G.inA_word hw
    · exact G.inA_zero

/-- The block evaluation of a root word through a frame. -/
def frameWord (F : Frame ℓ m K) {n : ℕ} (l : List (Root n × R)) : Steinberg (n * K) R :=
  (l.map (fun qa => blockRoot qa.1 (G.relocate F qa.2))).prod

theorem frameWord_eq_blockMap (F : Frame ℓ m K) {n : ℕ} (l : List (Root n × R)) :
    G.frameWord F l = blockMap (rootWord (l.map (fun qa => (qa.1, G.relocate F qa.2)))) := by
  rw [frameWord, rootWord, map_list_prod, List.map_map, List.map_map]
  congr 1
  apply List.map_congr_left
  intro qa _
  simp only [Function.comp_apply, blockMap_x]

theorem rep_rootWord_relocate (F : Frame ℓ m K) {n : ℕ} (l : List (Root n × R))
    (hl : ∀ qa ∈ l, qa.2 ∈ G.W) :
    (Elementary.representation (rootWord (l.map (fun qa => (qa.1, G.relocate F qa.2))))).val =
      ((Elementary.representation (rootWord l)).val).map (G.relocate F) ∧
    ∀ i j, G.InA ((Elementary.representation (rootWord l)).val i j) := by
  induction l with
  | nil =>
    simp only [List.map_nil, rootWord, List.prod_nil, map_one, Units.val_one]
    exact ⟨(G.map_relocate_one F).symm, fun i j => by
      rw [Matrix.one_apply]
      split_ifs
      · exact G.inA_one
      · exact G.inA_zero⟩
  | cons qa l ih =>
    have hqa : qa.2 ∈ G.W := hl qa (List.mem_cons.mpr (Or.inl rfl))
    obtain ⟨ih₁, ih₂⟩ := ih (fun qb hqb => hl qb (List.mem_cons.mpr (Or.inr hqb)))
    have hcons : ∀ (L : List (Root n × R)), Elementary.representation (rootWord (qa :: L)) =
        Elementary.e qa.1 qa.2 * Elementary.representation (rootWord L) := by
      intro L
      rw [rootWord_cons, map_mul, Elementary.representation_x]
    have hcons' : Elementary.representation (rootWord ((qa :: l).map
        (fun qa => (qa.1, G.relocate F qa.2)))) =
        Elementary.e qa.1 (G.relocate F qa.2) *
          Elementary.representation (rootWord (l.map (fun qa => (qa.1, G.relocate F qa.2)))) := by
      rw [List.map_cons, rootWord_cons, map_mul, Elementary.representation_x]
    refine ⟨?_, ?_⟩
    · rw [hcons', hcons, Units.val_mul, Units.val_mul, ih₁,
        G.map_mul_of_inA F (G.inA_e qa.1 hqa) ih₂, G.map_relocate_e]
    · intro i j
      rw [hcons, Units.val_mul, Matrix.mul_apply]
      exact G.inA_sum _ _ (fun k _ => G.inA_mul (G.inA_e qa.1 hqa i k) (ih₂ k j))

/-- The block evaluation through a frame of a root word in words with identity matrix has
identity matrix. -/
theorem frameWord_kernel (F : Frame ℓ m K) {n : ℕ} (l : List (Root n × R))
    (hl : ∀ qa ∈ l, qa.2 ∈ G.W) (h : Elementary.representation (rootWord l) = 1) :
    Elementary.representation (G.frameWord F l) = 1 := by
  rw [G.frameWord_eq_blockMap F l]
  apply blockMap_kernel
  apply Units.ext
  rw [(G.rep_rootWord_relocate F l hl).1, h, Units.val_one, Units.val_one, G.map_relocate_one F]

end PhaseGrading
end Kernel
end
end AllPrimeGroups
