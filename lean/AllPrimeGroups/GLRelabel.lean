import AllPrimeGroups.GLInduction

/-! Relabelling the coordinates of words in the presentation along an injection.

A word in the generators on `k` coordinates is carried to `n` coordinates along an injection
`f : Fin k → Fin n`. Its matrix acts on vectors supported on the image of `f` as the original
matrix, and fixes the standard columns outside the image. So the relabelled word is a relation
exactly when the original one is. Conversely, every word supported on the image of `f` is a
relabelled word. Every set of at most five coordinates lies in the image of an injection from
`Fin 5` once `n ≥ 5`. -/

namespace AllPrimeGroups
namespace GLPres

open LocalGL Matrix

variable {B : Type*} [Ring B] {k n : ℕ}

/-- Relabelling the coordinates of a generator along an injection. -/
def Gen.relabel (f : Fin k → Fin n) (hf : Function.Injective f) : Gen k B → Gen n B
  | .elem p a => .elem (p.map f hf) a
  | .diag i u => .diag (f i) u

theorem Gen.supp_relabel (f : Fin k → Fin n) (hf : Function.Injective f) (g : Gen k B) :
    (g.relabel f hf).supp = g.supp.map ⟨f, hf⟩ := by
  cases g with
  | elem p a => simp [Gen.relabel, Gen.supp, Root.map, Finset.map_insert, Finset.map_singleton]
  | diag i u => simp [Gen.relabel, Gen.supp]

/-- The relabelling of words. -/
def relabel (f : Fin k → Fin n) (hf : Function.Injective f) :
    FreeGroup (Gen k B) →* FreeGroup (Gen n B) :=
  FreeGroup.map (Gen.relabel f hf)

theorem relabel_of (f : Fin k → Fin n) (hf : Function.Injective f) (g : Gen k B) :
    relabel f hf (FreeGroup.of g) = FreeGroup.of (g.relabel f hf) :=
  FreeGroup.map.of

/-- Vectors supported on the image of an injection. -/
noncomputable def extendVec (f : Fin k → Fin n) (x : Fin k → B) : Fin n → B :=
  Function.extend f x 0

variable {f : Fin k → Fin n} (hf : Function.Injective f)

include hf in
theorem extendVec_apply (x : Fin k → B) (j : Fin k) : extendVec f x (f j) = x j :=
  hf.extend_apply x 0 j

theorem extendVec_apply_out (x : Fin k → B) {l : Fin n} (hl : ∀ j, f j ≠ l) :
    extendVec f x l = 0 :=
  Function.extend_apply' x (0 : Fin n → B) l (fun ⟨j, hj⟩ => hl j hj)

include hf in
theorem extendVec_single (j : Fin k) :
    extendVec f (Pi.single j (1 : B)) = Pi.single (f j) 1 := by
  funext l
  by_cases hl : ∃ i, f i = l
  · obtain ⟨i, rfl⟩ := hl
    rw [extendVec_apply hf]
    simp [Pi.single_apply, hf.eq_iff]
  · have hl' : ∀ i, f i ≠ l := fun i e => hl ⟨i, e⟩
    rw [extendVec_apply_out _ hl']
    simp [Ne.symm (hl' j)]

theorem relabel_val_mulVec (g : Gen k B) (x : Fin k → B) :
    (((g.relabel f hf).val : (Matrix (Fin n) (Fin n) B)ˣ) : Matrix (Fin n) (Fin n) B) *ᵥ
      extendVec f x = extendVec f (((g.val : (Matrix (Fin k) (Fin k) B)ˣ) :
        Matrix (Fin k) (Fin k) B) *ᵥ x) := by
  funext l
  by_cases hl : ∃ j, f j = l
  · obtain ⟨j, rfl⟩ := hl
    rw [extendVec_apply hf]
    cases g with
    | elem p a =>
      simp only [Gen.relabel, Gen.val, e_mulVec, Root.map, hf.eq_iff, extendVec_apply hf]
    | diag i u =>
      simp only [Gen.relabel, Gen.val, d_mulVec, hf.eq_iff, extendVec_apply hf]
  · have hl' : ∀ j, f j ≠ l := fun j e => hl ⟨j, e⟩
    rw [extendVec_apply_out _ hl']
    cases g with
    | elem p a =>
      simp only [Gen.relabel, Gen.val, e_mulVec, Root.map, (hl' p.row).symm, ↓reduceIte,
        extendVec_apply_out _ hl']
    | diag i u =>
      simp only [Gen.relabel, Gen.val, d_mulVec, (hl' i).symm, ↓reduceIte,
        extendVec_apply_out _ hl']

theorem relabel_val_single_out (g : Gen k B) {l : Fin n} (hl : ∀ j, f j ≠ l) :
    (((g.relabel f hf).val : (Matrix (Fin n) (Fin n) B)ˣ) : Matrix (Fin n) (Fin n) B) *ᵥ
      Pi.single l 1 = Pi.single l 1 := by
  funext m
  cases g with
  | elem p a =>
    simp only [Gen.relabel, Gen.val, e_mulVec, Root.map]
    have h0 : (Pi.single l (1 : B) : Fin n → B) (f p.col) = 0 := by simp [hl p.col]
    rw [h0, mul_zero, add_zero, ite_self]
  | diag i u =>
    simp only [Gen.relabel, Gen.val, d_mulVec]
    by_cases hm : m = f i
    · subst hm
      simp [(hl i)]
    · simp [hm]

theorem inv_mulVec_of_mulVec {M : (Matrix (Fin n) (Fin n) B)ˣ} {x y : Fin n → B}
    (h : (M : Matrix (Fin n) (Fin n) B) *ᵥ x = y) :
    ((M⁻¹ : (Matrix (Fin n) (Fin n) B)ˣ) : Matrix (Fin n) (Fin n) B) *ᵥ y = x := by
  rw [← h, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]

theorem ev_relabel_mulVec (w : FreeGroup (Gen k B)) (x : Fin k → B) :
    ((ev (relabel f hf w) : (Matrix (Fin n) (Fin n) B)ˣ) : Matrix (Fin n) (Fin n) B) *ᵥ
      extendVec f x = extendVec f (((ev w : (Matrix (Fin k) (Fin k) B)ˣ) :
        Matrix (Fin k) (Fin k) B) *ᵥ x) := by
  induction w using FreeGroup.induction_on generalizing x with
  | one => simp
  | of g =>
    rw [relabel_of, ev_of, ev_of]
    exact relabel_val_mulVec hf g x
  | inv_of g _ =>
    rw [map_inv, relabel_of, map_inv, ev_of, map_inv, ev_of]
    apply inv_mulVec_of_mulVec
    rw [relabel_val_mulVec hf g, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  | mul v w hv hw =>
    rw [map_mul, map_mul, Units.val_mul, ← Matrix.mulVec_mulVec, hw, hv, map_mul, Units.val_mul,
      Matrix.mulVec_mulVec]

theorem ev_relabel_single_out (w : FreeGroup (Gen k B)) {l : Fin n} (hl : ∀ j, f j ≠ l) :
    ((ev (relabel f hf w) : (Matrix (Fin n) (Fin n) B)ˣ) : Matrix (Fin n) (Fin n) B) *ᵥ
      Pi.single l 1 = Pi.single l 1 := by
  induction w using FreeGroup.induction_on with
  | one => rw [map_one, map_one, Units.val_one, Matrix.one_mulVec]
  | of g =>
    rw [relabel_of, ev_of]
    exact relabel_val_single_out hf g hl
  | inv_of g _ =>
    rw [map_inv, relabel_of, map_inv, ev_of]
    exact inv_mulVec_of_mulVec (relabel_val_single_out hf g hl)
  | mul v w hv hw =>
    rw [map_mul, map_mul, Units.val_mul, ← Matrix.mulVec_mulVec, hw, hv]

theorem eq_one_of_mulVec_single {M : (Matrix (Fin n) (Fin n) B)ˣ}
    (h : ∀ l, (M : Matrix (Fin n) (Fin n) B) *ᵥ Pi.single l 1 = Pi.single l 1) : M = 1 := by
  apply Units.ext
  ext i l
  have := congrFun (h l) i
  rw [Matrix.mulVec_single_one] at this
  rw [Units.val_one, Matrix.one_apply]
  simpa [Pi.single_apply, eq_comm] using this

/-- A relabelled word is a relation exactly when the original one is. -/
theorem ev_relabel_eq_one_iff (w : FreeGroup (Gen k B)) :
    ev (relabel f hf w) = 1 ↔ ev w = 1 := by
  constructor
  · intro h
    apply eq_one_of_mulVec_single
    intro j
    have := ev_relabel_mulVec hf w (Pi.single j 1)
    rw [h, Units.val_one, Matrix.one_mulVec, extendVec_single hf] at this
    funext i
    have := congrFun this (f i)
    rw [extendVec_apply hf] at this
    rw [← this]
    simp [Pi.single_apply, hf.eq_iff]
  · intro h
    apply eq_one_of_mulVec_single
    intro l
    by_cases hl : ∃ j, f j = l
    · obtain ⟨j, rfl⟩ := hl
      rw [← extendVec_single hf, ev_relabel_mulVec hf, h, Units.val_one, Matrix.one_mulVec]
    · exact ev_relabel_single_out hf w (fun j e => hl ⟨j, e⟩)

theorem relabel_supported (w : FreeGroup (Gen k B)) :
    relabel f hf w ∈ supported (Finset.univ.map ⟨f, hf⟩) := by
  have h : (⊤ : Subgroup (FreeGroup (Gen k B))) ≤
      (supported (B := B) (Finset.univ.map ⟨f, hf⟩)).comap (relabel f hf) := by
    rw [← FreeGroup.closure_range_of, Subgroup.closure_le]
    rintro _ ⟨g, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, relabel_of]
    apply of_mem_supported
    rw [Gen.supp_relabel]
    exact Finset.map_subset_map.mpr (Finset.subset_univ _)
  exact h (Subgroup.mem_top w)

/-- Every word supported on the image of an injection is a relabelled word. -/
theorem exists_relabel {w : FreeGroup (Gen n B)} (hw : w ∈ supported (Finset.univ.map ⟨f, hf⟩)) :
    ∃ w' : FreeGroup (Gen k B), relabel f hf w' = w := by
  have h : supported (B := B) (Finset.univ.map ⟨f, hf⟩) ≤ (relabel (B := B) f hf).range := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨g, hg, rfl⟩
    have hmem : ∀ l ∈ g.supp, ∃ j, f j = l := fun l hl => by
      obtain ⟨j, -, hj⟩ := Finset.mem_map.mp (hg hl)
      exact ⟨j, hj⟩
    cases g with
    | elem p a =>
      obtain ⟨r, hr⟩ := hmem p.row (by simp [Gen.supp])
      obtain ⟨c, hc⟩ := hmem p.col (by simp [Gen.supp])
      have hrc : r ≠ c := fun e => p.ne (by rw [← hr, ← hc, e])
      refine ⟨FreeGroup.of (Gen.elem ⟨r, c, hrc⟩ a), ?_⟩
      rw [relabel_of]
      congr 2
      cases p
      simp only at hr hc ⊢
      subst hr
      subst hc
      rfl
    | diag i u =>
      obtain ⟨j, hj⟩ := hmem i (by simp [Gen.supp])
      refine ⟨FreeGroup.of (Gen.diag j u), ?_⟩
      rw [relabel_of]
      simp only [Gen.relabel, hj]
  exact h hw

/-- At most five coordinates lie in the image of an injection from `Fin 5`. -/
theorem exists_embedding_five {T : Finset (Fin n)} (hT : T.card ≤ 5) (hn : 5 ≤ n) :
    ∃ (f : Fin 5 → Fin n) (hf : Function.Injective f), T ⊆ Finset.univ.map ⟨f, hf⟩ := by
  obtain ⟨T', hTT', hcard⟩ := Finset.exists_superset_card_eq hT (by simpa using hn)
  refine ⟨T'.orderEmbOfFin hcard, (T'.orderEmbOfFin hcard).injective, fun t ht => ?_⟩
  have : t ∈ Set.range (T'.orderEmbOfFin hcard) := by
    rw [Finset.range_orderEmbOfFin]
    exact hTT' ht
  obtain ⟨j, hj⟩ := this
  exact Finset.mem_map.mpr ⟨j, Finset.mem_univ _, hj⟩

end GLPres
end AllPrimeGroups
