import OAI.GroupTheory.PeriodicGroups.Steinberg.CoefficientQuotients

/-! The word basis of a word algebra (manuscript Lemma 16.1, its linear part).

For a table of replacements and zero words, the upstream file `Algebra/WordAlgebra.lean`
constructs a linear functional on the free algebra that detects the replacement class of one
non-vanishing word and kills the relation ideal. Here it is descended to the quotient algebra,
which gives linear independence of the classes of non-vanishing words over any nontrivial
commutative ring.

Also, the map that keeps only the words satisfying a predicate descends to the quotient whenever
the predicate is invariant under replacements and false on vanishing words. Applied to phases,
this gives the projections onto phase components needed by the relocation homomorphisms. -/

namespace AllPrimeGroups
noncomputable section
open OAI OAI.SourceBurnside OAI.SourceBurnside.WordAlgebra
open Classical

namespace WordBasis
variable {α : Type*} {K : Type*} [CommRing K] (T : Table α)

/-- An additive map from the free algebra that kills the relation ideal descends to the word
algebra. -/
def descend {M : Type*} [AddCommGroup M] (F : Polynomial K α →+ M)
    (hF : ∀ f ∈ T.ideal (K := K), F f = 0) : T.Algebra (K := K) →+ M where
  toFun := Quotient.lift F (fun a b hab => by
    apply sub_eq_zero.mp
    rw [← map_sub]
    exact hF _ (((T.ideal (K := K)).rel_iff a b).mp hab))
  map_zero' := map_zero F
  map_add' x y := by
    obtain ⟨a, rfl⟩ := (T.ideal (K := K)).ringCon.mk'_surjective x
    obtain ⟨b, rfl⟩ := (T.ideal (K := K)).ringCon.mk'_surjective y
    rw [← map_add]
    exact map_add F a b

@[simp] theorem descend_quotient {M : Type*} [AddCommGroup M] (F : Polynomial K α →+ M)
    (hF : ∀ f ∈ T.ideal (K := K), F f = 0) (f : Polynomial K α) :
    descend T F hF (T.quotient f) = F f := rfl

/-- The map keeping only the monomials whose word satisfies a predicate. -/
def polyFilter (Φ : Word α → Prop) : Polynomial K α →+ Polynomial K α where
  toFun f := MonoidAlgebra.ofCoeff (Finsupp.filter Φ f.coeff)
  map_zero' := by
    change MonoidAlgebra.ofCoeff (Finsupp.filter Φ 0) = 0
    rw [Finsupp.filter_zero]
    rfl
  map_add' f g := by
    change MonoidAlgebra.ofCoeff (Finsupp.filter Φ (f.coeff + g.coeff)) = _
    rw [Finsupp.filter_add]
    rfl

theorem polyFilter_single (Φ : Word α → Prop) (w : Word α) (a : K) :
    polyFilter Φ (MonoidAlgebra.single w a) = if Φ w then MonoidAlgebra.single w a else 0 := by
  change MonoidAlgebra.ofCoeff (Finsupp.filter Φ (Finsupp.single w a)) = _
  split_ifs with h
  · rw [Finsupp.filter_single_of_pos _ h]
    rfl
  · rw [Finsupp.filter_single_of_neg _ h]
    rfl

/-- A predicate on words that is invariant under replacements and false on vanishing words. -/
structure Compatible (Φ : Word α → Prop) : Prop where
  reach : ∀ {v w}, T.Reach v w → (Φ v ↔ Φ w)
  vanish : ∀ {w}, T.Vanishes w → ¬ Φ w

/-- The polynomials all of whose two-sided multiples filter into the relation ideal. -/
def filterIdeal (Φ : Word α → Prop) : TwoSidedIdeal (Polynomial K α) :=
  TwoSidedIdeal.mk' {f | ∀ a b, polyFilter Φ (a * f * b) ∈ T.ideal (K := K)}
    (by intro a b; simp)
    (by
      intro f g hf hg a b
      rw [mul_add, add_mul, map_add]
      exact add_mem (hf a b) (hg a b))
    (by
      intro f hf a b
      rw [mul_neg, neg_mul, map_neg]
      exact neg_mem (hf a b))
    (by intro f g hg a b; simpa only [mul_assoc] using hg (a * f) b)
    (by intro f g hf a b; simpa only [mul_assoc] using hf a (g * b))

theorem mem_filterIdeal {Φ : Word α → Prop} {f : Polynomial K α} :
    f ∈ filterIdeal T Φ ↔ ∀ a b, polyFilter Φ (a * f * b) ∈ T.ideal (K := K) := by
  simp [filterIdeal]

theorem relation_mem_filterIdeal {Φ : Word α → Prop} (hΦ : Compatible T Φ) {f : Polynomial K α}
    (hf : f ∈ T.relations) : f ∈ filterIdeal T Φ := by
  apply (mem_filterIdeal T).mpr
  intro A B
  induction A using MonoidAlgebra.induction_linear with
  | zero => simp
  | add A₁ A₂ h₁ h₂ =>
    rw [add_mul, add_mul, map_add]
    exact add_mem h₁ h₂
  | single p a =>
    induction B using MonoidAlgebra.induction_linear with
    | zero => simp
    | add B₁ B₂ h₁ h₂ =>
      rw [mul_add, map_add]
      exact add_mem h₁ h₂
    | single s b =>
      rcases hf with ⟨v, w, hvw, rfl⟩ | ⟨z, hz, rfl⟩
      · have hr : T.Reach (p * v * s) (p * w * s) :=
          T.reach_context (ConGen.Rel.of _ _ hvw) p s
        have he : MonoidAlgebra.single p a * (monomial v - monomial w) * MonoidAlgebra.single s b =
            MonoidAlgebra.single (p * v * s) (a * b) - MonoidAlgebra.single (p * w * s) (a * b) := by
          simp only [monomial, mul_sub, sub_mul, MonoidAlgebra.single_mul_single, mul_one]
        have hmem : MonoidAlgebra.single p a * (monomial v - monomial w) *
            MonoidAlgebra.single s b ∈ T.ideal (K := K) :=
          (T.ideal (K := K)).mul_mem_right _ _ ((T.ideal (K := K)).mul_mem_left _ _
            (TwoSidedIdeal.subset_span (Or.inl ⟨v, w, hvw, rfl⟩)))
        rw [he, map_sub, polyFilter_single, polyFilter_single]
        by_cases hpv : Φ (p * v * s)
        · have hpw : Φ (p * w * s) := (hΦ.reach hr).mp hpv
          simp only [hpv, hpw, ↓reduceIte]
          rw [← he]
          exact hmem
        · have hpw : ¬ Φ (p * w * s) := fun h => hpv ((hΦ.reach hr).mpr h)
          simp only [hpv, hpw, ↓reduceIte, sub_zero]
          exact zero_mem _
      · have he : MonoidAlgebra.single p a * monomial z * MonoidAlgebra.single s b =
            MonoidAlgebra.single (p * z * s) (a * b) := by
          simp only [monomial, MonoidAlgebra.single_mul_single, mul_one]
        have hn : ¬ Φ (p * z * s) := hΦ.vanish ⟨p, z, s, hz, (conGen T.rep).refl _⟩
        rw [he, polyFilter_single]
        simp only [hn, ↓reduceIte]
        exact zero_mem _

theorem polyFilter_mem_ideal {Φ : Word α → Prop} (hΦ : Compatible T Φ) {f : Polynomial K α}
    (hf : f ∈ T.ideal (K := K)) : polyFilter Φ f ∈ T.ideal (K := K) := by
  have hle : T.ideal (K := K) ≤ filterIdeal T Φ :=
    TwoSidedIdeal.span_le.mpr (fun _ hg => relation_mem_filterIdeal T hΦ hg)
  have h := (mem_filterIdeal T).mp (hle hf) 1 1
  simpa only [one_mul, mul_one] using h

/-- The projection of the word algebra onto the classes of words satisfying a compatible
predicate. -/
def filterMap {Φ : Word α → Prop} (hΦ : Compatible T Φ) : T.Algebra (K := K) →+ T.Algebra (K := K) :=
  descend T ((T.quotient (K := K)).toAddMonoidHom.comp (polyFilter Φ)) (by
    intro f hf
    exact ((T.ideal (K := K)).ringCon.eq).mpr
      (((T.ideal (K := K)).rel_iff _ _).mpr (by rw [sub_zero]; exact polyFilter_mem_ideal T hΦ hf)))

theorem filterMap_word {Φ : Word α → Prop} (hΦ : Compatible T Φ) (w : Word α) :
    filterMap T hΦ (T.word (K := K) w) = if Φ w then T.word w else 0 := by
  change T.quotient (polyFilter Φ (monomial w)) = _
  rw [monomial, polyFilter_single]
  split_ifs
  · rfl
  · exact map_zero _

theorem filterMap_one {Φ : Word α → Prop} (hΦ : Compatible T Φ) (h1 : ¬ Φ 1) :
    filterMap T hΦ (1 : T.Algebra (K := K)) = 0 := by
  have h := filterMap_word T hΦ (K := K) 1
  rw [T.word_one] at h
  simpa only [h1, ↓reduceIte] using h

/-- The functional detecting the class of a non-vanishing word, on the word algebra. -/
def detectMap (w₀ : Word α) (hw₀ : ¬ T.Vanishes w₀) : T.Algebra (K := K) →+ K :=
  descend T (T.detect w₀) (by
    intro f hf
    have hd := (Table.mem_annihilator (T.detect w₀) _).mp (T.ideal_le_annihilator w₀ hw₀ hf) 1 1
    simpa only [one_mul, mul_one] using hd)

theorem detectMap_word (w₀ : Word α) (hw₀ : ¬ T.Vanishes w₀) (w : Word α) :
    detectMap T w₀ hw₀ (T.word (K := K) w) = if T.Reach w₀ w then 1 else 0 := by
  change T.detect w₀ (monomial w) = _
  rw [monomial, Table.detect_single]

theorem detect_smul (w₀ : Word α) (c : K) (f : Polynomial K α) :
    T.detect w₀ (c • f) = c * T.detect w₀ f := by
  induction f using MonoidAlgebra.induction_linear with
  | zero => simp
  | add f g hf hg => rw [smul_add, map_add, map_add, hf, hg, mul_add]
  | single w a =>
    rw [MonoidAlgebra.smul_single, Table.detect_single, Table.detect_single, smul_eq_mul]
    split_ifs <;> simp

theorem detectMap_smul (w₀ : Word α) (hw₀ : ¬ T.Vanishes w₀) (c : K) (x : T.Algebra (K := K)) :
    detectMap T w₀ hw₀ (c • x) = c * detectMap T w₀ hw₀ x := by
  obtain ⟨f, rfl⟩ := (T.ideal (K := K)).ringCon.mk'_surjective x
  change detectMap T w₀ hw₀ (c • T.quotient f) = c * detectMap T w₀ hw₀ (T.quotient f)
  rw [← Table.quotient_smul]
  exact detect_smul T w₀ c f

/-- Manuscript Lemma 16.1, linear part: distinct classes of non-vanishing words are linearly
independent. -/
theorem linearIndependent_words [Nontrivial K] (W : Set (T.Algebra (K := K)))
    (hW : ∀ x ∈ W, ∃ w, ¬ T.Vanishes w ∧ x = T.word w) :
    LinearIndependent K (fun x : W => (x : T.Algebra (K := K))) := by
  apply linearIndependent_iff'.mpr
  intro s g hs i hi
  obtain ⟨w₀, hw₀, hi'⟩ := hW i i.property
  have h := congrArg (detectMap T w₀ hw₀) hs
  rw [map_sum, map_zero, Finset.sum_eq_single i] at h
  · have hrefl : T.Reach w₀ w₀ := (conGen T.rep).refl w₀
    rw [detectMap_smul, hi', detectMap_word] at h
    simpa only [hrefl, ↓reduceIte, mul_one] using h
  · intro j _ hji
    obtain ⟨w, hw, hj'⟩ := hW j j.property
    have hnr : ¬ T.Reach w₀ w := by
      intro hr
      apply hji
      apply Subtype.ext
      rw [hj', hi']
      exact (T.word_reach hr).symm
    rw [detectMap_smul, hj', detectMap_word]
    simp only [hnr, ↓reduceIte, mul_zero]
  · intro hi''
    exact absurd hi hi''

end WordBasis
end
end AllPrimeGroups
