/-
Finite presentation of the Steinberg group of a finitely presented algebra over the prime
field (manuscript Theorem 10.1), adapted from OpenAI
PeriodicGroups/Steinberg/{MonomialPresentation,CoefficientQuotients}.lean (commit pinned in
upstream/provenance.json; Apache-2.0, see upstream/OpenAI-LICENSE).

The upstream statements are for the two-element field. Here the coefficients are `ZMod ℓ`
with `ℓ` nonzero; the finite relator list uses ℓ-th powers of the short root generators.
The coefficient-quotient part is valid over every unital ring, as upstream.
-/
import AllPrimeGroups.MonomialPresentation
import Mathlib.GroupTheory.FinitelyPresentedGroup
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.RingTheory.TwoSidedIdeal.Operations

namespace AllPrimeGroups
universe u v

namespace Steinberg
variable {n : ℕ} {R : Type u} [Ring R]

theorem x_nsmul (p : Root n) (a : R) (k : ℕ) : x p (k • a) = x p a ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [succ_nsmul, x_add, ih, pow_succ]

end Steinberg

namespace FiniteSteinbergPresentation

open MonomialCompletion

variable {ℓ n : ℕ} {α : Type u}

abbrev ShortWord (α : Type u) := {w : List α // w.length ≤ 2}
abbrev Gen (n : ℕ) (α : Type u) := Root n × ShortWord α

instance root_finite (n : ℕ) : Finite (Root n) :=
  Finite.of_injective (fun p : Root n => (p.row, p.col)) (by
    rintro ⟨i, j, hij⟩ ⟨k, l, hkl⟩ he
    have hi : i = k := congrArg Prod.fst he
    have hj : j = l := congrArg Prod.snd he
    subst k; subst l
    rfl)

def shortWordMap : Unit ⊕ (α ⊕ α × α) → ShortWord α
  | .inl _ => ⟨[], by simp⟩
  | .inr (.inl a) => ⟨[a], by simp⟩
  | .inr (.inr (a, b)) => ⟨[a, b], by simp⟩

instance shortWord_finite [Finite α] : Finite (ShortWord α) :=
  Finite.of_surjective shortWordMap (by
    rintro ⟨w, hw⟩
    match w with
    | [] => exact ⟨.inl (), rfl⟩
    | [a] => exact ⟨.inr (.inl a), rfl⟩
    | [a, b] => exact ⟨.inr (.inr (a, b)), rfl⟩
    | _ :: _ :: _ :: _ => simp only [List.length_cons] at hw; omega)

def gen (p : Root n) (w : ShortWord α) : FreeGroup (Gen n α) := FreeGroup.of (p, w)

/-- The finite relator list: ℓ-th powers, commuting positions, and products of total
length at most two. -/
inductive Rel (ℓ n : ℕ) (α : Type u) : FreeGroup (Gen n α) → Prop
  | power (p : Root n) (w : ShortWord α) : Rel ℓ n α (gen p w ^ ℓ)
  | commute (p q : Root n) (h₁ : p.col ≠ q.row) (h₂ : p.row ≠ q.col)
      (u v : ShortWord α) : Rel ℓ n α (bracket (gen p u) (gen q v))
  | product (i j k : Fin n) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
      (u v : ShortWord α) (h : u.val.length + v.val.length ≤ 2) :
      Rel ℓ n α (bracket (gen ⟨i, j, hij⟩ u) (gen ⟨j, k, hjk⟩ v) *
        (gen ⟨i, k, hik⟩ ⟨u.val ++ v.val, by simpa only [List.length_append] using h⟩)⁻¹)

theorem rel_finite [Finite α] : {r | Rel ℓ n α r}.Finite := by
  let S₁ := Set.range (fun g : Gen n α => FreeGroup.of g ^ ℓ)
  let S₂ := Set.range (fun g : Gen n α × Gen n α => bracket (FreeGroup.of g.1) (FreeGroup.of g.2))
  let S₃ := Set.range (fun g : Gen n α × Gen n α × Gen n α =>
    bracket (FreeGroup.of g.1) (FreeGroup.of g.2.1) * (FreeGroup.of g.2.2)⁻¹)
  apply ((Set.finite_range _).union ((Set.finite_range _).union (Set.finite_range _)) :
    (S₁ ∪ (S₂ ∪ S₃)).Finite).subset
  intro r hr
  cases hr with
  | power p w => exact Or.inl ⟨(p, w), rfl⟩
  | commute p q h₁ h₂ u v => exact Or.inr (Or.inl ⟨((p, u), (q, v)), rfl⟩)
  | product i j k hij hjk hik u v h =>
    exact Or.inr (Or.inr ⟨((⟨i, j, hij⟩, u), (⟨j, k, hjk⟩, v),
      (⟨i, k, hik⟩, ⟨u.val ++ v.val, by simpa only [List.length_append] using h⟩)), rfl⟩)

/-- The group with the finite presentation. -/
abbrev PresentedSteinberg (ℓ n : ℕ) (α : Type u) := PresentedGroup {r | Rel ℓ n α r}

instance finitelyPresented [Finite α] :
    Group.IsFinitelyPresented (PresentedSteinberg ℓ n α) := by
  have : Finite {r | Rel ℓ n α r} := (rel_finite (ℓ := ℓ) (n := n) (α := α)).to_subtype
  infer_instance

noncomputable def seed : Seed ℓ n α (PresentedSteinberg ℓ n α) where
  g p w := if h : w.length ≤ 2 then PresentedGroup.of (p, ⟨w, h⟩) else 1
  power p w hw := by
    simp only [dite_eq_left hw]
    have h := PresentedGroup.one_of_mem (Rel.power (ℓ := ℓ) p ⟨w, hw⟩)
    simp only [map_pow, gen] at h
    exact h
  commute p q u v hu hv h₁ h₂ := by
    simp only [dite_eq_left hu, dite_eq_left hv]
    apply (bracket_eq_one_iff _ _).mp
    have h := PresentedGroup.one_of_mem (Rel.commute (ℓ := ℓ) p q h₁ h₂ ⟨u, hu⟩ ⟨v, hv⟩)
    simp only [map_bracket, gen] at h
    exact h
  product i j k hij hjk hik u v huv := by
    have hu : u.length ≤ 2 := by omega
    have hv : v.length ≤ 2 := by omega
    have hw : (u ++ v).length ≤ 2 := by simp only [List.length_append]; omega
    simp only [dite_eq_left hu, dite_eq_left hv, dite_eq_left hw]
    have h := PresentedGroup.mk_eq_mk_of_mul_inv_mem
      (Rel.product (ℓ := ℓ) i j k hij hjk hik ⟨u, hu⟩ ⟨v, hv⟩ huv)
    simp only [map_bracket, gen] at h
    exact h

@[simp] theorem seed_short (p : Root n) (w : ShortWord α) :
    (seed (ℓ := ℓ)).g p w.val = (PresentedGroup.of (p, w) : PresentedSteinberg ℓ n α) := by
  simp [seed, w.property]

noncomputable def monomial (w : List α) : Polynomial ℓ α :=
  MonoidAlgebra.single (FreeMonoid.ofList w) 1

@[simp] theorem monomial_append (u v : List α) :
    monomial (ℓ := ℓ) (u ++ v) = monomial u * monomial v := by
  rw [monomial, monomial, monomial, MonoidAlgebra.single_mul_single, one_mul]
  rfl

theorem x_monomial_pow (p : Root n) (w : List α) :
    Steinberg.x p (monomial (ℓ := ℓ) w) ^ ℓ = 1 := by
  rw [← Steinberg.x_nsmul, ZModModule.char_nsmul_eq_zero ℓ, Steinberg.x_zero]

noncomputable def toSteinberg : PresentedSteinberg ℓ n α →* Steinberg n (Polynomial ℓ α) :=
  PresentedGroup.toGroup (f := fun g : Gen n α => Steinberg.x g.1 (monomial g.2.val)) (by
    intro r hr
    cases hr with
    | power p w =>
      simp only [map_pow, gen, FreeGroup.lift_apply_of]
      exact x_monomial_pow p w.val
    | commute p q h₁ h₂ u v =>
      simp only [map_bracket, gen, FreeGroup.lift_apply_of]
      exact (bracket_eq_one_iff _ _).mpr (Steinberg.x_commute p q h₁ h₂ _ _)
    | product i j k hij hjk hik u v h =>
      simp only [map_mul, map_inv, map_bracket, gen, FreeGroup.lift_apply_of]
      rw [Steinberg.x_mul i j k hij hjk hik, monomial_append, mul_inv_cancel])

@[simp] theorem toSteinberg_of (p : Root n) (w : ShortWord α) :
    toSteinberg (PresentedGroup.of (p, w) : PresentedSteinberg ℓ n α) =
      Steinberg.x p (monomial w.val) :=
  PresentedGroup.toGroup.of _

variable [NeZero ℓ]

noncomputable def fromSteinberg (hn : 5 ≤ n) :
    Steinberg n (Polynomial ℓ α) →* PresentedSteinberg ℓ n α :=
  MonomialCompletion.lift seed hn

@[simp] theorem fromSteinberg_x (hn : 5 ≤ n) (p : Root n) (f : Polynomial ℓ α) :
    fromSteinberg hn (Steinberg.x p f) = poly seed hn p f := by
  simp [fromSteinberg]

omit [NeZero ℓ] in
theorem toSteinberg_seed (p : Root n) (w : List α) (hw : w.length ≤ 2) :
    toSteinberg ((seed (ℓ := ℓ)).g p w : PresentedSteinberg ℓ n α) =
      Steinberg.x p (monomial w) := by
  rw [seed_short p ⟨w, hw⟩, toSteinberg_of]

omit [NeZero ℓ] in
theorem toSteinberg_word (hn : 5 ≤ n) (p : Root n) (w : List α) :
    toSteinberg (word (seed (ℓ := ℓ)) hn p w : PresentedSteinberg ℓ n α) =
      Steinberg.x p (monomial w) := by
  induction w generalizing p with
  | nil => rw [word_short _ _ _ _ (by simp), toSteinberg_seed _ _ (by simp)]
  | cons a v ih =>
    by_cases hv : v.length ≤ 1
    · rw [word_short _ _ _ _ (by simp only [List.length_cons]; omega),
        toSteinberg_seed _ _ (by simp only [List.length_cons]; omega)]
    · rw [word_long _ _ _ _ _ (by omega), map_bracket,
        word_short _ _ _ _ (by simp), toSteinberg_seed _ _ (by simp), ih,
        Steinberg.x_mul p.row (middle hn p) p.col
          (middle_ne_row hn p).symm (middle_ne_col hn p) p.ne]
      exact congrArg (Steinberg.x p) (monomial_append [a] v).symm

theorem toSteinberg_poly (hn : 5 ≤ n) (p : Root n) (f : Polynomial ℓ α) :
    toSteinberg (poly (seed (ℓ := ℓ)) hn p f : PresentedSteinberg ℓ n α) = Steinberg.x p f := by
  induction f using polynomial_induction with
  | zero => simp
  | add f g hf hg => rw [poly_add, map_mul, hf, hg, Steinberg.x_add]
  | monomial w =>
    rw [poly_single, toSteinberg_word]
    rfl

theorem from_to (hn : 5 ≤ n) :
    (fromSteinberg (ℓ := ℓ) (α := α) hn).comp toSteinberg =
      MonoidHom.id (PresentedSteinberg ℓ n α) := by
  apply PresentedGroup.ext
  rintro ⟨p, w⟩
  simp only [MonoidHom.comp_apply, toSteinberg_of, fromSteinberg_x, MonoidHom.id_apply]
  change poly seed hn p (MonoidAlgebra.single (FreeMonoid.ofList w.val) 1) = _
  rw [poly_single]
  change word seed hn p w.val = _
  rw [word_short _ _ _ _ w.property]
  exact seed_short p w

theorem to_from (hn : 5 ≤ n) :
    toSteinberg.comp (fromSteinberg (ℓ := ℓ) (α := α) hn) =
      MonoidHom.id (Steinberg n (Polynomial ℓ α)) := by
  apply Steinberg.hom_ext
  intro p f
  simp only [MonoidHom.comp_apply, fromSteinberg_x, toSteinberg_poly, MonoidHom.id_apply]

noncomputable def equiv (hn : 5 ≤ n) :
    PresentedSteinberg ℓ n α ≃* Steinberg n (Polynomial ℓ α) where
  toFun := toSteinberg
  invFun := fromSteinberg hn
  left_inv a := DFunLike.congr_fun (from_to hn) a
  right_inv a := DFunLike.congr_fun (to_from hn) a
  map_mul' := toSteinberg.map_mul

/-- The Steinberg group of a free algebra on a finite alphabet over the prime field is
finitely presented in rank at least five. -/
theorem free_finitelyPresented [Finite α] (hn : 5 ≤ n) :
    Group.IsFinitelyPresented (Steinberg n (Polynomial ℓ α)) :=
  Group.IsFinitelyPresented.equiv (equiv hn)

end FiniteSteinbergPresentation

namespace SteinbergQuotient

variable {n : ℕ} {R : Type u} [Ring R]

def killedIdeal {G : Type v} [Group G] (hn : 5 ≤ n) (f : Steinberg n R →* G) :
    TwoSidedIdeal R :=
  TwoSidedIdeal.mk' {a | ∀ p, f (Steinberg.x p a) = 1}
    (by intro p; simp)
    (by intro a b ha hb p; rw [Steinberg.x_add, map_mul, ha, hb, one_mul])
    (by intro a ha p; rw [Steinberg.x_neg, map_inv, ha, inv_one])
    (by
      intro a b hb p
      obtain ⟨j, hji, hjk, _, _⟩ := exists_fresh hn p.row p.col p.row p.col
      rw [← Steinberg.x_mul p.row j p.col hji.symm hjk p.ne, map_bracket, hb]
      simp [bracket])
    (by
      intro a b ha p
      obtain ⟨j, hji, hjk, _, _⟩ := exists_fresh hn p.row p.col p.row p.col
      rw [← Steinberg.x_mul p.row j p.col hji.symm hjk p.ne, map_bracket, ha]
      simp [bracket])

@[simp] theorem mem_killedIdeal {G : Type v} [Group G] (hn : 5 ≤ n)
    (f : Steinberg n R →* G) (a : R) :
    a ∈ killedIdeal hn f ↔ ∀ p, f (Steinberg.x p a) = 1 := by
  simp [killedIdeal]

variable (S : Set R)

def rootRelations : Set (Steinberg n R) := {g | ∃ p a, a ∈ S ∧ g = Steinberg.x p a}

abbrev normal : Subgroup (Steinberg n R) := Subgroup.normalClosure (rootRelations (n := n) S)

abbrev Quot := Steinberg n R ⧸ normal (n := n) S

abbrev coeffIdeal := TwoSidedIdeal.span S

/-- The quotient of the coefficient ring by the two-sided ideal generated by `S`. -/
abbrev Coeff := (coeffIdeal S).ringCon.Quotient

abbrev proj : Steinberg n R →* Quot (n := n) S := QuotientGroup.mk' (normal S)

theorem killed (hn : 5 ≤ n) {a : R} (ha : a ∈ coeffIdeal S) (p : Root n) :
    proj S (Steinberg.x p a) = 1 := by
  have hs : coeffIdeal S ≤ killedIdeal hn (proj (n := n) S) := by
    apply TwoSidedIdeal.span_le.mpr
    intro b hb
    apply (mem_killedIdeal hn _ _).mpr
    intro q
    apply (QuotientGroup.eq_one_iff _).mpr
    exact Subgroup.subset_normalClosure ⟨q, b, hb, rfl⟩
  exact (mem_killedIdeal hn _ _).mp (hs ha) p

noncomputable def quotientRoot (hn : 5 ≤ n) (p : Root n) : Coeff S → Quot (n := n) S :=
  Quotient.lift (fun a => proj S (Steinberg.x p a)) (by
    intro a b hab
    have hk := killed S hn ((coeffIdeal S).rel_iff a b |>.mp hab) p
    rw [sub_eq_add_neg, Steinberg.x_add, Steinberg.x_neg, map_mul, map_inv] at hk
    exact mul_inv_eq_one.mp hk)

@[simp] theorem quotientRoot_mk (hn : 5 ≤ n) (p : Root n) (a : R) :
    quotientRoot S hn p ((coeffIdeal S).ringCon.mk' a) = proj S (Steinberg.x p a) := rfl

noncomputable def fromCoeff (hn : 5 ≤ n) : Steinberg n (Coeff S) →* Quot (n := n) S :=
  Steinberg.lift (quotientRoot S hn)
    (by
      intro p a b
      obtain ⟨a, rfl⟩ := (coeffIdeal S).ringCon.mk'_surjective a
      obtain ⟨b, rfl⟩ := (coeffIdeal S).ringCon.mk'_surjective b
      rw [← map_add, quotientRoot_mk, quotientRoot_mk, quotientRoot_mk,
        Steinberg.x_add, map_mul])
    (by
      intro p q h₁ h₂ a b
      obtain ⟨a, rfl⟩ := (coeffIdeal S).ringCon.mk'_surjective a
      obtain ⟨b, rfl⟩ := (coeffIdeal S).ringCon.mk'_surjective b
      exact (Steinberg.x_commute p q h₁ h₂ a b).map (proj S))
    (by
      intro i j k hij hjk hik a b
      obtain ⟨a, rfl⟩ := (coeffIdeal S).ringCon.mk'_surjective a
      obtain ⟨b, rfl⟩ := (coeffIdeal S).ringCon.mk'_surjective b
      rw [← map_mul, quotientRoot_mk, quotientRoot_mk, quotientRoot_mk,
        ← map_bracket, Steinberg.x_mul])

@[simp] theorem fromCoeff_x (hn : 5 ≤ n) (p : Root n) (a : R) :
    fromCoeff S hn (Steinberg.x p ((coeffIdeal S).ringCon.mk' a)) =
      proj S (Steinberg.x p a) := by
  change quotientRoot S hn p ((coeffIdeal S).ringCon.mk' a) = _
  rfl

theorem normal_le_ker :
    normal (n := n) S ≤ (Steinberg.map (n := n) (coeffIdeal S).ringCon.mk').ker := by
  apply Subgroup.normalClosure_le_normal
  rintro g ⟨p, a, ha, rfl⟩
  change Steinberg.map (n := n) (coeffIdeal S).ringCon.mk' (Steinberg.x p a) = 1
  rw [Steinberg.map_x]
  have ha0 : (coeffIdeal S).ringCon.mk' a = 0 := by
    apply ((coeffIdeal S).ringCon.eq).mpr
    exact TwoSidedIdeal.subset_span ha
  rw [ha0, Steinberg.x_zero]

noncomputable def toCoeff : Quot (n := n) S →* Steinberg n (Coeff S) :=
  QuotientGroup.lift (normal S) (Steinberg.map (n := n) (coeffIdeal S).ringCon.mk')
    (normal_le_ker S)

@[simp] theorem toCoeff_proj (g : Steinberg n R) :
    toCoeff S (proj S g) = Steinberg.map (n := n) (coeffIdeal S).ringCon.mk' g := rfl

theorem fromCoeff_comp_toCoeff (hn : 5 ≤ n) :
    (fromCoeff S hn).comp (toCoeff S) = MonoidHom.id (Quot (n := n) S) := by
  have h : ((fromCoeff S hn).comp (toCoeff S)).comp (proj S) = proj (n := n) S := by
    apply Steinberg.hom_ext
    intro p a
    change fromCoeff S hn (toCoeff S (proj S (Steinberg.x p a))) = _
    rw [toCoeff_proj, Steinberg.map_x, fromCoeff_x]
  apply MonoidHom.ext
  intro g
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (normal S) g
  exact DFunLike.congr_fun h g

theorem toCoeff_comp_fromCoeff (hn : 5 ≤ n) :
    (toCoeff S).comp (fromCoeff S hn) = MonoidHom.id (Steinberg n (Coeff S)) := by
  apply Steinberg.hom_ext
  intro p a
  obtain ⟨a, rfl⟩ := (coeffIdeal S).ringCon.mk'_surjective a
  change toCoeff S (fromCoeff S hn (Steinberg.x p ((coeffIdeal S).ringCon.mk' a))) = _
  rw [fromCoeff_x, toCoeff_proj, Steinberg.map_x]
  rfl

noncomputable def equiv (hn : 5 ≤ n) : Quot (n := n) S ≃* Steinberg n (Coeff S) where
  toFun := toCoeff S
  invFun := fromCoeff S hn
  left_inv g := DFunLike.congr_fun (fromCoeff_comp_toCoeff S hn) g
  right_inv g := DFunLike.congr_fun (toCoeff_comp_fromCoeff S hn) g
  map_mul' := (toCoeff S).map_mul

theorem rootRelations_finite (hS : S.Finite) : (rootRelations (n := n) S).Finite := by
  have h : rootRelations (n := n) S =
      (fun z : Root n × R => Steinberg.x z.1 z.2) '' (Set.univ ×ˢ S) := by
    ext g
    constructor
    · rintro ⟨p, a, ha, rfl⟩
      exact ⟨(p, a), ⟨Set.mem_univ _, ha⟩, rfl⟩
    · rintro ⟨⟨p, a⟩, ⟨_, ha⟩, rfl⟩
      exact ⟨p, a, ha, rfl⟩
  rw [h]
  exact ((Set.finite_univ : (Set.univ : Set (Root n)).Finite).prod hS).image _

theorem normal_finitelyGenerated (hS : S.Finite) :
    (normal (n := n) S).IsFinitelyNormallyGenerated :=
  ⟨rootRelations S, rootRelations_finite S hS, rfl⟩

/-- Passing to the quotient by finitely many relators preserves finite presentation of the
Steinberg group, over every unital ring and in rank at least five. -/
theorem finitelyPresented (hn : 5 ≤ n) (hS : S.Finite)
    [Group.IsFinitelyPresented (Steinberg n R)] :
    Group.IsFinitelyPresented (Steinberg n (Coeff S)) := by
  have : Group.IsFinitelyPresented (Quot (n := n) S) :=
    Group.IsFinitelyPresented.quotient (normal S) (normal_finitelyGenerated S hS)
  exact Group.IsFinitelyPresented.equiv (equiv S hn)

end SteinbergQuotient

/-- Manuscript Theorem 10.1 over the prime field: for a finite alphabet and a finite set of
relators, the Steinberg group of the quotient algebra is finitely presented in rank at least
five. -/
theorem steinberg_finitelyPresented {ℓ n : ℕ} [NeZero ℓ] (hn : 5 ≤ n) {α : Type u} [Finite α]
    (S : Set (MonomialCompletion.Polynomial ℓ α)) (hS : S.Finite) :
    Group.IsFinitelyPresented (Steinberg n (SteinbergQuotient.Coeff S)) := by
  have : Group.IsFinitelyPresented (Steinberg n (MonomialCompletion.Polynomial ℓ α)) :=
    FiniteSteinbergPresentation.free_finitelyPresented hn
  exact SteinbergQuotient.finitelyPresented S hn hS

end AllPrimeGroups
