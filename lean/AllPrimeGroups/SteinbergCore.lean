/-
The presented Steinberg group and its elementary API are extracted from OpenAI's
PeriodicGroups/Steinberg/PresentationModel.lean, pinned in upstream/provenance.json.
Apache-2.0; see upstream/OpenAI-LICENSE. Definitions and proofs below retain the
original mathematical presentation; the namespace, imports, and adapters are local.
-/
import AllPrimeGroups.RootCalculus
import Mathlib.GroupTheory.PresentedGroup

namespace AllPrimeGroups
universe u v

structure Root (n : ℕ) where
  row : Fin n
  col : Fin n
  ne : row ≠ col
  deriving DecidableEq

abbrev Generator (n : ℕ) (R : Type u) := Root n × R

def letter {n : ℕ} {R : Type u} (p : Root n) (a : R) :
    FreeGroup (Generator n R) := FreeGroup.of (p, a)

inductive SteinbergRel (n : ℕ) (R : Type u) [Ring R] :
    FreeGroup (Generator n R) → Prop
  | add (p : Root n) (a b : R) :
      SteinbergRel n R (letter p (a + b) * (letter p a * letter p b)⁻¹)
  | commute (p q : Root n) (h₁ : p.col ≠ q.row) (h₂ : p.row ≠ q.col) (a b : R) :
      SteinbergRel n R (bracket (letter p a) (letter q b))
  | mul (i j k : Fin n) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a b : R) :
      SteinbergRel n R
        (bracket (letter ⟨i, j, hij⟩ a) (letter ⟨j, k, hjk⟩ b) *
          (letter ⟨i, k, hik⟩ (a * b))⁻¹)

def Steinberg (n : ℕ) (R : Type u) [Ring R] :=
  PresentedGroup {r | SteinbergRel n R r}
  deriving Group

@[simp] theorem map_bracket {G : Type u} {H : Type v} [Group G] [Group H]
    (f : G →* H) (a b : G) : f (bracket a b) = bracket (f a) (f b) := by
  simp [bracket]

namespace Steinberg

variable {n : ℕ} {R : Type u} [Ring R]

def x (p : Root n) (a : R) : Steinberg n R := PresentedGroup.of (p, a)

@[simp] theorem x_add (p : Root n) (a b : R) : x p (a + b) = x p a * x p b := by
  exact PresentedGroup.mk_eq_mk_of_mul_inv_mem (SteinbergRel.add p a b)

@[simp] theorem x_zero (p : Root n) : x p (0 : R) = 1 := by
  have h := x_add p (0 : R) 0
  simp only [zero_add] at h
  exact mul_left_cancel (h.symm.trans (mul_one _).symm)

@[simp] theorem x_neg (p : Root n) (a : R) : x p (-a) = (x p a)⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  rw [← x_add, add_neg_cancel, x_zero]

theorem x_commute (p q : Root n) (h₁ : p.col ≠ q.row) (h₂ : p.row ≠ q.col)
    (a b : R) : Commute (x p a) (x q b) := by
  apply (bracket_eq_one_iff _ _).mp
  have h := PresentedGroup.one_of_mem (SteinbergRel.commute p q h₁ h₂ a b)
  simp only [bracket, map_mul] at h
  exact h

theorem x_mul (i j k : Fin n) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (a b : R) :
    bracket (x ⟨i, j, hij⟩ a) (x ⟨j, k, hjk⟩ b) = x ⟨i, k, hik⟩ (a * b) := by
  have h := PresentedGroup.mk_eq_mk_of_mul_inv_mem (SteinbergRel.mul i j k hij hjk hik a b)
  simp only [bracket, map_mul] at h
  exact h

def lift {G : Type v} [Group G] (f : Root n → R → G)
    (ha : ∀ p a b, f p (a + b) = f p a * f p b)
    (hc : ∀ p q, p.col ≠ q.row → p.row ≠ q.col → ∀ a b, Commute (f p a) (f q b))
    (hm : ∀ i j k hij hjk hik a b,
      bracket (f ⟨i, j, hij⟩ a) (f ⟨j, k, hjk⟩ b) = f ⟨i, k, hik⟩ (a * b)) :
    Steinberg n R →* G :=
  PresentedGroup.toGroup (f := fun g => f g.1 g.2) (by
    intro r hr
    cases hr with
    | add p a b => simp [letter, ha]
    | commute p q h₁ h₂ a b =>
      simpa [letter] using (bracket_eq_one_iff _ _).mpr (hc p q h₁ h₂ a b)
    | mul i j k hij hjk hik a b =>
      simp only [map_mul, map_inv, map_bracket, letter, FreeGroup.lift_apply_of]
      rw [hm i j k hij hjk hik a b, mul_inv_cancel])

@[simp] theorem lift_x {G : Type v} [Group G] (f : Root n → R → G) ha hc hm
    (p : Root n) (a : R) : lift f ha hc hm (x p a) = f p a :=
  PresentedGroup.toGroup.of _

@[ext] theorem hom_ext {G : Type v} [Group G] {f g : Steinberg n R →* G}
    (h : ∀ p a, f (x p a) = g (x p a)) : f = g := by
  apply PresentedGroup.ext
  rintro ⟨p, a⟩
  exact h p a

theorem closure_range_x : Subgroup.closure (Set.range (fun g : Generator n R => x g.1 g.2)) = ⊤ :=
  PresentedGroup.closure_range_of _

def map {S : Type v} [Ring S] (f : R →+* S) : Steinberg n R →* Steinberg n S :=
  lift (fun p a => x p (f a)) (by simp) (by intros; apply x_commute <;> assumption)
    (by intros; simpa using x_mul _ _ _ _ _ _ _ _)

@[simp] theorem map_x {S : Type v} [Ring S] (f : R →+* S) (p : Root n) (a : R) :
    map f (x p a) = x p (f a) := lift_x _ _ _ _ _ _

end Steinberg

namespace Steinberg
variable {n : ℕ} {R : Type u} [Ring R]

noncomputable def indexedRoot (i j : Fin n) (a : R) : Steinberg n R := by
  classical
  exact if h : i ≠ j then x ⟨i, j, h⟩ a else 1

noncomputable def rootFamily : RootFamily (Fin n) R (Steinberg n R) where
  x := indexedRoot
  zero := by
    intro i j
    classical
    by_cases h : i ≠ j <;> simp [indexedRoot, h]
  commute := by
    intro i j k l h₁ h₂ a b
    classical
    by_cases hij : i ≠ j
    · by_cases hkl : k ≠ l
      · simpa [indexedRoot, hij, hkl] using x_commute ⟨i, j, hij⟩ ⟨k, l, hkl⟩ h₁ h₂ a b
      · simp [indexedRoot, hkl]
    · simp [indexedRoot, hij]
  product := by
    intro i j k hij hjk hik a b
    classical
    simpa [indexedRoot, hij, hjk, hik] using x_mul i j k hij hjk hik a b

theorem indexedRoot_add (i j : Fin n) (a b : R) :
    indexedRoot i j (a + b) = indexedRoot i j a * indexedRoot i j b := by
  classical
  by_cases h : i ≠ j <;> simp [indexedRoot, h]

/-- Cut movement in the concrete presented Steinberg group, not only a root-family interface. -/
theorem move_cut {i h j : Fin n} (hih : i ≠ h) (hhj : h ≠ j) (hij : i ≠ j)
    (a b c : R) (hca : c * a = 0) :
    bracket (x ⟨i, j, hij⟩ (a * b)) (x ⟨j, i, hij.symm⟩ c) =
      bracket (x ⟨i, h, hih⟩ a) (x ⟨h, i, hih.symm⟩ (b * c)) := by
  simpa [rootFamily, indexedRoot, hij, hij.symm, hih, hih.symm] using
    (rootFamily (n := n) (R := R)).move_cut hih hhj hij a b c hca

/-- The opposite-root commutator has exponent dividing p under the zero-product hypothesis. -/
theorem opposite_commutator_pow_char (p : ℕ) [CharP R p]
    {i h j : Fin n} (hih : i ≠ h) (hhj : h ≠ j) (hij : i ≠ j)
    (a c : R) (hca : c * a = 0) :
    bracket (x ⟨i, j, hij⟩ a) (x ⟨j, i, hij.symm⟩ c) ^ p = 1 := by
  simpa [rootFamily, indexedRoot, hij, hij.symm] using
    (rootFamily (n := n) (R := R)).opposite_commutator_pow_char p indexedRoot_add
      hih hhj hij a c hca

end Steinberg
end AllPrimeGroups
