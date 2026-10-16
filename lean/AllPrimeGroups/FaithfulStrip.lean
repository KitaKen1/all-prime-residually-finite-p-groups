/-
Adapted from OpenAI PeriodicGroups/Steinberg/KernelRelations.lean,
commit pinned in upstream/provenance.json. Apache-2.0, see upstream/OpenAI-LICENSE.
These rectangular-strip arguments work over any unital ring.
-/
import AllPrimeGroups.MatrixModel
import Mathlib.GroupTheory.NoncommPiCoprod

namespace AllPrimeGroups.Kernel
universe u
open scoped BigOperators
noncomputable section
open Classical
variable {n : ℕ} {R : Type u} [Ring R]

def rootHom (p : Root n) : Multiplicative R →* Steinberg n R where
  toFun a := Steinberg.x p a.toAdd
  map_one' := Steinberg.x_zero p
  map_mul' a b := Steinberg.x_add p a.toAdd b.toAdd

abbrev RectIndex (H L : Finset (Fin n)) := {i // i ∈ H} × {j // j ∈ L}

variable (H L : Finset (Fin n)) (hHL : Disjoint H L)

def rectPosition (p : RectIndex H L) : Root n :=
  ⟨p.1.val, p.2.val, fun h => Finset.disjoint_left.mp hHL p.1.property (h ▸ p.2.property)⟩

lemma rect_commute (p q : RectIndex H L) (a b : R) :
    Commute (Steinberg.x (rectPosition H L hHL p) a)
      (Steinberg.x (rectPosition H L hHL q) b) := by
  apply Steinberg.x_commute
  · intro h
    change p.2.val = q.1.val at h
    exact Finset.disjoint_left.mp hHL q.1.property (h ▸ p.2.property)
  · intro h
    change p.1.val = q.2.val at h
    exact Finset.disjoint_left.mp hHL p.1.property (h ▸ q.2.property)

def rectRoot : (RectIndex H L → Multiplicative R) →* Steinberg n R :=
  MonoidHom.noncommPiCoprod (fun p => rootHom (rectPosition H L hHL p))
    (fun p q _ a b => rect_commute H L hHL p q a.toAdd b.toAdd)

@[simp] lemma rectRoot_single (p : RectIndex H L) (a : R) :
    rectRoot H L hHL (Pi.mulSingle p (Multiplicative.ofAdd a)) =
      Steinberg.x (rectPosition H L hHL p) a :=
  MonoidHom.noncommPiCoprod_mulSingle _ _ _

def rectMatrix (A : RectIndex H L → Multiplicative R) : Matrix (Fin n) (Fin n) R :=
  fun i j => if hi : i ∈ H then if hj : j ∈ L then (A (⟨i, hi⟩, ⟨j, hj⟩)).toAdd
    else 0 else 0

@[simp] lemma rectMatrix_entry (A : RectIndex H L → Multiplicative R)
    (p : RectIndex H L) : rectMatrix H L A p.1.val p.2.val = (A p).toAdd := by
  simp [rectMatrix, p.1.property, p.2.property]

@[simp] lemma rectMatrix_one : rectMatrix H L (1 : RectIndex H L → Multiplicative R) = 0 := by
  ext i j
  simp [rectMatrix]

@[simp] lemma rectMatrix_mul (A B : RectIndex H L → Multiplicative R) :
    rectMatrix H L (A * B) = rectMatrix H L A + rectMatrix H L B := by
  ext i j
  simp only [rectMatrix, Matrix.add_apply]
  split_ifs <;> simp_all

include hHL in
lemma rectMatrix_product (A B : RectIndex H L → Multiplicative R) :
    rectMatrix H L A * rectMatrix H L B = 0 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.zero_apply]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hk : k ∈ H
  · have hk' : k ∉ L := fun hl => Finset.disjoint_left.mp hHL hk hl
    simp [rectMatrix, hk']
  · simp [rectMatrix, hk]

def rectUnits : (RectIndex H L → Multiplicative R) →*
    (Matrix (Fin n) (Fin n) R)ˣ where
  toFun A :=
    { val := 1 + rectMatrix H L A
      inv := 1 - rectMatrix H L A
      val_inv := by
        simp [add_mul, mul_sub, rectMatrix_product H L hHL]
      inv_val := by
        simp [sub_mul, mul_add, rectMatrix_product H L hHL] }
  map_one' := by apply Units.ext; simp
  map_mul' A B := by
    apply Units.ext
    simp only [Units.val_mul, rectMatrix_mul]
    simp [add_mul, mul_add, rectMatrix_product H L hHL, add_assoc]

@[simp] lemma coe_rectUnits (A : RectIndex H L → Multiplicative R) :
    (rectUnits H L hHL A).val = 1 + rectMatrix H L A := rfl

lemma rectMatrix_single (p : RectIndex H L) (a : R) :
    rectMatrix H L (Pi.mulSingle p (Multiplicative.ofAdd a)) =
      Matrix.single p.1.val p.2.val a := by
  ext i j
  by_cases hi : i ∈ H
  · by_cases hj : j ∈ L
    · simp only [rectMatrix, dite_eq_left hi, dite_eq_left hj, Matrix.single_apply]
      by_cases hp : p = (⟨i, hi⟩, ⟨j, hj⟩)
      · subst p
        simp
      · have hp' : ¬ (p.1.val = i ∧ p.2.val = j) := by
          rintro ⟨h₁, h₂⟩
          apply hp
          exact Prod.ext (Subtype.ext h₁) (Subtype.ext h₂)
        simp [hp, hp']
    · have hn : p.2.val ≠ j := by intro h; exact hj (h ▸ p.2.property)
      simp [rectMatrix, hi, hj, hn]
  · have hn : p.1.val ≠ i := by intro h; exact hi (h ▸ p.1.property)
    simp [rectMatrix, hi, hn]

@[simp] lemma rectUnits_single (p : RectIndex H L) (a : R) :
    rectUnits H L hHL (Pi.mulSingle p (Multiplicative.ofAdd a)) =
      Elementary.e (rectPosition H L hHL p) a := by
  apply Units.ext
  rw [coe_rectUnits, rectMatrix_single]
  rfl

lemma representation_rectRoot :
    Elementary.representation.comp (rectRoot H L hHL (R := R)) = rectUnits H L hHL := by
  apply MonoidHom.pi_ext
  intro p a
  change Elementary.representation (rectRoot H L hHL (Pi.mulSingle p a)) =
    rectUnits H L hHL (Pi.mulSingle p a)
  change Elementary.representation
    (rectRoot H L hHL (Pi.mulSingle p (Multiplicative.ofAdd a.toAdd))) =
    rectUnits H L hHL (Pi.mulSingle p (Multiplicative.ofAdd a.toAdd))
  rw [rectRoot_single, rectUnits_single, Elementary.representation_x]

lemma rectUnits_injective : Function.Injective (rectUnits H L hHL (R := R)) := by
  intro A B h
  have hm := congrArg (fun x : (Matrix (Fin n) (Fin n) R)ˣ => x.val) h
  have he : rectMatrix H L A = rectMatrix H L B := add_left_cancel hm
  funext p
  apply Multiplicative.toAdd.injective
  simpa using congrArg (fun M : Matrix (Fin n) (Fin n) R => M p.1.val p.2.val) he

def Strip : Subgroup (Steinberg n R) :=
  Subgroup.closure {g | ∃ (p : RectIndex H L) (a : R),
    g = Steinberg.x (rectPosition H L hHL p) a}

lemma strip_le_range : Strip H L hHL ≤ (rectRoot H L hHL (R := R)).range := by
  apply (Subgroup.closure_le _).mpr
  rintro g ⟨p, a, rfl⟩
  exact ⟨Pi.mulSingle p (Multiplicative.ofAdd a), rectRoot_single H L hHL p a⟩

theorem strip_faithful {g : Steinberg n R} (hg : g ∈ Strip H L hHL)
    (hmat : Elementary.representation g = 1) : g = 1 := by
  obtain ⟨A, rfl⟩ := strip_le_range H L hHL hg
  have hr : rectUnits H L hHL A = 1 := by
    rw [← MonoidHom.comp_apply, representation_rectRoot] at hmat
    exact hmat
  have ha : A = 1 := rectUnits_injective H L hHL (hr.trans (map_one _).symm)
  rw [ha, map_one]


end
end AllPrimeGroups.Kernel
