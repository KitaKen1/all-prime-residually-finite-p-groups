/-
Generic stabilization and spare-coordinate centrality adapted from OpenAI
PeriodicGroups/Steinberg/KernelRelations.lean. Apache-2.0; provenance is pinned.
This proves centrality AFTER adding a coordinate, not finite-rank injectivity.
-/
import AllPrimeGroups.FaithfulStrip
import Mathlib.GroupTheory.IsPerfect
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Reindex

universe u v

namespace AllPrimeGroups
namespace Root

def map {n m : ℕ} (f : Fin n → Fin m) (hf : Function.Injective f) (p : Root n) : Root m :=
  ⟨f p.row, f p.col, fun h => p.ne (hf h)⟩
end Root

namespace Steinberg
variable {n m : ℕ} {R : Type u} [Ring R]

def coordinateMap (f : Fin n → Fin m) (hf : Function.Injective f) :
    Steinberg n R →* Steinberg m R :=
  lift (fun p a => x (p.map f hf) a)
    (fun _ _ _ => x_add _ _ _)
    (fun _p _q h₁ h₂ a b => x_commute _ _ (fun h => h₁ (hf h)) (fun h => h₂ (hf h)) a b)
    (fun i j k hij hjk hik a b =>
      x_mul (f i) (f j) (f k) (fun h => hij (hf h)) (fun h => hjk (hf h))
        (fun h => hik (hf h)) a b)

@[simp] theorem coordinateMap_x (f : Fin n → Fin m) (hf : Function.Injective f)
    (p : Root n) (a : R) : coordinateMap f hf (x p a) = x (p.map f hf) a :=
  lift_x _ _ _ _ _ _

lemma conjugate_chain (i j k : Fin n) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (a b : R) :
    x ⟨i,j,hij⟩ a * x ⟨j,k,hjk⟩ b * (x ⟨i,j,hij⟩ a)⁻¹ =
      x ⟨i,k,hik⟩ (a*b) * x ⟨j,k,hjk⟩ b := by
  calc
    _ = bracket (x ⟨i,j,hij⟩ a) (x ⟨j,k,hjk⟩ b) * x ⟨j,k,hjk⟩ b := by
      simp [bracket, mul_assoc]
    _ = _ := by rw [x_mul]

lemma conjugate_reverse (i j k : Fin n) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (a b : R) :
    x ⟨j,k,hjk⟩ b * x ⟨i,j,hij⟩ a * (x ⟨j,k,hjk⟩ b)⁻¹ =
      x ⟨i,k,hik⟩ (-(a*b)) * x ⟨i,j,hij⟩ a := by
  calc
    _ = (bracket (x ⟨i,j,hij⟩ a) (x ⟨j,k,hjk⟩ b))⁻¹ * x ⟨i,j,hij⟩ a := by
      simp [bracket, mul_assoc]
    _ = _ := by rw [x_mul, x_neg]

lemma conjugate_commute (p q : Root n) (h₁ : p.col ≠ q.row) (h₂ : p.row ≠ q.col)
    (a b : R) : x p a * x q b * (x p a)⁻¹ = x q b := by
  rw [(x_commute p q h₁ h₂ a b).eq, mul_inv_cancel_right]

lemma outside (hn : 3 ≤ n) (p : Root n) : ∃ k : Fin n, k ≠ p.row ∧ k ≠ p.col := by
  have hc : ({p.row,p.col} : Finset (Fin n)).card < (Finset.univ : Finset (Fin n)).card := by
    have h := (Finset.card_le_two : ({p.row,p.col} : Finset (Fin n)).card ≤ 2)
    simpa using (lt_of_le_of_lt h (show 2 < n by omega))
  obtain ⟨k, _, hk⟩ := Finset.exists_mem_notMem_of_card_lt_card hc
  exact ⟨k, by simpa using hk⟩

theorem commutator_eq_top (hn : 3 ≤ n) : commutator (Steinberg n R) = ⊤ := by
  apply top_unique
  rw [← closure_range_x]
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨⟨p,a⟩,rfl⟩
  obtain ⟨k,hki,hkj⟩ := outside hn p
  have hb := x_mul p.row k p.col hki.symm hkj p.ne a (1 : R)
  rw [mul_one] at hb
  change x p a ∈ commutator (Steinberg n R)
  change _ = x p a at hb
  rw [← hb, commutator_eq_closure]
  exact Subgroup.subset_closure ⟨x ⟨p.row,k,hki.symm⟩ a, x ⟨k,p.col,hkj⟩ 1, rfl⟩

theorem hom_to_commGroup_trivial (hn : 3 ≤ n) {A : Type v} [CommGroup A]
    (f : Steinberg n R →* A) : f = 1 := by
  apply hom_ext
  intro p a
  obtain ⟨k,hki,hkj⟩ := outside hn p
  have hb := x_mul p.row k p.col hki.symm hkj p.ne a (1 : R)
  rw [mul_one] at hb
  rw [← hb, map_bracket]
  simp [bracket, mul_comm]

end Steinberg
end AllPrimeGroups
namespace AllPrimeGroups.Kernel
noncomputable section
open Classical
variable {n : ℕ} {R : Type*} [Ring R]
def awayCoordinates (t : Fin n) : Finset (Fin n) := Finset.univ.erase t
lemma away_disjoint (t : Fin n) : Disjoint (awayCoordinates t) {t} := by
  simp [awayCoordinates]
def columnStrip (t : Fin n) : Subgroup (Steinberg n R) := Strip (awayCoordinates t) {t} (away_disjoint t)
def rowStrip (t : Fin n) : Subgroup (Steinberg n R) := Strip {t} (awayCoordinates t) (away_disjoint t).symm
lemma column_root_mem (t i : Fin n) (hi : i≠t) (a : R) :
    Steinberg.x ⟨i,t,hi⟩ a∈columnStrip t := by
  apply Subgroup.subset_closure
  refine ⟨(⟨i,by simp [awayCoordinates,hi]⟩,⟨t,by simp⟩),a,rfl⟩
lemma row_root_mem (t i : Fin n) (hi : t≠i) (a : R) :
    Steinberg.x ⟨t,i,hi⟩ a∈rowStrip t := by
  apply Subgroup.subset_closure
  refine ⟨(⟨t,by simp⟩,⟨i,by simp [awayCoordinates,Ne.symm hi]⟩),a,rfl⟩
lemma conjugate_column_root_mem (t : Fin n) (p : Root n) (hpt : p.row≠t) (hct : p.col≠t)
    (a : R) (i : Fin n) (hi : i≠t) (b : R) :
    Steinberg.x p a * Steinberg.x ⟨i,t,hi⟩ b * (Steinberg.x p a)⁻¹∈columnStrip t := by
  by_cases hc : p.col=i
  · have he := Steinberg.conjugate_chain p.row i t (hc ▸ p.ne) hi hpt a b
    have hp : p=⟨p.row,i,hc ▸ p.ne⟩ := by cases p;cases hc;rfl
    rw [hp,he]
    exact (columnStrip t).mul_mem (column_root_mem t _ hpt _) (column_root_mem t _ hi _)
  · rw [Steinberg.conjugate_commute p ⟨i,t,hi⟩ hc hpt]
    exact column_root_mem t i hi b
lemma conjugate_row_root_mem (t : Fin n) (p : Root n) (hpt : p.row≠t) (hct : p.col≠t)
    (a : R) (i : Fin n) (hi : t≠i) (b : R) :
    Steinberg.x p a * Steinberg.x ⟨t,i,hi⟩ b * (Steinberg.x p a)⁻¹∈rowStrip t := by
  by_cases hr : p.row=i
  · have he := Steinberg.conjugate_reverse t i p.col hi (hr ▸ p.ne) hct.symm b a
    have hp : p=⟨i,p.col,hr ▸ p.ne⟩ := by cases p;cases hr;rfl
    rw [hp,he]
    exact (rowStrip t).mul_mem (row_root_mem t _ hct.symm _) (row_root_mem t _ hi _)
  · rw [Steinberg.conjugate_commute p ⟨t,i,hi⟩ hct hr]
    exact row_root_mem t i hi b
lemma conjugate_column_mem (t : Fin n) (p : Root n) (hpt : p.row≠t) (hct : p.col≠t)
    (a : R) {g : Steinberg n R} (hg : g∈columnStrip t) :
    Steinberg.x p a * g * (Steinberg.x p a)⁻¹∈columnStrip t := by
  have H : columnStrip (R:=R) t ≤ (columnStrip t).comap (MulAut.conj (Steinberg.x p a)).toMonoidHom := by
    apply (Subgroup.closure_le _).mpr
    rintro g ⟨⟨⟨i,hi⟩,⟨j,hj⟩⟩,b,rfl⟩
    have hj' : j=t := Finset.mem_singleton.mp hj
    subst j
    have hi' : i≠t := by simpa [awayCoordinates] using hi
    exact conjugate_column_root_mem t p hpt hct a i hi' b
  exact H hg
lemma conjugate_row_mem (t : Fin n) (p : Root n) (hpt : p.row≠t) (hct : p.col≠t)
    (a : R) {g : Steinberg n R} (hg : g∈rowStrip t) :
    Steinberg.x p a * g * (Steinberg.x p a)⁻¹∈rowStrip t := by
  have H : rowStrip (R:=R) t ≤ (rowStrip t).comap (MulAut.conj (Steinberg.x p a)).toMonoidHom := by
    apply (Subgroup.closure_le _).mpr
    rintro g ⟨⟨⟨i,hi⟩,⟨j,hj⟩⟩,b,rfl⟩
    have hi' : i=t := Finset.mem_singleton.mp hi
    subst i
    have hj' : j≠t := by simpa [awayCoordinates] using hj
    exact conjugate_row_root_mem t p hpt hct a j hj'.symm b
  exact H hg

def away (t : Fin n) : Subgroup (Steinberg n R) :=
  Subgroup.closure {g | ∃(p : Root n)(a : R),p.row≠t ∧ p.col≠t ∧ g=Steinberg.x p a}
lemma away_le_column_normalizer (t : Fin n) :
    away (R:=R) t ≤ Subgroup.normalizer (columnStrip (R:=R) t : Set (Steinberg n R)) := by
  apply (Subgroup.closure_le _).mpr
  rintro g ⟨p,a,hpt,hct,rfl⟩
  apply Subgroup.mem_normalizer_iff.mpr
  intro x
  constructor
  · exact conjugate_column_mem t p hpt hct a
  · intro hx
    have H := conjugate_column_mem t p hpt hct (-a) hx
    simpa only [Steinberg.x_neg,inv_inv,mul_assoc,inv_mul_cancel_left,mul_inv_cancel_right,inv_mul_cancel,mul_one] using H
lemma away_le_row_normalizer (t : Fin n) :
    away (R:=R) t ≤ Subgroup.normalizer (rowStrip (R:=R) t : Set (Steinberg n R)) := by
  apply (Subgroup.closure_le _).mpr
  rintro g ⟨p,a,hpt,hct,rfl⟩
  apply Subgroup.mem_normalizer_iff.mpr
  intro x
  constructor
  · exact conjugate_row_mem t p hpt hct a
  · intro hx
    have H := conjugate_row_mem t p hpt hct (-a) hx
    simpa only [Steinberg.x_neg,inv_inv,mul_assoc,inv_mul_cancel_left,mul_inv_cancel_right,inv_mul_cancel,mul_one] using H
lemma kernel_commutes_column (t : Fin n) {g : Steinberg n R} (hg : g∈away t)
    (hmat : Elementary.representation g=1) (i : Fin n) (hi : i≠t) (a : R) :
    Commute g (Steinberg.x ⟨i,t,hi⟩ a) := by
  let x := Steinberg.x ⟨i,t,hi⟩ a
  have hx : x∈columnStrip t := column_root_mem t i hi a
  have hc : g*x*g⁻¹∈columnStrip t := (Subgroup.mem_normalizer_iff.mp (away_le_column_normalizer t hg) x).mp hx
  have H := strip_faithful (awayCoordinates t) {t} (away_disjoint t)
    ((columnStrip t).mul_mem hc ((columnStrip t).inv_mem hx)) (by simp [map_mul,map_inv,hmat])
  exact mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp H)
lemma kernel_commutes_row (t : Fin n) {g : Steinberg n R} (hg : g∈away t)
    (hmat : Elementary.representation g=1) (i : Fin n) (hi : t≠i) (a : R) :
    Commute g (Steinberg.x ⟨t,i,hi⟩ a) := by
  let x := Steinberg.x ⟨t,i,hi⟩ a
  have hx : x∈rowStrip t := row_root_mem t i hi a
  have hc : g*x*g⁻¹∈rowStrip t := (Subgroup.mem_normalizer_iff.mp (away_le_row_normalizer t hg) x).mp hx
  have H := strip_faithful {t} (awayCoordinates t) (away_disjoint t).symm
    ((rowStrip t).mul_mem hc ((rowStrip t).inv_mem hx)) (by simp [map_mul,map_inv,hmat])
  exact mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp H)

theorem supported_kernel_central (t : Fin n) {g : Steinberg n R} (hg : g∈away t)
    (hmat : Elementary.representation g=1) : g∈Subgroup.center (Steinberg n R) := by
  have hc (p : Root n) (a : R) : Commute g (Steinberg.x p a) := by
    by_cases hr : p.row=t
    · have hp : p=⟨t,p.col,hr ▸ p.ne⟩ := by cases p;cases hr;rfl
      rw [hp]
      exact kernel_commutes_row t hg hmat p.col (hr ▸ p.ne) a
    · by_cases ht : p.col=t
      · have hp : p=⟨p.row,t,ht ▸ p.ne⟩ := by cases p;cases ht;rfl
        rw [hp]
        exact kernel_commutes_column t hg hmat p.row (ht ▸ p.ne) a
      · have he := Steinberg.x_mul p.row t p.col hr (Ne.symm ht) p.ne a (1:R)
        rw [mul_one] at he
        have HH := CommutatorCalculus.commute_bracket_right
          (kernel_commutes_column t hg hmat p.row hr a)
          (kernel_commutes_row t hg hmat p.col (Ne.symm ht) 1)
        exact he ▸ HH
  have hf : (MulAut.conj g).toMonoidHom=MonoidHom.id (Steinberg n R) := by
    apply Steinberg.hom_ext
    intro p a
    change g*Steinberg.x p a*g⁻¹=Steinberg.x p a
    rw [(hc p a).eq,mul_inv_cancel_right]
  apply Subgroup.mem_center_iff.mpr
  intro x
  have H := DFunLike.congr_fun hf x
  change g*x*g⁻¹=x at H
  exact (mul_inv_eq_iff_eq_mul.mp H).symm
end
end AllPrimeGroups.Kernel

namespace AllPrimeGroups.Kernel
noncomputable section
open Classical
variable {n : ℕ} {R : Type*} [Ring R]
def coordinateEquiv (n : ℕ) : Fin n ⊕ Fin 1 ≃ Fin (n+1) := finSumFinEquiv
def coordinateIndex (n : ℕ) (i : Fin n) : Fin (n+1) := coordinateEquiv n (Sum.inl i)
lemma coordinateIndex_injective (n : ℕ) : Function.Injective (coordinateIndex n) :=
  (coordinateEquiv n).injective.comp Sum.inl_injective
def spareCoordinate (n : ℕ) : Fin (n+1) := coordinateEquiv n (Sum.inr 0)
lemma coordinateIndex_ne_spare (i : Fin n) : coordinateIndex n i≠spareCoordinate n := by
  intro he
  have := (coordinateEquiv n).injective he
  contradiction

def blockUnits (u : (Matrix (Fin n) (Fin n) R)ˣ) :
    (Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) R)ˣ where
  val := Matrix.fromBlocks u.val 0 0 1
  inv := Matrix.fromBlocks u.inv 0 0 1
  val_inv := by simp [Matrix.fromBlocks_multiply]
  inv_val := by simp [Matrix.fromBlocks_multiply]
def blockUnitsHom : (Matrix (Fin n) (Fin n) R)ˣ →* (Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) R)ˣ where
  toFun := blockUnits
  map_one' := by apply Units.ext;simp [blockUnits]
  map_mul' u v := by apply Units.ext;simp [blockUnits,Matrix.fromBlocks_multiply]
def padUnitsHom : (Matrix (Fin n) (Fin n) R)ˣ →* (Matrix (Fin (n+1)) (Fin (n+1)) R)ˣ :=
  (Units.map (Matrix.reindexRingEquiv R (coordinateEquiv n)).toMonoidHom).comp blockUnitsHom
lemma padUnitsHom_e (p : Root n) (a : R) :
    padUnitsHom (Elementary.e p a)=Elementary.e (p.map (coordinateIndex n) (coordinateIndex_injective n)) a := by
  apply Units.ext
  change (Matrix.fromBlocks (1+Matrix.single p.row p.col a) 0 0 1).submatrix
    (coordinateEquiv n).symm (coordinateEquiv n).symm =
      1+Matrix.single (coordinateIndex n p.row) (coordinateIndex n p.col) a
  apply Matrix.ext
  intro i j
  obtain ⟨i,rfl⟩ := (coordinateEquiv n).surjective i
  obtain ⟨j,rfl⟩ := (coordinateEquiv n).surjective j
  cases i <;> cases j <;>
    simp [coordinateIndex,Matrix.submatrix_apply,Matrix.fromBlocks,Matrix.add_apply,Matrix.one_apply,Matrix.single_apply]

def padSteinberg : Steinberg n R →* Steinberg (n+1) R :=
  Steinberg.coordinateMap (coordinateIndex n) (coordinateIndex_injective n)
lemma pad_representation :
    Elementary.representation.comp (padSteinberg (n:=n) (R:=R))=
      padUnitsHom.comp Elementary.representation := by
  apply Steinberg.hom_ext
  intro p a
  simp only [MonoidHom.comp_apply,padSteinberg,Steinberg.coordinateMap_x,Elementary.representation_x,padUnitsHom_e]
lemma pad_mem_away (g : Steinberg n R) : padSteinberg g∈away (spareCoordinate n) := by
  have H : (⊤ : Subgroup (Steinberg n R)) ≤ (away (spareCoordinate n)).comap padSteinberg := by
    rw [←Steinberg.closure_range_x]
    apply (Subgroup.closure_le _).mpr
    rintro x ⟨⟨p,a⟩,rfl⟩
    apply Subgroup.subset_closure
    exact ⟨p.map (coordinateIndex n) (coordinateIndex_injective n),a,
      coordinateIndex_ne_spare p.row,coordinateIndex_ne_spare p.col,by simp [padSteinberg]⟩
  exact H (Subgroup.mem_top g)

theorem stabilized_kernel_central (g : Steinberg n R) (hg : Elementary.representation g=1) :
    padSteinberg g∈Subgroup.center (Steinberg (n+1) R) := by
  apply supported_kernel_central (spareCoordinate n) (pad_mem_away g)
  have he := DFunLike.congr_fun (pad_representation (n:=n) (R:=R)) g
  simpa only [MonoidHom.comp_apply,hg,map_one] using he
end
end AllPrimeGroups.Kernel

namespace AllPrimeGroups.Steinberg
variable {n : ℕ} {R : Type*} [Ring R]

/-- Every rank at least three Steinberg group is perfect in mathlib's sense. -/
theorem isPerfect (hn : 3 ≤ n) : Group.IsPerfect (Steinberg n R) :=
  ⟨commutator_eq_top hn⟩

end AllPrimeGroups.Steinberg
