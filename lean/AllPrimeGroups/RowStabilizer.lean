import AllPrimeGroups.GLLift
import AllPrimeGroups.K1Stability
import AllPrimeGroups.CentralClosed
import Mathlib.GroupTheory.GroupExtension.Defs

/-! The central extension of the last-column stabilizer used in manuscript Section 12.

Its domain is the row group semidirect the smaller Steinberg group. The row action factors
through the elementary matrix representation. The map to the larger Steinberg group is
constructed from root words, without assuming injectivity of stabilization. -/

namespace AllPrimeGroups
namespace FrameStabilizer

open Matrix GLPres

variable {B : Type*} [Ring B] {m : ℕ}

def rowGen (b : Fin m) (a : B) : Steinberg (m + 1) B := Steinberg.x (GLPres.rowRoot b) a

theorem rowGen_add (b : Fin m) (a a' : B) :
    rowGen b (a + a') = rowGen b a * rowGen b a' := Steinberg.x_add _ _ _

theorem rowGen_zero (b : Fin m) : rowGen b (0 : B) = 1 := Steinberg.x_zero _

theorem rowGen_commute (b b' : Fin m) (a a' : B) : Commute (rowGen b a) (rowGen b' a') :=
  Steinberg.x_commute _ _ (GLPres.castSucc_ne_last' b)
    (GLPres.castSucc_ne_last' b').symm a a'

def rowLiftFun (r : Fin m → B) : Steinberg (m + 1) B :=
  ((List.finRange m).map fun b => rowGen b (r b)).prod

def rowLift : Row m B →* Steinberg (m + 1) B where
  toFun r := rowLiftFun (Multiplicative.toAdd r)
  map_one' := by
    simp only [toAdd_one, rowLiftFun, Pi.zero_apply, rowGen_zero]
    exact List.prod_eq_one fun x hx => by
      obtain ⟨b, -, rfl⟩ := List.mem_map.mp hx
      rfl
  map_mul' r r' := by
    simp only [toAdd_mul, rowLiftFun, Pi.add_apply, rowGen_add]
    exact GLPres.list_prod_map_mul _ _ _ (fun i _ j _ => rowGen_commute i j _ _)

theorem representation_rowLift (r : Row m B) :
    Elementary.representation (rowLift r) = rowMatHom r := by
  show Elementary.representation (rowLiftFun (Multiplicative.toAdd r)) =
    rowMat (Multiplicative.toAdd r)
  rw [rowLiftFun, map_list_prod, List.map_map, rowMat, LocalGL.rowProd]
  congr 1
  apply List.map_congr_left
  intro b _
  exact Elementary.representation_x _ _

theorem rowLift_single (b : Fin m) (a : B) :
    rowLift (Multiplicative.ofAdd (Pi.single b a)) = rowGen b a := by
  show rowLiftFun (Pi.single b a) = rowGen b a
  rw [rowLiftFun]
  have e : (fun b' => rowGen b' ((Pi.single b a : Fin m → B) b')) =
      fun b' => if b' = b then rowGen b a else 1 := by
    funext b'
    by_cases h : b' = b
    · subst h
      simp
    · simp [h, rowGen_zero]
  rw [e, GLPres.list_prod_single (fun _ => rowGen b a) b _ (List.nodup_finRange m)]
  simp

theorem pad_conj_rowGen (p : Root m) (c : B) (b : Fin m) (a : B) :
    Kernel.padSteinberg (Steinberg.x p c) * rowGen b a *
      (Kernel.padSteinberg (Steinberg.x p c))⁻¹ =
      rowGen b a * rowGen p.col (if b = p.row then -(a * c) else 0) := by
  rw [Kernel.padSteinberg, Steinberg.coordinateMap_x]
  by_cases hb : b = p.row
  · subst hb
    simp only [↓reduceIte]
    have key : bracket (rowGen p.row (-a))
        (Steinberg.x (p.map (Kernel.coordinateIndex m) (Kernel.coordinateIndex_injective m)) c) =
        rowGen p.col (-a * c) :=
      Steinberg.x_mul (Fin.last m) p.row.castSucc p.col.castSucc
        (GLPres.castSucc_ne_last' _).symm ((Fin.castSucc_injective m).ne p.ne)
        (GLPres.castSucc_ne_last' _).symm (-a) c
    rw [show rowGen p.row (-a) = (rowGen p.row a)⁻¹ from Steinberg.x_neg _ _,
      bracket, inv_inv, neg_mul] at key
    rw [← key]
    group
  · simp only [hb, ↓reduceIte, rowGen_zero, mul_one]
    have hc := Steinberg.x_commute
      (p.map (Kernel.coordinateIndex m) (Kernel.coordinateIndex_injective m)) (GLPres.rowRoot b)
      (by rw [GLPres.castRoot_col, GLPres.rowRoot_row]; exact GLPres.castSucc_ne_last' _)
      (by rw [GLPres.castRoot_row, GLPres.rowRoot_col];
          exact (Fin.castSucc_injective m).ne (Ne.symm hb)) c a
    change Commute (Steinberg.x (p.map (Kernel.coordinateIndex m)
      (Kernel.coordinateIndex_injective m)) c) (rowGen b a) at hc
    rw [hc.eq, mul_inv_cancel_right]

theorem pad_conj_rowLift (z : Steinberg m B) (r : Row m B) :
    Kernel.padSteinberg z * rowLift r * (Kernel.padSteinberg z)⁻¹ =
      rowLift (rowAct (Elementary.representation z) r) := by
  have hz : z ∈ Subgroup.closure (Set.range (fun pa : Root m × B => Steinberg.x pa.1 pa.2)) := by
    rw [Steinberg.closure_range_x]
    trivial
  revert r
  induction hz using Subgroup.closure_induction with
  | mem z hz =>
    obtain ⟨⟨p, c⟩, rfl⟩ := hz
    intro r
    have hext : (MulAut.conj (Kernel.padSteinberg (Steinberg.x p c))).toMonoidHom.comp rowLift =
        rowLift.comp (rowAct (Elementary.e p c)).toMonoidHom := by
      apply GLPres.row_hom_ext
      intro b a
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        rowLift_single]
      rw [pad_conj_rowGen]
      show _ = rowLift (Multiplicative.ofAdd ((Pi.single b a : Fin m → B) ᵥ*
        (((Elementary.e p c)⁻¹ : (Matrix (Fin m) (Fin m) B)ˣ) : Matrix (Fin m) (Fin m) B)))
      rw [Elementary.e_inv, GLPres.single_vecMul_e, ofAdd_add,
        map_mul, rowLift_single]
      congr 1
      by_cases hb : b = p.row
      · simp [hb, rowLift_single, mul_neg]
      · simp [hb, rowGen_zero]
    rw [Elementary.representation_x]
    exact DFunLike.congr_fun hext r
  | one =>
    intro r
    simp
  | mul x y _ _ hx hy =>
    intro r
    rw [map_mul, mul_inv_rev, show Kernel.padSteinberg x * Kernel.padSteinberg y * rowLift r *
      ((Kernel.padSteinberg y)⁻¹ * (Kernel.padSteinberg x)⁻¹) =
      Kernel.padSteinberg x * (Kernel.padSteinberg y * rowLift r * (Kernel.padSteinberg y)⁻¹) *
        (Kernel.padSteinberg x)⁻¹ by group, hy, hx, map_mul, map_mul, MulAut.mul_apply]
  | inv x _ hx =>
    intro r
    have h := hx (rowAct (Elementary.representation x)⁻¹ r)
    have e : rowAct (Elementary.representation x) (rowAct (Elementary.representation x)⁻¹ r) = r := by
      rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
    rw [e] at h
    rw [map_inv Kernel.padSteinberg x, inv_inv, map_inv Elementary.representation x, ← h]
    group

def stRowAct : Steinberg m B →* MulAut (Row m B) := rowAct.comp Elementary.representation

abbrev Cover (m : ℕ) (B : Type*) [Ring B] := Row m B ⋊[stRowAct] Steinberg m B

/-- The map to the next rank. Injectivity is not assumed. -/
def toSteinberg : Cover m B →* Steinberg (m + 1) B :=
  SemidirectProduct.lift rowLift Kernel.padSteinberg (fun z => by
    refine MonoidHom.ext fun r => ?_
    exact (pad_conj_rowLift z r).symm)

theorem toSteinberg_inl (r : Row m B) :
    toSteinberg (SemidirectProduct.inl r : Cover m B) = rowLift r :=
  SemidirectProduct.lift_inl _ _ _ _

theorem toSteinberg_inr (z : Steinberg m B) :
    toSteinberg (SemidirectProduct.inr z : Cover m B) = Kernel.padSteinberg z :=
  SemidirectProduct.lift_inr _ _ _ _

def toRowGL : Cover m B →* Row m B ⋊[rowAct] (Matrix (Fin m) (Fin m) B)ˣ :=
  SemidirectProduct.map (MonoidHom.id _) Elementary.representation (fun _ => rfl)

def toMatrix : Cover m B →* (Matrix (Fin (m + 1)) (Fin (m + 1)) B)ˣ := GLPres.ι.comp toRowGL

theorem toMatrix_apply (x : Cover m B) :
    toMatrix x = rowMatHom x.left * Kernel.padUnitsHom (Elementary.representation x.right) := rfl

theorem representation_toSteinberg :
    Elementary.representation.comp (toSteinberg (m := m) (B := B)) = toMatrix := by
  apply SemidirectProduct.hom_ext
  · apply MonoidHom.ext
    intro r
    simp only [MonoidHom.comp_apply, toSteinberg_inl, representation_rowLift, toMatrix_apply,
      SemidirectProduct.left_inl, SemidirectProduct.right_inl, map_one, mul_one]
  · apply MonoidHom.ext
    intro z
    simp only [MonoidHom.comp_apply, toSteinberg_inr, toMatrix_apply,
      SemidirectProduct.left_inr, SemidirectProduct.right_inr, map_one, one_mul]
    exact DFunLike.congr_fun Kernel.pad_representation z

theorem toMatrix_eq_one_iff (x : Cover m B) :
    toMatrix x = 1 ↔ x.left = 1 ∧ Elementary.representation x.right = 1 := by
  constructor
  · intro h
    have hx : toRowGL x = 1 := GLPres.ι_injective (h.trans (map_one GLPres.ι).symm)
    exact ⟨congrArg SemidirectProduct.left hx, congrArg SemidirectProduct.right hx⟩
  · rintro ⟨hl, hr⟩
    have hx : toRowGL x = 1 := SemidirectProduct.ext hl hr
    rw [toMatrix, MonoidHom.comp_apply, hx, map_one]

theorem toMatrix_last (x : Cover m B) :
    (toMatrix x : Matrix (Fin (m + 1)) (Fin (m + 1)) B) *ᵥ Pi.single (Fin.last m) 1 =
      Pi.single (Fin.last m) 1 := GLPres.ι_last _

theorem toMatrix_mem_E (x : Cover m B) : toMatrix x ∈ K1.E (m + 1) B :=
  ⟨toSteinberg x, DFunLike.congr_fun representation_toSteinberg x⟩

theorem row_single_bracket (i j : Fin m) (hij : i ≠ j) (a : B) :
    bracket (SemidirectProduct.inl (Multiplicative.ofAdd (Pi.single i a)) : Cover m B)
      (SemidirectProduct.inr (Steinberg.x ⟨i, j, hij⟩ (1 : B))) =
      SemidirectProduct.inl (Multiplicative.ofAdd (Pi.single j a)) := by
  have hbr (r : Row m B) (z : Steinberg m B) :
      bracket (SemidirectProduct.inl r : Cover m B) (SemidirectProduct.inr z) =
        SemidirectProduct.inl (r * stRowAct z r⁻¹) := by
    rw [map_mul, SemidirectProduct.inl_aut, map_inv]
    simp only [bracket, map_inv]
    group
  rw [hbr]
  apply congrArg (SemidirectProduct.inl : Row m B → Cover m B)
  apply Multiplicative.toAdd.injective
  simp only [toAdd_mul, stRowAct, MonoidHom.comp_apply, Elementary.representation_x,
    rowAct_apply, toAdd_inv, toAdd_ofAdd, Elementary.e_inv]
  have hn : -(Pi.single i a : Fin m → B) = Pi.single i (-a) := by
    funext k
    by_cases hk : k = i <;> simp [hk]
  rw [hn,
    GLPres.single_vecMul_e]
  simp only [↓reduceIte, mul_neg, mul_one, neg_neg]
  rw [← hn]
  abel

theorem isPerfect (hm : 3 ≤ m) : Group.IsPerfect (Cover m B) := by
  have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have hsingle (b : Fin m) (a : B) :
      (SemidirectProduct.inl (Multiplicative.ofAdd (Pi.single b a)) : Cover m B) ∈
        commutator (Cover m B) := by
    obtain ⟨i, hi⟩ := exists_ne b
    rw [← row_single_bracket i b hi a, commutator_eq_closure]
    exact Subgroup.subset_closure ⟨_, _, rfl⟩
  have hq : (QuotientGroup.mk' (commutator (Cover m B))).comp
      (SemidirectProduct.inl : Row m B →* Cover m B) = 1 := by
    apply GLPres.row_hom_ext
    intro b a
    change (QuotientGroup.mk' (commutator (Cover m B)))
      (SemidirectProduct.inl (Multiplicative.ofAdd (Pi.single b a))) = 1
    rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
    exact hsingle b a
  have hR : (commutator (Steinberg m B)).map (SemidirectProduct.inr : Steinberg m B →* Cover m B) ≤
      commutator (Cover m B) := by
    rw [commutator_def, Subgroup.map_commutator, commutator_def]
    exact Subgroup.commutator_mono le_top le_top
  constructor
  apply top_unique
  intro x _
  rw [← SemidirectProduct.inl_left_mul_inr_right x]
  apply Subgroup.mul_mem
  · have h := DFunLike.congr_fun hq x.left
    rw [MonoidHom.comp_apply, MonoidHom.one_apply, ← MonoidHom.mem_ker,
      QuotientGroup.ker_mk'] at h
    exact h
  · exact hR ⟨x.right, by rw [Steinberg.commutator_eq_top hm]; trivial, rfl⟩

/-- The actual stabilizer of the last standard column in the elementary matrix group. -/
def LastColumnStabilizer (m : ℕ) (B : Type*) [Ring B] : Subgroup (K1.E (m + 1) B) where
  carrier := {A | (A.val : Matrix (Fin (m + 1)) (Fin (m + 1)) B) *ᵥ
    Pi.single (Fin.last m) 1 = Pi.single (Fin.last m) 1}
  one_mem' := Matrix.one_mulVec _
  mul_mem' {A A'} hA hA' := by
    show ((A.val * A'.val : (Matrix (Fin (m + 1)) (Fin (m + 1)) B)ˣ) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) B) *ᵥ _ = _
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, hA', hA]
  inv_mem' {A} hA := by
    have h := congrArg (fun v => ((A.val⁻¹ : (Matrix (Fin (m + 1)) (Fin (m + 1)) B)ˣ) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) B) *ᵥ v) hA
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at h
    exact h.symm

def toLastColumn : Cover m B →* LastColumnStabilizer m B where
  toFun x := ⟨⟨toMatrix x, toMatrix_mem_E x⟩, toMatrix_last x⟩
  map_one' := by apply Subtype.ext; apply Subtype.ext; exact map_one toMatrix
  map_mul' x y := by apply Subtype.ext; apply Subtype.ext; exact map_mul toMatrix x y

def kernelInclusion : (Elementary.representation (n := m) (R := B)).ker →* Cover m B :=
  SemidirectProduct.inr.comp (Elementary.representation (n := m) (R := B)).ker.subtype

theorem kernelInclusion_injective : Function.Injective (kernelInclusion (m := m) (B := B)) :=
  SemidirectProduct.inr_injective.comp Subtype.val_injective

theorem range_kernelInclusion : (kernelInclusion (m := m) (B := B)).range = toLastColumn.ker := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    apply Subtype.ext
    apply (toMatrix_eq_one_iff _).mpr
    exact ⟨rfl, z.property⟩
  · intro hx
    have hm : toMatrix x = 1 := congrArg (fun y : LastColumnStabilizer m B => y.val.val)
      (MonoidHom.mem_ker.mp hx)
    obtain ⟨hl, hr⟩ := (toMatrix_eq_one_iff x).mp hm
    refine ⟨⟨x.right, hr⟩, ?_⟩
    apply SemidirectProduct.ext
    · exact hl.symm
    · rfl

section Local
variable {K : Type*} [Field K] (ε : B →+* K) (hunit : ∀ b : B, ε b ≠ 0 → IsUnit b)

include hunit in
/-- The central kernel is exactly the smaller matrix kernel, with zero row component. -/
theorem kernel_central (hm : 6 ≤ m) {x : Cover m B} (hx : toMatrix x = 1) :
    x ∈ Subgroup.center (Cover m B) := by
  obtain ⟨hl, hr⟩ := (toMatrix_eq_one_iff x).mp hx
  have hz := GLAct.kernel_central ε hunit hm hr
  rw [Subgroup.mem_center_iff]
  intro y
  apply SemidirectProduct.ext
  · simp only [SemidirectProduct.mul_left, hl, map_one, MulAut.one_apply, mul_one,
      stRowAct, MonoidHom.comp_apply, hr, one_mul]
  · exact Subgroup.mem_center_iff.mp hz y.right

include hunit in
/-- Every elementary matrix fixing the last column is covered; K1 stability supplies the
smaller elementary block. -/
theorem exists_of_fixes_last (hm : 5 ≤ m)
    (A : (Matrix (Fin (m + 1)) (Fin (m + 1)) B)ˣ) (hA : A ∈ K1.E (m + 1) B)
    (hfix : (A : Matrix (Fin (m + 1)) (Fin (m + 1)) B) *ᵥ Pi.single (Fin.last m) 1 =
      Pi.single (Fin.last m) 1) : ∃ x : Cover m B, toMatrix x = A := by
  obtain ⟨y, hy⟩ := GLPres.exists_ι A hfix
  have hrow : rowMatHom y.left ∈ K1.E (m + 1) B := by
    exact ⟨rowLift y.left, representation_rowLift y.left⟩
  have hpad : Kernel.padUnitsHom y.right ∈ K1.E (m + 1) B := by
    have hprod : rowMatHom y.left * Kernel.padUnitsHom y.right = A := by
      change rowMat (Multiplicative.toAdd y.left) * Kernel.padUnitsHom y.right = A
      rw [← GLPres.ι_inl, ← GLPres.ι_inr, ← map_mul, SemidirectProduct.inl_left_mul_inr_right, hy]
    have h := Subgroup.mul_mem (K1.E (m + 1) B) (Subgroup.inv_mem _ hrow) hA
    rwa [← hprod, inv_mul_cancel_left] at h
  obtain ⟨z, hz⟩ := K1.mem_E_of_pad ε hunit hm hpad
  refine ⟨⟨y.left, z⟩, ?_⟩
  change GLPres.ι (toRowGL _) = A
  rw [show toRowGL (⟨y.left, z⟩ : Cover m B) = y from SemidirectProduct.ext rfl hz, hy]

include hunit in
theorem toLastColumn_surjective (hm : 5 ≤ m) :
    Function.Surjective (toLastColumn (m := m) (B := B)) := by
  intro A
  obtain ⟨x, hx⟩ := exists_of_fixes_last ε hunit hm A.val.val A.val.property A.property
  exact ⟨x, Subtype.ext (Subtype.ext hx)⟩

/-- The one-column frame stabilizer as an exact group extension by the smaller matrix kernel. -/
def lastColumnExtension (hm : 5 ≤ m) :
    GroupExtension (Elementary.representation (n := m) (R := B)).ker
      (Cover m B) (LastColumnStabilizer m B) where
  inl := kernelInclusion
  rightHom := toLastColumn
  inl_injective := kernelInclusion_injective
  range_inl_eq_ker_rightHom := range_kernelInclusion
  rightHom_surjective := toLastColumn_surjective ε hunit hm

include hunit in
theorem lastColumn_isPerfect (hm : 5 ≤ m) : Group.IsPerfect (LastColumnStabilizer m B) := by
  have := isPerfect (B := B) (show 3 ≤ m by omega)
  exact Group.IsPerfect.ofSurjective (toLastColumn_surjective ε hunit hm)

end Local
end FrameStabilizer
end AllPrimeGroups
