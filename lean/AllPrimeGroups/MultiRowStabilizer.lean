import AllPrimeGroups.RowStabilizer

/-! Rectangular row models for frame stabilizers (manuscript Section 12).

The number of fixed columns is an arbitrary finite index type. The central extension and
perfectness are proved uniformly, before identifying these block models with the stabilizers
in the ambient elementary group. No injectivity of a rank-changing Steinberg map is used. -/

universe u v

namespace AllPrimeGroups
namespace FrameStabilizer

open Matrix GLPres

variable {B : Type u} [Ring B] {m : ℕ} {ι : Type v}

def rowsAct : (Matrix (Fin m) (Fin m) B)ˣ →* MulAut (ι → Row m B) where
  toFun A := MulEquiv.piCongrRight fun _ => rowAct A
  map_one' := by
    apply MulEquiv.ext
    intro r
    funext i
    exact DFunLike.congr_fun (map_one rowAct) (r i)
  map_mul' A A' := by
    apply MulEquiv.ext
    intro r
    funext i
    exact DFunLike.congr_fun (map_mul rowAct A A') (r i)

def stRowsAct : Steinberg m B →* MulAut (ι → Row m B) := rowsAct.comp Elementary.representation

abbrev BlockCover (ι : Type*) (m : ℕ) (B : Type*) [Ring B] :=
  (ι → Row m B) ⋊[stRowsAct] Steinberg m B

abbrev BlockStabilizer (ι : Type*) (m : ℕ) (B : Type*) [Ring B] :=
  (ι → Row m B) ⋊[rowsAct.comp (K1.E m B).subtype] K1.E m B

/-- The block model's central extension, before embedding the model in the ambient group. -/
def blockProjection : BlockCover ι m B →* BlockStabilizer ι m B :=
  SemidirectProduct.map (MonoidHom.id _) Elementary.representation.rangeRestrict (fun _ => rfl)

theorem blockProjection_surjective : Function.Surjective (blockProjection (ι := ι) (m := m) (B := B)) := by
  intro x
  obtain ⟨z, hz⟩ := x.right.property
  refine ⟨⟨x.left, z⟩, ?_⟩
  apply SemidirectProduct.ext
  · rfl
  · exact Subtype.ext hz

theorem blockProjection_eq_one_iff (x : BlockCover ι m B) :
    blockProjection x = 1 ↔ x.left = 1 ∧ Elementary.representation x.right = 1 := by
  constructor
  · intro h
    refine ⟨congrArg SemidirectProduct.left h, ?_⟩
    exact congrArg (fun y : BlockStabilizer ι m B => (y.right :
      (Matrix (Fin m) (Fin m) B)ˣ)) h
  · rintro ⟨hl, hr⟩
    apply SemidirectProduct.ext hl
    exact Subtype.ext hr

def blockKernelInclusion : (Elementary.representation (n := m) (R := B)).ker →* BlockCover ι m B :=
  SemidirectProduct.inr.comp (Elementary.representation (n := m) (R := B)).ker.subtype

theorem blockKernelInclusion_injective :
    Function.Injective (blockKernelInclusion (ι := ι) (m := m) (B := B)) :=
  SemidirectProduct.inr_injective.comp Subtype.val_injective

theorem range_blockKernelInclusion :
    (blockKernelInclusion (ι := ι) (m := m) (B := B)).range = blockProjection.ker := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    exact (blockProjection_eq_one_iff _).mpr ⟨rfl, z.property⟩
  · intro hx
    obtain ⟨hl, hr⟩ := (blockProjection_eq_one_iff x).mp hx
    refine ⟨⟨x.right, hr⟩, ?_⟩
    apply SemidirectProduct.ext
    · exact hl.symm
    · rfl

def blockExtension : GroupExtension (Elementary.representation (n := m) (R := B)).ker
    (BlockCover ι m B) (BlockStabilizer ι m B) where
  inl := blockKernelInclusion
  rightHom := blockProjection
  inl_injective := blockKernelInclusion_injective
  range_inl_eq_ker_rightHom := range_blockKernelInclusion
  rightHom_surjective := blockProjection_surjective

def rowInclusion [DecidableEq ι] (i : ι) : Cover m B →* BlockCover ι m B :=
  SemidirectProduct.map (MonoidHom.mulSingle (fun _ : ι => Row m B) i) (MonoidHom.id _) (fun z => by
    apply MonoidHom.ext
    intro r
    funext j
    change (Pi.mulSingle i (stRowAct z r) : ι → Row m B) j =
      stRowAct z ((Pi.mulSingle i r : ι → Row m B) j)
    by_cases h : j = i
    · subst h
      simp
    · simp [h])

theorem rowInclusion_inl [DecidableEq ι] (i : ι) (r : Row m B) :
    rowInclusion i (SemidirectProduct.inl r : Cover m B) =
      (SemidirectProduct.inl (Pi.mulSingle i r) : BlockCover ι m B) :=
  SemidirectProduct.map_inl _ _ _ _

theorem rowInclusion_inr [DecidableEq ι] (i : ι) (z : Steinberg m B) :
    rowInclusion i (SemidirectProduct.inr z : Cover m B) =
      (SemidirectProduct.inr z : BlockCover ι m B) :=
  SemidirectProduct.map_inr _ _ _ _

/-- Every rectangular block cover is perfect in rank at least three. -/
theorem blockCover_isPerfect [Fintype ι] (hm : 3 ≤ m) : Group.IsPerfect (BlockCover ι m B) := by
  classical
  have hmap {G : Type u} [Group G] (f : G →* BlockCover ι m B) (hG : Group.IsPerfect G) :
      f.range ≤ commutator (BlockCover ι m B) := by
    have h : (commutator G).map f ≤ commutator (BlockCover ι m B) := by
      rw [commutator_def, Subgroup.map_commutator, commutator_def]
      exact Subgroup.commutator_mono le_top le_top
    rwa [hG.commutator_eq_top, Subgroup.map_top] at h
  have hsingle (i : ι) (r : Row m B) :
      (SemidirectProduct.inl (Pi.mulSingle i r) : BlockCover ι m B) ∈
        commutator (BlockCover ι m B) := by
    exact hmap (rowInclusion (m := m) (B := B) i) (FrameStabilizer.isPerfect hm)
      ⟨SemidirectProduct.inl r, rowInclusion_inl i r⟩
  have hq : (QuotientGroup.mk' (commutator (BlockCover ι m B))).comp
      (SemidirectProduct.inl : (ι → Row m B) →* BlockCover ι m B) = 1 := by
    apply MonoidHom.pi_ext
    intro i r
    change (QuotientGroup.mk' (commutator (BlockCover ι m B)))
      (SemidirectProduct.inl (Pi.mulSingle i r)) = 1
    rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
    exact hsingle i r
  constructor
  apply top_unique
  intro x _
  rw [← SemidirectProduct.inl_left_mul_inr_right x]
  apply Subgroup.mul_mem
  · have hx := DFunLike.congr_fun hq x.left
    rw [MonoidHom.comp_apply, MonoidHom.one_apply, ← MonoidHom.mem_ker,
      QuotientGroup.ker_mk'] at hx
    exact hx
  · exact hmap (SemidirectProduct.inr : Steinberg m B →* BlockCover ι m B)
      (Steinberg.isPerfect hm) ⟨x.right, rfl⟩

theorem blockStabilizer_isPerfect [Fintype ι] (hm : 3 ≤ m) : Group.IsPerfect (BlockStabilizer ι m B) := by
  have := blockCover_isPerfect (ι := ι) (B := B) hm
  exact Group.IsPerfect.ofSurjective blockProjection_surjective

section Local
variable {K : Type*} [Field K] (ε : B →+* K) (hunit : ∀ b : B, ε b ≠ 0 → IsUnit b)

include hunit in
theorem blockKernel_central (hm : 6 ≤ m) {x : BlockCover ι m B} (hx : blockProjection x = 1) :
    x ∈ Subgroup.center (BlockCover ι m B) := by
  obtain ⟨hl, hr⟩ := (blockProjection_eq_one_iff x).mp hx
  have hz := GLAct.kernel_central ε hunit hm hr
  rw [Subgroup.mem_center_iff]
  intro y
  apply SemidirectProduct.ext
  · simp only [SemidirectProduct.mul_left, hl, map_one, MulAut.one_apply, mul_one,
      stRowsAct, MonoidHom.comp_apply, hr, one_mul]
  · exact Subgroup.mem_center_iff.mp hz y.right

end Local
end FrameStabilizer
end AllPrimeGroups
