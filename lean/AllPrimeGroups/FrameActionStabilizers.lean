import AllPrimeGroups.FrameActions
import AllPrimeGroups.SignedFacePair

/-! Standard ordered frames and their actual stabilizers under the elementary action.

This connects the rectangular matrix stabilizers to `MulAction.stabilizer` of the frame
complex. The two normalized faces become inclusion and elementary conjugation in the same
ambient group. -/

namespace AllPrimeGroups
namespace Frames
noncomputable section
open Matrix GLPres FrameBlocks FrameFaces

variable {B K : Type*} [Ring B] [Field K] (ε : B →+* K) {m l : ℕ}

def standardIndex (j : Fin l) : Fin (m + l) := finSumFinEquiv (.inr j)

theorem standardIndex_injective : Function.Injective (standardIndex (m := m) (l := l)) :=
  finSumFinEquiv.injective.comp Sum.inr_injective

def standardColumn (j : Fin l) : Col (m + l) B := Pi.single (standardIndex j) 1

theorem standardColumn_red (j : Fin l) :
    red ε (standardColumn (B := B) (m := m) j) = Pi.single (standardIndex j) 1 := red_single ε _

theorem standardColumn_independent :
    LinearIndependent K (fun j : Fin l => red ε (standardColumn (B := B) (m := m) j)) := by
  simp only [standardColumn_red]
  simpa only [Function.comp_def, Pi.basisFun_apply] using
    (Pi.basisFun K (Fin (m + l))).linearIndependent.comp standardIndex standardIndex_injective

include ε in
theorem standardColumn_injective : Function.Injective (standardColumn (B := B) (m := m) (l := l)) := by
  intro i j h
  exact (standardColumn_independent ε).injective (congrArg (red ε) h)

def standardFrame (m l : ℕ) : ColumnFrame ε (m + l) :=
  ⟨List.ofFn (standardColumn (B := B) (m := m) (l := l)), by
    refine ⟨List.nodup_ofFn_ofInjective (standardColumn_injective ε), ?_⟩
    have hs : {x : Col (m + l) B | x ∈ List.ofFn (standardColumn (m := m) (l := l))} =
        Set.range (standardColumn (m := m) (l := l)) := by ext x; simp
    rw [hs]
    exact (linearIndepOn_range_iff (standardColumn_injective ε) (red ε)).mpr
      (standardColumn_independent ε)⟩

theorem pairNormalizer_basis :
    (pairNormalizer m B).val.val *ᵥ Pi.single (pairFreeIndex m) 1 =
      Pi.single (pairFixedIndex m) 1 := by
  change (ev (K1.sgnWord (pairFixedIndex m) (pairFreeIndex m) pairIndices_ne.symm)).val *ᵥ _ = _
  rw [K1.sgnWord_mulVec]
  funext i
  by_cases ha : i = pairFreeIndex m
  · subst ha
    simp [pairIndices_ne]
  · by_cases hb : i = pairFixedIndex m
    · subst hb
      simp
    · simp [ha, hb]

theorem firstFace_standardFrame :
    face (standardFrame ε m 2) 0 = standardFrame ε (m + 1) 1 := by
  have hi : standardIndex (m := m) (1 : Fin 2) = standardIndex (m := m + 1) (0 : Fin 1) := by
    apply Fin.ext
    simp [standardIndex, finSumFinEquiv]
  apply Subtype.ext
  change [standardColumn (B := B) (m := m) (1 : Fin 2)] =
    [standardColumn (B := B) (m := m + 1) (0 : Fin 1)]
  simp only [standardColumn, hi]

/-- The elementary normalizer sends the other face to the same standard vertex. -/
theorem signedSecondFace_standardFrame :
    pairNormalizer m B • face (standardFrame ε m 2) 1 = standardFrame ε (m + 1) 1 := by
  have ha : standardIndex (m := m) (0 : Fin 2) = pairFreeIndex m := by
    apply Fin.ext
    simp [standardIndex, pairFreeIndex, finSumFinEquiv]
  apply Subtype.ext
  change [(pairNormalizer m B).val • standardColumn (B := B) (m := m) (0 : Fin 2)] =
    [standardColumn (B := B) (m := m + 1) (0 : Fin 1)]
  apply congrArg List.singleton
  change (pairNormalizer m B).val.val *ᵥ Pi.single (standardIndex (m := m) (0 : Fin 2)) 1 =
    Pi.single (pairFixedIndex m) 1
  rw [ha]
  exact pairNormalizer_basis

def standardFrameStabilizer (m l : ℕ) : Subgroup (K1.E (m + l) B) :=
  MulAction.stabilizer (K1.E (m + l) B) (standardFrame ε m l)

theorem mem_standardFrameStabilizer_iff (U : K1.E (m + l) B) :
    U ∈ standardFrameStabilizer ε m l ↔
      ∀ j : Fin l, U.val • standardColumn (B := B) (m := m) j = standardColumn j := by
  rw [standardFrameStabilizer, MulAction.mem_stabilizer_iff]
  constructor
  · intro h j
    have hL := congrArg Subtype.val h
    change (List.ofFn (standardColumn (B := B) (m := m) (l := l))).map (U.val • ·) =
      List.ofFn (standardColumn (B := B) (m := m) (l := l)) at hL
    rw [List.map_ofFn, List.ofFn_inj] at hL
    exact congrFun hL j
  · intro h
    apply Subtype.ext
    change (List.ofFn (standardColumn (B := B) (m := m) (l := l))).map (U.val • ·) =
      List.ofFn (standardColumn (B := B) (m := m) (l := l))
    rw [List.map_ofFn, List.ofFn_inj]
    exact funext h

def unlabel : (Matrix (Fin (m + l)) (Fin (m + l)) B)ˣ →*
    (Matrix (Fin m ⊕ Fin l) (Fin m ⊕ Fin l) B)ˣ := MatrixGeometry.relabel finSumFinEquiv.symm

theorem unlabel_sumRelabel (U : (Matrix (Fin m ⊕ Fin l) (Fin m ⊕ Fin l) B)ˣ) :
    unlabel (sumRelabel U) = U := by
  apply Units.ext
  ext i j
  change U.val (finSumFinEquiv.symm (finSumFinEquiv i))
    (finSumFinEquiv.symm (finSumFinEquiv j)) = U.val i j
  simp only [Equiv.symm_apply_apply]

theorem sumRelabel_unlabel (U : (Matrix (Fin (m + l)) (Fin (m + l)) B)ˣ) :
    sumRelabel (unlabel (m := m) (l := l) U) = U := by
  apply Units.ext
  ext i j
  change U.val (finSumFinEquiv (finSumFinEquiv.symm i))
    (finSumFinEquiv (finSumFinEquiv.symm j)) = U.val i j
  simp only [Equiv.apply_symm_apply]

theorem mem_standardFrameStabilizer_iff_unlabel (U : K1.E (m + l) B) :
    U ∈ standardFrameStabilizer ε m l ↔ unlabel (m := m) (l := l) U.val ∈ MatrixGeometry.rightFixer := by
  rw [mem_standardFrameStabilizer_iff, MatrixGeometry.mem_rightFixer_iff]
  constructor
  · intro h i j
    have hc := congrFun (h j) (finSumFinEquiv i)
    change (U.val.val *ᵥ Pi.single (standardIndex j) 1) (finSumFinEquiv i) =
      (Pi.single (standardIndex j) (1 : B) : Fin (m + l) → B) (finSumFinEquiv i) at hc
    simp only [Matrix.mulVec_single_one, Matrix.col_apply, Pi.single_apply] at hc
    change U.val.val (finSumFinEquiv i) (finSumFinEquiv (.inr j)) = _
    simpa only [standardIndex, Matrix.one_apply, finSumFinEquiv.injective.eq_iff, eq_comm] using hc
  · intro h j
    funext i
    obtain ⟨i, rfl⟩ := (finSumFinEquiv : Fin m ⊕ Fin l ≃ Fin (m + l)).surjective i
    have hc := h i j
    change U.val.val (finSumFinEquiv i) (finSumFinEquiv (.inr j)) = _ at hc
    change (U.val.val *ᵥ Pi.single (standardIndex j) 1) (finSumFinEquiv i) =
      (Pi.single (standardIndex j) (1 : B) : Fin (m + l) → B) (finSumFinEquiv i)
    simp only [Matrix.mulVec_single_one, Matrix.col_apply, Pi.single_apply]
    simpa only [standardIndex, Matrix.one_apply, finSumFinEquiv.injective.eq_iff, eq_comm] using hc

def toFrameStabilizer : Stabilizer m l B →* standardFrameStabilizer ε m l :=
  stabilizerToElementary.codRestrict _ (fun U => by
    apply (mem_standardFrameStabilizer_iff_unlabel ε _).mpr
    change unlabel (sumRelabel U.val) ∈ MatrixGeometry.rightFixer
    rw [unlabel_sumRelabel]
    exact U.property.1)

theorem toFrameStabilizer_injective :
    Function.Injective (toFrameStabilizer ε (m := m) (l := l)) := by
  intro U V h
  have hM := congrArg (fun x : standardFrameStabilizer ε m l => x.val.val) h
  have hU := congrArg (unlabel (m := m) (l := l)) hM
  change unlabel (sumRelabel U.val) = unlabel (sumRelabel V.val) at hU
  exact Subtype.ext (by simpa only [unlabel_sumRelabel] using hU)

theorem toFrameStabilizer_surjective :
    Function.Surjective (toFrameStabilizer ε (m := m) (l := l)) := by
  intro U
  let V : Stabilizer m l B := ⟨unlabel U.val.val,
    (mem_standardFrameStabilizer_iff_unlabel ε U.val).mp U.property,
    by change sumRelabel (unlabel U.val.val) ∈ K1.E (m + l) B
       rw [sumRelabel_unlabel]
       exact U.val.property⟩
  refine ⟨V, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  exact sumRelabel_unlabel U.val.val

def frameStabilizerEquiv : Stabilizer m l B ≃* standardFrameStabilizer ε m l :=
  MulEquiv.ofBijective (toFrameStabilizer ε)
    ⟨toFrameStabilizer_injective ε, toFrameStabilizer_surjective ε⟩

section Local
variable (hunit : ∀ b : B, ε b ≠ 0 → IsUnit b)

def blockFrameStabilizerEquiv (hm : 5 ≤ m) :
    FrameStabilizer.BlockStabilizer (Fin l) m B ≃* standardFrameStabilizer ε m l :=
  (stabilizerEquiv ε hunit hm).trans (frameStabilizerEquiv ε)

def standardFrameExtension (hm : 5 ≤ m) :
    GroupExtension (Elementary.representation (n := m) (R := B)).ker
      (FrameStabilizer.BlockCover (Fin l) m B) (standardFrameStabilizer ε m l) :=
  (stabilizerExtension ε hunit hm).relabelQuotient (frameStabilizerEquiv ε)

include hunit in
theorem standardFrameStabilizer_isPerfect (hm : 5 ≤ m) :
    Group.IsPerfect (standardFrameStabilizer ε m l) := by
  have := stabilizer_isPerfect ε hunit (l := l) hm
  exact Group.IsPerfect.ofSurjective (frameStabilizerEquiv ε).surjective

def firstActionFace (hm : 5 ≤ m) :
    standardFrameStabilizer ε m 2 →* standardFrameStabilizer ε (m + 1) 1 :=
  (frameStabilizerEquiv ε).toMonoidHom.comp
    ((actualFace ε hunit hm (0 : Fin 2)).comp (frameStabilizerEquiv ε).symm.toMonoidHom)

def signedActionFace (hm : 5 ≤ m) :
    standardFrameStabilizer ε m 2 →* standardFrameStabilizer ε (m + 1) 1 :=
  (frameStabilizerEquiv ε).toMonoidHom.comp
    ((actualSignedPair ε hunit hm).comp (frameStabilizerEquiv ε).symm.toMonoidHom)

theorem firstActionFace_inclusion (hm : 5 ≤ m) (U : standardFrameStabilizer ε m 2) :
    (firstActionFace ε hunit hm U).val = U.val := by
  change stabilizerToElementary
    (actualFace ε hunit hm (0 : Fin 2) ((frameStabilizerEquiv ε).symm U)) = U.val
  rw [actualFirstFace_inclusion]
  exact congrArg Subtype.val ((frameStabilizerEquiv ε).apply_symm_apply U)

theorem signedActionFace_conjugation (hm : 5 ≤ m) (U : standardFrameStabilizer ε m 2) :
    (signedActionFace ε hunit hm U).val = pairNormalizer m B * U.val * (pairNormalizer m B)⁻¹ := by
  change stabilizerToElementary
    (actualSignedPair ε hunit hm ((frameStabilizerEquiv ε).symm U)) = _
  rw [actualSignedPair_conjugation]
  have h : stabilizerToElementary ((frameStabilizerEquiv ε).symm U) = U.val :=
    congrArg Subtype.val ((frameStabilizerEquiv ε).apply_symm_apply U)
  rw [h]

end Local
end
end Frames
end AllPrimeGroups
