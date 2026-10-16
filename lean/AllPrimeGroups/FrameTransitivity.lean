import AllPrimeGroups.SplitFrameCompletion
import AllPrimeGroups.FrameActionStabilizers
import Mathlib.Algebra.Group.Action.Pretransitive

/-! Transitivity on all ordered frames with at least one unused ambient coordinate.

The split matrix-nil hypotheses allow simultaneous completion. This proves the full
equal-length transitivity statement, rather than only the few lengths used in the theorem. -/

namespace AllPrimeGroups
namespace Frames
noncomputable section
open Matrix GLPres

section Lists
variable {K W ι : Type*} [Field K] [AddCommGroup W] [Module K W] {f : ι → W}

theorem IsFrame.linearIndependent_get {L : List ι} (h : IsFrame K f L) :
    LinearIndependent K (fun i : Fin L.length => f (L.get i)) := by
  let t : Fin L.length → {x | x ∈ L} := fun i => ⟨L.get i, List.get_mem ..⟩
  have ht : Function.Injective t := fun i j he => h.1.injective_get (congrArg Subtype.val he)
  exact h.2.linearIndependent.comp t ht

end Lists

variable {B K : Type*} [Ring B] [Field K] (ε : B →+* K) {n m l : ℕ}

def frameTuple (F : ColumnFrame ε n) (hF : F.val.length = l) : Fin l → Col n B :=
  fun j => F.val.get (Fin.cast hF.symm j)

theorem frameTuple_independent (F : ColumnFrame ε n) (hF : F.val.length = l) :
    LinearIndependent K (fun j => red ε (frameTuple ε F hF j)) :=
  F.property.linearIndependent_get.comp (Fin.cast hF.symm) (Fin.cast_injective _)

theorem frameTuple_ofFn (F : ColumnFrame ε n) (hF : F.val.length = l) :
    List.ofFn (frameTuple ε F hF) = F.val :=
  (List.ofFn_congr hF F.val.get).symm.trans (List.ofFn_get F.val)

/-- The E-set of ordered frames with a fixed number of columns. -/
def LengthFrame (n l : ℕ) := {F : ColumnFrame ε n // F.val.length = l}

instance lengthFrameMulAction : MulAction (K1.E n B) (LengthFrame ε n l) where
  smul g F := ⟨g • F.val, by rw [elementaryFrame_smul_val, List.length_map]; exact F.property⟩
  one_smul F := Subtype.ext (one_smul _ _)
  mul_smul g h F := Subtype.ext (mul_smul g h F.val)

def standardLengthFrame (m l : ℕ) : LengthFrame ε (m + l) l :=
  ⟨standardFrame ε m l, List.length_ofFn⟩

theorem stabilizer_standardLengthFrame :
    MulAction.stabilizer (K1.E (m + l) B) (standardLengthFrame ε m l) =
      standardFrameStabilizer ε m l := by
  ext g
  rw [MulAction.mem_stabilizer_iff, standardFrameStabilizer, MulAction.mem_stabilizer_iff]
  exact Subtype.ext_iff

section Split
variable (σ : K →+* B) (hs : ε.comp σ = RingHom.id K)
variable (hnil : ∀ A : Matrix (Fin (m + l)) (Fin (m + l)) B, ε.mapMatrix A = 0 → IsNilpotent A)
variable (hunit : ∀ b : B, ε b ≠ 0 → IsUnit b)

include σ hs hnil hunit in
theorem exists_split_elementary_from_standard (hm : 0 < m)
    (F : ColumnFrame ε (m + l)) (hF : F.val.length = l) :
    ∃ A : K1.E (m + l) B, A • standardFrame ε m l = F := by
  let i₀ : Fin (m + l) := finSumFinEquiv (.inl (⟨0, hm⟩ : Fin m))
  have hi₀ (j : Fin l) : standardIndex (m := m) j ≠ i₀ :=
    finSumFinEquiv.injective.ne Sum.inr_ne_inl
  obtain ⟨A, hA⟩ := exists_split_elementary_columns ε σ hs hnil hunit
    standardIndex standardIndex_injective i₀ hi₀ (frameTuple ε F hF) (frameTuple_independent ε F hF)
  refine ⟨A, ?_⟩
  apply Subtype.ext
  change (List.ofFn (standardColumn (B := B) (m := m) (l := l))).map (A.val • ·) = F.val
  rw [List.map_ofFn, ← frameTuple_ofFn ε F hF]
  apply congrArg List.ofFn
  funext j
  exact hA j

include σ hs hnil hunit in
theorem exists_split_elementary_between (hm : 0 < m) (F G : ColumnFrame ε (m + l))
    (hF : F.val.length = l) (hG : G.val.length = l) :
    ∃ A : K1.E (m + l) B, A • F = G := by
  obtain ⟨A, hA⟩ := exists_split_elementary_from_standard ε σ hs hnil hunit hm F hF
  obtain ⟨D, hD⟩ := exists_split_elementary_from_standard ε σ hs hnil hunit hm G hG
  refine ⟨D * A⁻¹, ?_⟩
  rw [← hA, mul_smul, inv_smul_smul, hD]

include σ hs hnil hunit in
theorem lengthFrame_isPretransitive (hm : 0 < m) :
    MulAction.IsPretransitive (K1.E (m + l) B) (LengthFrame ε (m + l) l) := by
  apply MulAction.IsPretransitive.of_orbit (x₀ := standardLengthFrame ε m l)
  intro F
  obtain ⟨A, hA⟩ := exists_split_elementary_from_standard ε σ hs hnil hunit hm F.val F.property
  exact ⟨A, Subtype.ext hA⟩

end Split
end
end Frames
end AllPrimeGroups
