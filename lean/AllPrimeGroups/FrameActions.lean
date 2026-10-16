import AllPrimeGroups.FrameExactness
import AllPrimeGroups.GLTransport
import AllPrimeGroups.K1Stability
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! The elementary action on the ordered frame complex of reduced columns.

The reduction of an invertible matrix acts by an injective linear map over the residue field.
Thus every ordered frame stays a frame. The resulting action commutes with each face and with
the augmented chain boundary, and preserves chain degree. No transitivity is assumed here. -/

namespace AllPrimeGroups
namespace Frames
noncomputable section

section General
variable {K W ι : Type*} [Field K] [AddCommGroup W] [Module K W] {f : ι → W}

theorem IsFrame.map_of_linear {L : List ι} (h : IsFrame K f L)
    (g : ι → ι) (hg : Function.Injective g) (T : W →ₗ[K] W)
    (hT : Function.Injective T) (hfg : ∀ x, f (g x) = T (f x)) : IsFrame K f (L.map g) := by
  have hi : LinearIndepOn K (f ∘ g) {x | x ∈ L} := by
    have hmap := h.2.map_injOn T hT.injOn
    have he : f ∘ g = T ∘ f := funext hfg
    rw [he]
    exact hmap
  exact (show IsFrame K (f ∘ g) L from ⟨h.1, hi⟩).map hg

end General

section Columns
variable {B K : Type*} [Ring B] [Field K] (ε : B →+* K) {n : ℕ}
open GLPres Matrix

abbrev ColumnFrame (n : ℕ) := Frame K (red ε : Col n B → Fin n → K)

def reducedLinear (g : (Matrix (Fin n) (Fin n) B)ˣ) :
    (Fin n → K) →ₗ[K] (Fin n → K) := (g.val.map ε).mulVecLin

theorem reducedLinear_injective (g : (Matrix (Fin n) (Fin n) B)ˣ) :
    Function.Injective (reducedLinear ε g) := by
  intro x y h
  have hi := congrArg ((g.inv.map ε) *ᵥ ·) h
  change (g.inv.map ε) *ᵥ ((g.val.map ε) *ᵥ x) =
    (g.inv.map ε) *ᵥ ((g.val.map ε) *ᵥ y) at hi
  simpa only [Matrix.mulVec_mulVec, ← Matrix.map_mul, g.inv_val,
    Matrix.map_one _ ε.map_zero ε.map_one, Matrix.one_mulVec] using hi

def columnFrameAct (g : (Matrix (Fin n) (Fin n) B)ˣ) (F : ColumnFrame ε n) : ColumnFrame ε n :=
  ⟨F.val.map (g • ·), F.property.map_of_linear (g • ·) (MulAction.injective g)
    (reducedLinear ε g) (reducedLinear_injective ε g) (red_smul ε g)⟩

instance columnFrameMulAction : MulAction (Matrix (Fin n) (Fin n) B)ˣ (ColumnFrame ε n) where
  smul := columnFrameAct ε
  one_smul F := by
    apply Subtype.ext
    change F.val.map ((1 : (Matrix (Fin n) (Fin n) B)ˣ) • ·) = F.val
    simp
  mul_smul g h F := by
    apply Subtype.ext
    change F.val.map ((g * h) • ·) = (F.val.map (h • ·)).map (g • ·)
    simp only [List.map_map, Function.comp_def, mul_smul]

instance elementaryFrameMulAction : MulAction (K1.E n B) (ColumnFrame ε n) :=
  MulAction.compHom _ (K1.E n B).subtype

theorem columnFrame_smul_val (g : (Matrix (Fin n) (Fin n) B)ˣ) (F : ColumnFrame ε n) :
    (g • F).val = F.val.map (g • ·) := rfl

theorem elementaryFrame_smul_val (g : K1.E n B) (F : ColumnFrame ε n) :
    (g • F).val = F.val.map (g.val • ·) := rfl

theorem face_columnFrame_smul (g : (Matrix (Fin n) (Fin n) B)ˣ)
    (F : ColumnFrame ε n) (i : ℕ) : face (g • F) i = g • face F i :=
  Subtype.ext (List.eraseIdx_map (g • ·) F.val i)

theorem face_elementaryFrame_smul (g : K1.E n B) (F : ColumnFrame ε n) (i : ℕ) :
    face (g • F) i = g • face F i := face_columnFrame_smul ε g.val F i

def columnChainAct (g : (Matrix (Fin n) (Fin n) B)ˣ) :
    (ColumnFrame ε n →₀ ℤ) →+ (ColumnFrame ε n →₀ ℤ) :=
  Finsupp.mapDomain.addMonoidHom (g • ·)

theorem columnChainAct_single (g : (Matrix (Fin n) (Fin n) B)ˣ)
    (F : ColumnFrame ε n) (a : ℤ) :
    columnChainAct ε g (Finsupp.single F a) = Finsupp.single (g • F) a :=
  Finsupp.mapDomain_single

theorem columnChainAct_one (z : ColumnFrame ε n →₀ ℤ) :
    columnChainAct ε (1 : (Matrix (Fin n) (Fin n) B)ˣ) z = z := by
  induction z using Finsupp.induction_linear with
  | zero => exact map_zero _
  | add x y hx hy => rw [map_add, hx, hy]
  | single F a => rw [columnChainAct_single, one_smul]

theorem columnChainAct_mul (g h : (Matrix (Fin n) (Fin n) B)ˣ)
    (z : ColumnFrame ε n →₀ ℤ) :
    columnChainAct ε (g * h) z = columnChainAct ε g (columnChainAct ε h z) := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single F a => simp only [columnChainAct_single, mul_smul]

theorem bd_columnChainAct (g : (Matrix (Fin n) (Fin n) B)ˣ) (z : ColumnFrame ε n →₀ ℤ) :
    bd (columnChainAct ε g z) = columnChainAct ε g (bd z) := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single F a =>
    have hl : (g • F).val.length = F.val.length := List.length_map _
    rw [columnChainAct_single, bd_single, bd_single, map_zsmul, faces, faces, hl, map_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [map_zsmul, columnChainAct_single, face_columnFrame_smul]

theorem deg_columnChainAct (g : (Matrix (Fin n) (Fin n) B)ˣ)
    {k : ℕ} {z : ColumnFrame ε n →₀ ℤ} (hz : Deg k z) : Deg k (columnChainAct ε g z) := by
  classical
  intro F hF
  obtain ⟨G, hG, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hF)
  exact (List.length_map _).trans (hz G hG)

end Columns
end
end Frames
end AllPrimeGroups
