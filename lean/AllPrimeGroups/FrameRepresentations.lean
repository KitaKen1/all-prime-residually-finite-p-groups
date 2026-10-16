import AllPrimeGroups.FrameActions
import AllPrimeGroups.FrameTheorem
import Mathlib.RepresentationTheory.Basic

/-! The augmented ordered frame complex as integer representations of the elementary group.

Chains are restricted to one frame length. The boundary is linear and equivariant, consecutive
boundaries compose to zero, and the existing ordered-frame exactness theorem applies using the
standard reduced columns. These are the chain objects needed for the low-degree cohomology
argument; no orbit transitivity or character extension is asserted. -/

namespace AllPrimeGroups
namespace Frames
noncomputable section
open Matrix GLPres

variable {B K : Type*} [Ring B] [Field K] (ε : B →+* K) {n : ℕ}

def frameChains (n k : ℕ) : Submodule ℤ (ColumnFrame ε n →₀ ℤ) where
  carrier := Deg k
  zero_mem' := Deg.zero k
  add_mem' := Deg.add
  smul_mem' a _ hz := hz.zsmul a

def frameRepresentation (n k : ℕ) : Representation ℤ (K1.E n B) (frameChains ε n k) where
  toFun g :=
    { toFun z := ⟨columnChainAct ε g.val z.val, deg_columnChainAct ε g.val z.property⟩
      map_add' x y := Subtype.ext (map_add _ x.val y.val)
      map_smul' a z := Subtype.ext (map_zsmul _ a z.val) }
  map_one' := by
    apply LinearMap.ext
    intro z
    exact Subtype.ext (columnChainAct_one ε z.val)
  map_mul' g h := by
    apply LinearMap.ext
    intro z
    exact Subtype.ext (columnChainAct_mul ε g.val h.val z.val)

theorem frameRepresentation_single (g : K1.E n B) (F : ColumnFrame ε n) (a : ℤ)
    {k : ℕ} (hF : F.val.length = k) :
    (frameRepresentation ε n k g ⟨Finsupp.single F a, hF ▸ Deg.single F a⟩).val =
      Finsupp.single (g • F) a := columnChainAct_single ε g.val F a

def frameBoundary (n k : ℕ) : frameChains ε n (k + 1) →ₗ[ℤ] frameChains ε n k where
  toFun z := ⟨bd z.val, z.property.bd⟩
  map_add' x y := Subtype.ext (map_add _ x.val y.val)
  map_smul' a z := Subtype.ext (map_zsmul _ a z.val)

theorem frameBoundary_equivariant (k : ℕ) (g : K1.E n B) (z : frameChains ε n (k + 1)) :
    frameBoundary ε n k (frameRepresentation ε n (k + 1) g z) =
      frameRepresentation ε n k g (frameBoundary ε n k z) :=
  Subtype.ext (bd_columnChainAct ε g.val z.val)

theorem frameBoundary_comp (k : ℕ) :
    (frameBoundary ε n k).comp (frameBoundary ε n (k + 1)) = 0 := by
  apply LinearMap.ext
  intro z
  exact Subtype.ext (bd_bd z.val)

theorem reducedBasis_independent :
    LinearIndependent K (fun i : Fin n => red ε (Pi.single i (1 : B) : Col n B)) := by
  have h : (fun i : Fin n => red ε (Pi.single i (1 : B) : Col n B)) =
      (Pi.basisFun K (Fin n)) := by
    funext i
    rw [red_single, Pi.basisFun_apply]
  rw [h]
  exact (Pi.basisFun K (Fin n)).linearIndependent

/-- A cycle in the augmented frame complex bounds in every length below the rank. -/
theorem frameChains_bound (k : ℕ) (hk : k + 1 ≤ n) (z : frameChains ε n k)
    (hcyc : k = 0 ∨ bd z.val = 0) :
    ∃ y : frameChains ε n (k + 1), frameBoundary ε n k y = z := by
  obtain ⟨y, hy, hbd⟩ := exact_of_independent (red ε : Col n B → Fin n → K)
    (fun i : Fin n => (Pi.single i (1 : B) : Col n B)) (reducedBasis_independent ε)
    k hk z.val z.property hcyc
  exact ⟨⟨y, hy⟩, Subtype.ext hbd⟩

theorem frameBoundary_exact (k : ℕ) (hk : k + 2 ≤ n) (z : frameChains ε n (k + 1))
    (hz : frameBoundary ε n k z = 0) :
    ∃ y : frameChains ε n (k + 2), frameBoundary ε n (k + 1) y = z := by
  have hb : bd z.val = 0 := congrArg Subtype.val hz
  exact frameChains_bound ε (k + 1) hk z (Or.inr hb)

theorem frameBoundary_zero_surjective (hn : 1 ≤ n) :
    Function.Surjective (frameBoundary ε n 0) := by
  intro z
  exact frameChains_bound ε 0 hn z (Or.inl rfl)

end
end Frames
end AllPrimeGroups
