import AllPrimeGroups.ChainLimit
import AllPrimeGroups.Stabilization

/-! The stable Steinberg group as a genuine mathlib direct limit.
No finite-rank injectivity is assumed in its construction or its centrality theorem. -/

namespace AllPrimeGroups
noncomputable section

variable (R : Type*) [Ring R]

abbrev steinbergStep (n : ℕ) : Steinberg n R →* Steinberg (n + 1) R :=
  Kernel.padSteinberg

abbrev matrixStep (n : ℕ) : (Matrix (Fin n) (Fin n) R)ˣ →*
    (Matrix (Fin (n + 1)) (Fin (n + 1)) R)ˣ := Kernel.padUnitsHom

abbrev StableSteinberg := Chain.Limit (steinbergStep R)
abbrev StableMatrixUnits := Chain.Limit (matrixStep R)

namespace Stable

def of (n : ℕ) : Steinberg n R →* StableSteinberg R := Chain.of (steinbergStep R) n

def matrixOf (n : ℕ) : (Matrix (Fin n) (Fin n) R)ˣ →* StableMatrixUnits R :=
  Chain.of (matrixStep R) n

theorem matrixStep_injective (n : ℕ) : Function.Injective (matrixStep R n) := by
  intro u v h
  have hm : (Kernel.blockUnits u).val = (Kernel.blockUnits v).val :=
    (Matrix.reindexRingEquiv R (Kernel.coordinateEquiv n)).injective (congrArg Units.val h)
  apply Units.ext
  ext i j
  simpa [Kernel.blockUnits, Matrix.fromBlocks] using
    congrArg (fun M => M (Sum.inl i) (Sum.inl j)) hm

theorem matrixOf_injective (n : ℕ) : Function.Injective (matrixOf R n) :=
  Chain.of_injective (matrixStep R) (matrixStep_injective R) n

def representation : StableSteinberg R →* StableMatrixUnits R :=
  Chain.lift (steinbergStep R)
    (fun n => (matrixOf R n).comp (Elementary.representation (n := n))) (by
      intro n
      apply MonoidHom.ext
      intro g
      have he := DFunLike.congr_fun (Kernel.pad_representation (n := n) (R := R)) g
      simp only [MonoidHom.comp_apply] at he ⊢
      rw [he]
      exact Chain.of_step (matrixStep R) n (Elementary.representation g))

@[simp] theorem representation_of (n : ℕ) (g : Steinberg n R) :
    representation R (of R n g) = matrixOf R n (Elementary.representation g) := by
  simp only [representation, of, Chain.lift_of, MonoidHom.comp_apply]

theorem of_eq_one_iff (n : ℕ) (g : Steinberg n R) :
    of R n g = 1 ↔ ∃ m, ∃ h : n ≤ m, Chain.connect (steinbergStep R) n m h g = 1 :=
  Chain.of_eq_one_iff (steinbergStep R) n g

/-- A zero stable matrix image already means a zero finite matrix image. -/
theorem finite_matrix_kernel (n : ℕ) (g : Steinberg n R)
    (hg : representation R (of R n g) = 1) : Elementary.representation g = 1 := by
  apply matrixOf_injective R n
  simpa only [representation_of, map_one] using hg

/-- The stable matrix kernel is central, over every unital ring.
This uses faithful strips and a fresh coordinate, and proves a group assertion. -/
theorem kernel_central (g : StableSteinberg R) (hg : representation R g = 1) :
    g ∈ Subgroup.center (StableSteinberg R) := by
  obtain ⟨n, g, rfl⟩ := Chain.exists_stage (steinbergStep R) g
  apply Subgroup.mem_center_iff.mpr
  intro h
  obtain ⟨m, h, rfl⟩ := Chain.exists_stage (steinbergStep R) h
  let k := max n m
  let gk := Chain.connect (steinbergStep R) n k (le_max_left n m) g
  let hk := Chain.connect (steinbergStep R) m k (le_max_right n m) h
  have hgOf : of R k gk = of R n g := Chain.of_connect (steinbergStep R) n k _ g
  have hhOf : of R k hk = of R m h := Chain.of_connect (steinbergStep R) m k _ h
  have hgk : Elementary.representation gk = 1 :=
    finite_matrix_kernel R k gk (by rw [hgOf]; exact hg)
  have hc := Kernel.stabilized_kernel_central gk hgk
  have he := Subgroup.mem_center_iff.mp hc (Kernel.padSteinberg hk)
  have hgNext : of R (k + 1) (Kernel.padSteinberg gk) = of R n g :=
    (Chain.of_step (steinbergStep R) k gk).trans hgOf
  have hhNext : of R (k + 1) (Kernel.padSteinberg hk) = of R m h :=
    (Chain.of_step (steinbergStep R) k hk).trans hhOf
  have H := congrArg (of R (k + 1)) he
  simp only [map_mul] at H
  rw [hgNext, hhNext] at H
  change of R m h * of R n g = of R n g * of R m h
  exact H

/-- The actual map from the finite-rank matrix kernel to the stable matrix kernel. -/
def kernelMap (n : ℕ) : (Elementary.representation (n := n) (R := R)).ker →*
    (representation R).ker where
  toFun g := ⟨of R n g.val, by
    have hg : Elementary.representation g.val = 1 := g.property
    change representation R (of R n g.val) = 1
    rw [representation_of, hg, map_one]⟩
  map_one' := Subtype.ext (map_one (of R n))
  map_mul' g h := Subtype.ext (map_mul (of R n) g.val h.val)

/-- Finite-rank injectivity reduces exactly to injectivity on K₂.
The injectivity of kernelMap remains the substantive stability theorem to prove. -/
theorem of_injective_iff_kernelMap_injective (n : ℕ) :
    Function.Injective (of R n) ↔ Function.Injective (kernelMap R n) := by
  constructor
  · intro hinj x y hxy
    apply Subtype.ext
    exact hinj (congrArg Subtype.val hxy)
  · intro hinj
    apply (of R n).ker_eq_bot_iff.mp
    apply (Subgroup.eq_bot_iff_forall _).mpr
    intro g hg
    have hg' : of R n g = 1 := hg
    have hmat : Elementary.representation g = 1 :=
      finite_matrix_kernel R n g (by rw [hg', map_one])
    let z : (Elementary.representation (n := n) (R := R)).ker := ⟨g, hmat⟩
    have hz : kernelMap R n z = kernelMap R n 1 := by
      apply Subtype.ext
      change of R n g = of R n 1
      rw [hg', map_one]
    exact congrArg Subtype.val (hinj hz)

theorem root_injective (n : ℕ) (p : Root n) :
    Function.Injective (fun a : R => of R n (Steinberg.x p a)) := by
  intro a b h
  apply Elementary.e_injective p
  apply matrixOf_injective R n
  simpa only [representation_of, Elementary.representation_x] using congrArg (representation R) h

theorem infinite [Infinite R] {n : ℕ} (p : Root n) : Infinite (StableSteinberg R) :=
  Infinite.of_injective _ (root_injective R n p)

/-- This is the remaining finite-rank assertion. It is stated but not assumed or proved. -/
def FiniteRankInjectivity : Prop :=
  ∀ n : ℕ, 12 ≤ n → Function.Injective (of R n)

end Stable
end
end AllPrimeGroups
