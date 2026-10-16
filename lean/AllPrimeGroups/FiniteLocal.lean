import AllPrimeGroups.GLAction
import AllPrimeGroups.FinitePerfect

/-! Finite-rank Steinberg groups over finite local coefficient rings.
Centrality of the matrix kernel and Schur's theorem suffice; no stabilization
injectivity or classification of the kernel is needed. -/

namespace AllPrimeGroups.Steinberg

variable {B K : Type*} [Ring B] [Field K]

/-- Manuscript Theorem 13.2, using the unit-reflection form of the local hypothesis. -/
theorem finite_of_local_augmentation [Finite B] (ε : B →+* K)
    (hunit : ∀ b : B, ε b ≠ 0 → IsUnit b) {n : ℕ} (hn : 6 ≤ n) :
    Finite (Steinberg n B) := by
  have : Group.IsPerfect (Steinberg n B) := isPerfect (by omega)
  have : (Elementary.representation (n := n) (R := B)).ker.FiniteIndex := inferInstance
  have hcentral : (Elementary.representation (n := n) (R := B)).ker ≤
      Subgroup.center (Steinberg n B) := by
    intro z hz
    exact GLAct.kernel_central ε hunit hn hz
  have : (Subgroup.center (Steinberg n B)).FiniteIndex := Subgroup.finiteIndex_of_le hcentral
  exact finite_of_perfect_finite_center_quotient (Steinberg n B)

/-- In particular the finite-rank Steinberg group of a finite field is finite. -/
theorem finite_of_finite_field [Finite K] {n : ℕ} (hn : 6 ≤ n) : Finite (Steinberg n K) :=
  finite_of_local_augmentation (RingHom.id K) (fun _ h => isUnit_iff_ne_zero.mpr h) hn

end AllPrimeGroups.Steinberg
