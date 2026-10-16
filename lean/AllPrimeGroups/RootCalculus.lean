/-
The commutator calculus below is adapted from OpenAI's PeriodicGroups,
Steinberg/MonomialPresentation.lean (commit 1581d4cbdd69a0faf34b2089614fe2a814316a6a).
Apache-2.0; see upstream/OpenAI-LICENSE and upstream/provenance.json.
The root-family interface and cut-moving theorem are new.
-/
import Mathlib.Algebra.Group.Commute.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.CharP.Basic
import Mathlib.GroupTheory.Commutator.Basic

namespace AllPrimeGroups

def bracket {G : Type*} [Group G] (x y : G) : G := x * y * x⁻¹ * y⁻¹

theorem bracket_eq_one_iff {G : Type*} [Group G] (a b : G) :
    bracket a b = 1 ↔ Commute a b := by
  simp only [bracket, mul_inv_eq_iff_eq_mul, one_mul]
  rfl

namespace CommutatorCalculus

variable {G : Type*} [Group G]

 theorem commute_bracket_right {x a b : G} (ha : Commute x a) (hb : Commute x b) :
    Commute x (bracket a b) :=
  ((ha.mul_right hb).mul_right ha.inv_right).mul_right hb.inv_right

 theorem commute_bracket_left {a b x : G} (ha : Commute a x) (hb : Commute b x) :
    Commute (bracket a b) x := (commute_bracket_right ha.symm hb.symm).symm

 theorem mul_left (a b c : G) :
    bracket (a * b) c = a * bracket b c * a⁻¹ * bracket a c := by
  simp [bracket, mul_assoc]

 theorem mul_right (a b c : G) :
    bracket a (b * c) = bracket a b * b * bracket a c * b⁻¹ := by
  simp [bracket, mul_assoc]

 theorem conj_of_commute {a b : G} (h : Commute a b) : a * b * a⁻¹ = b := by
  rw [h.eq, mul_inv_cancel_right]

 theorem separated (a b c d : G)
    (hac : Commute a c) (had : Commute a d)
    (hbc : Commute b c) (hbd : Commute b d) :
    bracket (a * c) (b * d) = bracket a b * bracket c d := by
  have hAD := commute_bracket_right hac had
  have hBD := commute_bracket_right hbc hbd
  rw [mul_left, mul_right, mul_right,
    (bracket_eq_one_iff _ _).mpr hbc.symm,
    (bracket_eq_one_iff _ _).mpr had]
  simp only [one_mul, mul_one, mul_inv_cancel_right]
  rw [conj_of_commute hBD, conj_of_commute hAD]
  exact (commute_bracket_left hAD hBD).symm.eq

 theorem three_factor (X Y Z : G)
    (hAX : Commute (bracket X Y) X) (_hAY : Commute (bracket X Y) Y)
    (_hBY : Commute (bracket Y Z) Y) (hBZ : Commute (bracket Y Z) Z)
    (hAB : Commute (bracket X Y) (bracket Y Z)) (hXZ : Commute X Z) :
    bracket (bracket X Y) Z = bracket X (bracket Y Z) ∧
    Commute (bracket (bracket X Y) Z) (bracket X Y) ∧
    Commute (bracket (bracket X Y) Z) Z ∧
    Commute (bracket (bracket X Y) Z) X ∧
    Commute (bracket (bracket X Y) Z) (bracket Y Z) := by
  let A := bracket X Y
  let B := bracket Y Z
  let C := bracket A⁻¹ Z
  let D := bracket X B
  have hconjX : Y * X * Y⁻¹ = A⁻¹ * X := by simp [A, bracket, mul_assoc]
  have hconjZ : Y * Z * Y⁻¹ = B * Z := by simp [B, bracket, mul_assoc]
  have hc : Commute (A⁻¹ * X) (Z * B) := by
    have hBZeq : B * Z = Z * B := hBZ.eq
    simpa only [hconjX, hconjZ, hBZeq] using hXZ.conj Y
  have hCD : C * D = 1 := by
    rw [← separated A⁻¹ Z X B hAX.inv_left hAB.inv_left hXZ.symm hBZ.symm]
    exact (bracket_eq_one_iff _ _).mpr hc
  have hC : C = D⁻¹ := eq_inv_of_mul_eq_one_left hCD
  have hDA : Commute D A := commute_bracket_left hAX.symm hAB.symm
  have hDZ : Commute D Z := commute_bracket_left hXZ hBZ
  have hCX : Commute C X := commute_bracket_left hAX.inv_left hXZ.symm
  have hCB : Commute C B := commute_bracket_left hAB.inv_left hBZ.symm
  have hCA : Commute C A := hC ▸ hDA.inv_left
  have hmain : bracket A Z = D := by
    apply inv_injective
    calc
      (bracket A Z)⁻¹ = A * C * A⁻¹ := by simp [C, bracket, mul_assoc]
      _ = C := conj_of_commute hCA.symm
      _ = D⁻¹ := hC
  refine ⟨hmain, ?_, ?_, ?_, ?_⟩
  · exact hmain ▸ hDA
  · exact hmain ▸ hDZ
  · rw [hmain]
    exact (Commute.inv_left_iff.mp (hC ▸ hCX))
  · rw [hmain]
    exact (Commute.inv_left_iff.mp (hC ▸ hCB))

end CommutatorCalculus

/-- The defining root identities used by the cut-moving argument.
No injectivity or assertion about opposite roots is assumed. -/
structure RootFamily (ι R G : Type*) [Ring R] [Group G] where
  x : ι → ι → R → G
  zero : ∀ i j, x i j 0 = 1
  commute : ∀ i j k l, j ≠ k → i ≠ l → ∀ a b, Commute (x i j a) (x k l b)
  product : ∀ i j k, i ≠ j → j ≠ k → i ≠ k → ∀ a b,
    bracket (x i j a) (x j k b) = x i k (a * b)

namespace RootFamily
variable {ι R G : Type*} [Ring R] [Group G] (s : RootFamily ι R G)

theorem consecutive_commute {i j k : ι} (hij : i ≠ j) (hjk : j ≠ k)
    (hik : i ≠ k) {a b : R} (hab : a * b = 0) :
    Commute (s.x i j a) (s.x j k b) := by
  apply (bracket_eq_one_iff _ _).mp
  rw [s.product i j k hij hjk hik, hab, s.zero]

/-- The exact group identity in manuscript Lemma 20.1, valid over any unital ring. -/
theorem move_cut_and_centralizes {i h j : ι} (hih : i ≠ h) (hhj : h ≠ j) (hij : i ≠ j)
    (a b c : R) (hca : c * a = 0) :
    bracket (s.x i j (a * b)) (s.x j i c) =
      bracket (s.x i h a) (s.x h i (b * c)) ∧
    Commute (bracket (s.x i j (a * b)) (s.x j i c)) (s.x i j (a * b)) ∧
    Commute (bracket (s.x i j (a * b)) (s.x j i c)) (s.x j i c) := by
  have hA := s.product i h j hih hhj hij a b
  have hB := s.product h j i hhj hij.symm hih.symm b c
  have hzero : (b * c) * (a * b) = 0 := by
    rw [mul_assoc, ← mul_assoc c, hca, zero_mul, mul_zero]
  have hc := CommutatorCalculus.three_factor (s.x i h a) (s.x h j b) (s.x j i c)
    (by rw [hA]; exact s.commute i j i h hij.symm hih _ _)
    (by rw [hA]; exact s.commute i j h j hhj.symm hij _ _)
    (by rw [hB]; exact s.commute h i h j hih hhj _ _)
    (by rw [hB]; exact s.commute h i j i hij hih.symm _ _)
    (by rw [hA, hB]; exact (s.consecutive_commute hih.symm hij hhj hzero).symm)
    ((s.consecutive_commute hij.symm hih hhj.symm hca).symm)
  simpa only [hA, hB] using And.intro hc.1 (And.intro hc.2.1 hc.2.2.1)


theorem move_cut {i h j : ι} (hih : i ≠ h) (hhj : h ≠ j) (hij : i ≠ j)
    (a b c : R) (hca : c * a = 0) :
    bracket (s.x i j (a * b)) (s.x j i c) =
      bracket (s.x i h a) (s.x h i (b * c)) :=
  (s.move_cut_and_centralizes hih hhj hij a b c hca).1

theorem opposite_commutator_centralizes {i h j : ι}
    (hih : i ≠ h) (hhj : h ≠ j) (hij : i ≠ j) (a c : R) (hca : c * a = 0) :
    Commute (bracket (s.x i j a) (s.x j i c)) (s.x i j a) ∧
    Commute (bracket (s.x i j a) (s.x j i c)) (s.x j i c) := by
  simpa only [mul_one, one_mul] using
    (s.move_cut_and_centralizes hih hhj hij a 1 c hca).2

/-- Additivity, rather than an involution argument, gives root exponent p. -/
theorem root_pow_char (p : ℕ) [CharP R p]
    (hadd : ∀ i j a b, s.x i j (a + b) = s.x i j a * s.x i j b)
    (i j : ι) (a : R) : s.x i j a ^ p = 1 := by
  have hn (n : ℕ) : s.x i j (n • a) = s.x i j a ^ n := by
    induction n with
    | zero => simp [s.zero]
    | succ n ih => rw [succ_nsmul, hadd, ih, pow_succ]
  have hp : p • a = 0 := by rw [nsmul_eq_mul, CharP.cast_eq_zero R p, zero_mul]
  rw [← hn, hp, s.zero]

theorem opposite_commutator_pow_char (p : ℕ) [CharP R p]
    (hadd : ∀ i j a b, s.x i j (a + b) = s.x i j a * s.x i j b)
    {i h j : ι} (hih : i ≠ h) (hhj : h ≠ j) (hij : i ≠ j)
    (a c : R) (hca : c * a = 0) :
    bracket (s.x i j a) (s.x j i c) ^ p = 1 := by
  have hc := (s.opposite_commutator_centralizes hih hhj hij a c hca).1.symm
  have hp := hc.commutatorElement_pow_left p
  change bracket (s.x i j a) (s.x j i c) ^ p = bracket (s.x i j a ^ p) (s.x j i c) at hp
  rw [s.root_pow_char p hadd] at hp
  simpa [bracket] using hp

end RootFamily
end AllPrimeGroups
