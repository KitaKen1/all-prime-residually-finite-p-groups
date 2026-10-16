/-
The numeric growth estimates are adapted from OpenAI PeriodicGroups/Algebra/HierarchyGrowth.lean.
Apache-2.0; see upstream/provenance.json and upstream/OpenAI-LICENSE.
Scaling the initial dimension is new and absorbs the characteristic-p factor.
-/
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace AllPrimeGroups.HierarchyGrowth
open scoped BigOperators

def height (H D n : ℕ) : ℕ := H * D ^ n

def dimension (d k : ℕ) (s : ℕ → ℕ) : ℕ → ℕ
  | 0 => d
  | n+1 => k * s n ^ k * dimension d k s n

def exponent (H D d k c n : ℕ) : ℕ :=
  d + k*n + k*c * ∑ i ∈ Finset.range n, height H D i

lemma height_succ (H D n : ℕ) : height H D (n+1) = D * height H D n := by
  simp [height, pow_succ]; ring

lemma exponent_succ (H D d k c n : ℕ) :
    exponent H D d k c (n+1) = k + c * height H D n * k + exponent H D d k c n := by
  simp [exponent, Finset.sum_range_succ]; ring

lemma dimension_bound (H D d k c : ℕ) (s : ℕ → ℕ)
    (hs : ∀ n, s n ≤ 2 ^ (c * height H D n)) (n : ℕ) :
    dimension d k s n ≤ 2 ^ exponent H D d k c n := by
  induction n with
  | zero => simpa [dimension, exponent] using (Nat.lt_two_pow_self (n := d)).le
  | succ n ih =>
    have hk : k ≤ 2^k := (Nat.lt_two_pow_self (n := k)).le
    calc
      dimension d k s (n+1) = k * s n ^ k * dimension d k s n := rfl
      _ ≤ 2^k * (2 ^ (c * height H D n)) ^ k * 2 ^ exponent H D d k c n :=
        Nat.mul_le_mul (Nat.mul_le_mul hk (Nat.pow_le_pow_left (hs n) k)) ih
      _ = 2 ^ exponent H D d k c (n+1) := by
        simp only [← pow_mul, ← pow_add, exponent_succ]

lemma geometric_identity (H D n : ℕ) (hD : 1 ≤ D) :
    H + (D-1) * (∑ i ∈ Finset.range n, height H D i) = height H D n := by
  induction n with
  | zero => simp [height]
  | succ n ih =>
    rw [Finset.sum_range_succ, Nat.mul_add, ← Nat.add_assoc, ih, height_succ]
    have hD' : D-1+1 = D := Nat.sub_add_cancel hD
    nlinarith

lemma source_choice (c k D : ℕ) (hD : 10*(c+1)*(k+1) < D) :
    4 ≤ D ∧ 4*k*c ≤ D-1 := by
  constructor
  · nlinarith
  · have hx : 4*k*c < D := by nlinarith
    omega

theorem stopping_index (H D d k c : ℕ) (s : ℕ → ℕ)
    (hH : 1 ≤ H) (hD : 10*(c+1)*(k+1) < D)
    (hs : ∀ n, s n ≤ 2 ^ (c * height H D n)) :
    ∃ n, 400*k*(dimension d k s n)^2 < 2 ^ height H D n := by
  obtain ⟨hD4, hDcharge⟩ := source_choice c k D hD
  let L := 400*k
  let n := 2*L + 4*d + 4*k + 2
  have hn : n < 2^n := Nat.lt_two_pow_self
  have hnheight : n^2 < height H D n := by
    calc
      n^2 < (2^n)^2 := Nat.pow_lt_pow_left hn (by decide)
      _ = 4^n := by rw [← pow_mul, Nat.mul_comm n 2, pow_mul]; norm_num
      _ ≤ D^n := Nat.pow_le_pow_left hD4 n
      _ ≤ H*D^n := Nat.le_mul_of_pos_left _ hH
  have hfree : 2*L + 4*d + 4*k*n < height H D n := by
    have hnlarge : 2*L + 4*d + 4*k + 2 = n := rfl
    nlinarith
  have hcharge : 4*k*c*(∑ i ∈ Finset.range n, height H D i) ≤ height H D n := by
    have hi := geometric_identity H D n (by omega)
    have hm := Nat.mul_le_mul_right (∑ i ∈ Finset.range n, height H D i) hDcharge
    omega
  have hexp : L + 2 * exponent H D d k c n < height H D n := by
    unfold exponent
    nlinarith
  refine ⟨n, ?_⟩
  calc
    400*k*(dimension d k s n)^2 ≤ 2^L * (2 ^ exponent H D d k c n)^2 :=
      Nat.mul_le_mul (Nat.lt_two_pow_self (n := L)).le
        (Nat.pow_le_pow_left (dimension_bound H D d k c s hs n) 2)
    _ = 2 ^ (L + 2 * exponent H D d k c n) := by
      simp only [← pow_mul, ← pow_add]
      congr 1
      omega
    _ < 2 ^ height H D n := Nat.pow_lt_pow_right (by decide) hexp

end AllPrimeGroups.HierarchyGrowth

namespace AllPrimeGroups.HierarchyGrowth

/-- The automaton dimension recurrence is linear in the initial dimension. -/
theorem dimension_scale (p d k : ℕ) (s : ℕ → ℕ) (n : ℕ) :
    dimension (p * d) k s n = p * dimension d k s n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [dimension, ih]; ring

/-- The original stopping argument handles the extra characteristic-p factor
by being applied to the initial dimension p*d. No new asymptotic proof is needed. -/
theorem stopping_index_char (p H D d k c : ℕ) (s : ℕ → ℕ) (hp : 1 ≤ p)
    (hH : 1 ≤ H) (hD : 10 * (c + 1) * (k + 1) < D)
    (hs : ∀ n, s n ≤ 2 ^ (c * height H D n)) :
    ∃ n, 400 * k * (p - 1) * (dimension d k s n) ^ 2 < 2 ^ height H D n := by
  obtain ⟨n, hn⟩ := stopping_index H D (p * d) k c s hH hD hs
  refine ⟨n, lt_of_le_of_lt ?_ hn⟩
  rw [dimension_scale]
  have hp2 : p - 1 ≤ p ^ 2 := by
    have := Nat.sub_le p 1
    nlinarith
  have he := Nat.mul_le_mul_left (400 * k * (dimension d k s n) ^ 2) hp2
  simpa only [mul_pow, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using he

end AllPrimeGroups.HierarchyGrowth
