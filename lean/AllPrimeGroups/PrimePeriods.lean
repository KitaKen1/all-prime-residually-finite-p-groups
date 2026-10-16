import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-! A choice of hierarchy parameters avoiding every p-adic valuation estimate. -/

namespace AllPrimeGroups

def blockLength (h : ℕ) : ℕ := 2 ^ (h + 1) + 1

theorem blockLength_coprime_two (h : ℕ) : (blockLength h).Coprime 2 := by
  apply Nat.coprime_comm.mpr
  rw [Nat.prime_two.coprime_iff_not_dvd]
  intro hd
  have hz := (ZMod.natCast_eq_zero_iff (blockLength h) 2).mpr hd
  simp only [blockLength, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] at hz
  rw [show (2 : ZMod 2) = 0 by decide, zero_pow (by omega : h + 1 ≠ 0), zero_add] at hz
  exact one_ne_zero hz

theorem blockLength_coprime_three {h : ℕ} (hh : Odd h) :
    (blockLength h).Coprime 3 := by
  obtain ⟨k, rfl⟩ := hh
  apply Nat.coprime_comm.mpr
  rw [Nat.prime_three.coprime_iff_not_dvd]
  intro hd
  have hz := (ZMod.natCast_eq_zero_iff (blockLength (2 * k + 1)) 3).mpr hd
  have he : 2 * k + 1 + 1 = 2 * (k + 1) := by omega
  simp only [blockLength, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] at hz
  rw [he, pow_mul, show (2 : ZMod 3) ^ 2 = 1 by decide, one_pow] at hz
  exact (by decide : (1 : ZMod 3) + 1 ≠ 0) hz

theorem blockLength_coprime_large_prime {p h : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hh : p - 1 ∣ h) : (blockLength h).Coprime p := by
  let : Fact p.Prime := ⟨hp⟩
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro hz
    have hd := (ZMod.natCast_eq_zero_iff 2 p).mp hz
    have := Nat.le_of_dvd (by decide : 0 < 2) hd
    omega
  have hpow : (2 : ZMod p) ^ h = 1 := by
    obtain ⟨k, rfl⟩ := hh
    rw [pow_mul, ZMod.pow_card_sub_one_eq_one htwo, one_pow]
  apply Nat.coprime_comm.mpr
  rw [hp.coprime_iff_not_dvd]
  intro hd
  have hz := (ZMod.natCast_eq_zero_iff (blockLength h) p).mpr hd
  have hthree : (3 : ZMod p) = 0 := by
    calc
      (3 : ZMod p) = 2 + 1 := by norm_num
      _ = (blockLength h : ZMod p) := by simp [blockLength, pow_succ, hpow]
      _ = 0 := hz
  have hd3 := (ZMod.natCast_eq_zero_iff 3 p).mp hthree
  have := Nat.le_of_dvd (by decide : 0 < 3) hd3
  omega

/-- Parameters can be chosen above any pre-existing machine threshold. -/
theorem exists_prime_free_hierarchy (p : ℕ) (hp : p.Prime) (D : ℕ) (hD : Odd D)
    (threshold : ℕ) :
    ∃ h₀ : ℕ, threshold < h₀ ∧
      ∀ j : ℕ, (blockLength (h₀ * D ^ j)).Coprime p := by
  by_cases hp2 : p = 2
  · subst p
    exact ⟨threshold + 1, by omega, fun j => blockLength_coprime_two _⟩
  by_cases hp3 : p = 3
  · subst p
    refine ⟨2 * threshold + 1, by omega, fun j => ?_⟩
    exact blockLength_coprime_three ((show Odd (2 * threshold + 1) from ⟨threshold, rfl⟩).mul
      hD.pow)
  refine ⟨(p - 1) * (threshold + 1), ?_, fun j => ?_⟩
  · have hpred : 1 ≤ p - 1 := by have := hp.two_le; omega
    nlinarith
  · apply blockLength_coprime_large_prime hp (by
      have := hp.two_le
      have hp4 : p ≠ 4 := by rintro rfl; exact (by decide : ¬ Nat.Prime 4) hp
      omega)
    exact dvd_mul_right (p - 1) (threshold + 1) |>.mul_right _


open scoped BigOperators

/-- The product period used after the first `d` hierarchy levels. -/
def phasePeriod (h₀ D d : ℕ) : ℕ :=
  ∏ j ∈ Finset.range d, blockLength (h₀ * D ^ j)

theorem phasePeriod_coprime {p h₀ D : ℕ}
    (h : ∀ j, (blockLength (h₀ * D ^ j)).Coprime p) (d : ℕ) :
    (phasePeriod h₀ D d).Coprime p :=
  Nat.coprime_prod_left_iff.mpr (fun j _ => h j)

theorem phasePeriod_ge_two_pow (h₀ D d : ℕ) : 2 ^ d ≤ phasePeriod h₀ D d := by
  induction d with
  | zero => simp [phasePeriod]
  | succ d ih =>
    have hb : 2 ≤ blockLength (h₀ * D ^ d) := by
      have := Nat.one_le_pow (h₀ * D ^ d + 1) 2 (by decide)
      unfold blockLength
      omega
    simpa [phasePeriod, Finset.prod_range_succ, pow_succ] using Nat.mul_le_mul ih hb

/-- Prime-free product periods can exceed any bound without changing the hierarchy. -/
theorem exists_large_prime_free_period {p h₀ D : ℕ}
    (h : ∀ j, (blockLength (h₀ * D ^ j)).Coprime p) (bound : ℕ) :
    ∃ d, bound < phasePeriod h₀ D d ∧ (phasePeriod h₀ D d).Coprime p := by
  exact ⟨bound, (Nat.lt_two_pow_self (n := bound)).trans_le
    (phasePeriod_ge_two_pow h₀ D bound), phasePeriod_coprime h bound⟩

/-- An odd hierarchy multiplier can also satisfy every prescribed growth threshold. -/
theorem exists_odd_multiplier (threshold : ℕ) : ∃ D, Odd D ∧ threshold < D := by
  exact ⟨2 * threshold + 1, ⟨threshold, rfl⟩, by omega⟩

end AllPrimeGroups
