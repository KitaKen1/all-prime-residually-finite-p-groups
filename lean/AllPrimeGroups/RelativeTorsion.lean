import AllPrimeGroups.PolynomialTorsion
import AllPrimeGroups.StableMap

/-! Relative ℓ-power torsion in the stable matrix kernel (manuscript Theorem 14.1).

The grading enters only through a ring homomorphism `γ` to polynomials whose value at one is
the identity and whose value at zero is the reduction to the prime field. An element of the
stable matrix kernel with trivial stable reduction then has ℓ-power order. Neither matrix
nilpotence nor finite presentation is used, and no finite-rank injectivity is assumed. -/

namespace AllPrimeGroups
noncomputable section

namespace Steinberg
variable {n m : ℕ} {R S : Type*} [Ring R] [Ring S]

lemma coordinateMap_ringMap (f : R →+* S) (g : Fin n → Fin m) (hg : Function.Injective g)
    (u : Steinberg n R) :
    map f (coordinateMap g hg u) = coordinateMap g hg (map f u) := by
  have he : (map f).comp (coordinateMap g hg) = (coordinateMap g hg).comp (map (n := n) f) := by
    apply hom_ext
    intro p a
    simp only [MonoidHom.comp_apply, coordinateMap_x, map_x]
  exact DFunLike.congr_fun he u

end Steinberg

namespace Stable
variable (R : Type*) [Ring R]

/-- The transition maps of the stable chain are the standard coordinate embeddings. -/
theorem connect_eq_castLE (n m : ℕ) (h : n ≤ m) :
    Chain.connect (steinbergStep R) n m h =
      Steinberg.coordinateMap (Fin.castLE h) (Fin.castLE_injective _) := by
  induction m, h using Nat.le_induction with
  | base =>
    have h0 : Chain.connect (steinbergStep R) n n le_rfl = MonoidHom.id _ := by
      unfold Chain.connect
      exact Nat.leRecOn_self _
    rw [h0]
    apply Steinberg.hom_ext
    intro p a
    rfl
  | succ m h ih =>
    rw [Chain.connect_succ (steinbergStep R) n m h, ih]
    apply Steinberg.hom_ext
    intro p a
    rfl

theorem of_castLE {n m : ℕ} (h : n ≤ m) (u : Steinberg n R) :
    of R m (Steinberg.coordinateMap (Fin.castLE h) (Fin.castLE_injective _) u) = of R n u := by
  rw [← connect_eq_castLE]
  exact Chain.of_connect (steinbergStep R) n m h u

variable {R}

/-- Manuscript Theorem 14.1 in the stable group. -/
theorem relative_torsion {ℓ : ℕ} [Fact ℓ.Prime] [Algebra (ZMod ℓ) R]
    (ε : R →+* ZMod ℓ) (γ : R →+* Polynomial R)
    (h1 : (Kernel.scalarEval (1 : ZMod ℓ)).comp γ = RingHom.id R)
    (h0 : (Kernel.scalarEval (0 : ZMod ℓ)).comp γ = (algebraMap (ZMod ℓ) R).comp ε)
    (z : StableSteinberg R) (hz : representation R z = 1) (hε : map ε z = 1) :
    ∃ a : ℕ, z ^ ℓ ^ a = 1 := by
  obtain ⟨n₀, u₀, hzu⟩ := Chain.exists_stage (steinbergStep R) z
  have hzu' : z = of R n₀ u₀ := hzu
  have hn₀ : n₀ ≤ max n₀ 3 := le_max_left _ _
  have hn3 : 3 ≤ max n₀ 3 := le_max_right _ _
  have hu₁ := of_castLE R hn₀ u₀
  have hε' : of (ZMod ℓ) (max n₀ 3) (Steinberg.map ε
      (Steinberg.coordinateMap (Fin.castLE hn₀) (Fin.castLE_injective _) u₀)) = 1 := by
    rw [← map_of, hu₁, ← hzu']
    exact hε
  obtain ⟨m, hnm, hm⟩ := (of_eq_one_iff (ZMod ℓ) (max n₀ 3) _).mp hε'
  rw [connect_eq_castLE (ZMod ℓ), ← Steinberg.coordinateMap_ringMap] at hm
  have hm3 : 3 ≤ m := hn3.trans hnm
  have hu := (of_castLE R hnm
    (Steinberg.coordinateMap (Fin.castLE hn₀) (Fin.castLE_injective _) u₀)).trans hu₁
  generalize Steinberg.coordinateMap (Fin.castLE hnm) (Fin.castLE_injective _)
    (Steinberg.coordinateMap (Fin.castLE hn₀) (Fin.castLE_injective _) u₀) = u at hm hu
  have hrep : Elementary.representation u = 1 :=
    finite_matrix_kernel R m u (by rw [hu, ← hzu']; exact hz)
  have hû : Elementary.representation (Steinberg.map γ u) = 1 := Elementary.map_kernel γ u hrep
  have hv : Steinberg.map (Kernel.scalarEval (0 : ZMod ℓ)) (Steinberg.map γ u) = 1 := by
    rw [Steinberg.map_map, h0, ← Steinberg.map_map, hm, map_one]
  have hone : Steinberg.map (Kernel.scalarEval (1 : ZMod ℓ)) (Steinberg.map γ u) = u := by
    rw [Steinberg.map_map, h1, Steinberg.map_identity]
    rfl
  obtain ⟨q, hmq, k, hk⟩ := Kernel.polynomial_kernel_standard_torsion hm3 (Steinberg.map γ u) hû hv
  rw [hone] at hk
  refine ⟨k, ?_⟩
  rw [hzu', ← hu, ← of_castLE R hmq u, ← map_pow, hk, map_one]

end Stable
end
end AllPrimeGroups
