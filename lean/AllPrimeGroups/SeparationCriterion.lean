import AllPrimeGroups.RelativeTorsion
import AllPrimeGroups.Separation

/-! A criterion for stable separation (manuscript Proposition 9.1 and the end of the proof of
Theorem 22.2).

For a graded algebra over `ZMod ℓ`, let z be an element of the stable matrix kernel with
trivial stable reduction. Relative torsion gives z an ℓ-power order, and removal of the wrap
entry shows that its graded evaluation at every sufficiently large cyclic shift is trivial.
If, for arbitrarily large moduli m prime to ℓ, that evaluation at the shift of size m equals
z^m, then z = 1.

The hypothesis `hcyc` is manuscript Proposition 21.2 together with Lemma 22.1. It is an
explicit hypothesis here and is not proved in this file. -/

namespace AllPrimeGroups
noncomputable section

namespace Kernel
variable {ℓ : ℕ} [Fact ℓ.Prime] {n : ℕ} {R : Type*} [Ring R] [Algebra (ZMod ℓ) R]

/-- A polynomial matrix-kernel element with trivial value at zero has trivial evaluation at
every sufficiently large cyclic shift. -/
theorem cyclic_evaluation_eq_one (hn : 3 ≤ n)
    (u : Steinberg n (Polynomial R)) (hu : Elementary.representation u = 1)
    (hv : Steinberg.map (scalarEval (0 : ZMod ℓ)) u = 1) :
    ∃ B : ℕ, ∀ N : ℕ, B < N → matrixSteinbergEval (cyclicShift N (ZMod ℓ)) u = 1 := by
  classical
  obtain ⟨l, hl⟩ := exists_rootWord u
  let p : Root n := ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by
    intro he
    have hh : (0 : ℕ) = 1 := congrArg Fin.val he
    omega⟩
  let l' := l ++ [(p, (0 : Polynomial R))]
  have hl' : rootWord l' = u := by
    simp [l', rootWord, Steinberg.x_zero] at hl ⊢
    exact hl
  have hm : 1 ≤ l'.length := by
    dsimp [l']
    simp
  let d := l'.toFinset.sup (fun pa => pa.2.natDegree)
  have hd : ∀ pa ∈ l', pa.2.natDegree ≤ d := by
    intro pa hpa
    exact Finset.le_sup (f := fun pa : Root n × Polynomial R => pa.2.natDegree)
      (List.mem_toFinset.mpr hpa)
  have hmat : Elementary.representation (rootWord l') = 1 := hl' ▸ hu
  have hval : Steinberg.map (scalarEval (0 : ZMod ℓ)) (rootWord l') = 1 := hl' ▸ hv
  refine ⟨2 * (l'.length + 1) * max 1 d, fun N hN => ?_⟩
  have h1 := wrap_removal (ℓ := ℓ) l' hm d hd hN hmat
  have h2 := triangular_evaluation (ℓ := ℓ) (N := N) (R := R) truncatedShift_upper 0
    truncatedShift_diag (rootWord l') hmat
  rw [hl'] at h1 h2
  rw [h1, h2, hv, map_one]

end Kernel

namespace Stable
variable {R : Type*} [Ring R]

/-- A stable matrix-kernel element with trivial stable reduction is represented, at some rank
at least three, by an element with identity matrix image and trivial reduction. -/
theorem exists_kernel_representative {S : Type*} [Ring S] (ε : R →+* S)
    (z : StableSteinberg R) (hz : representation R z = 1) (hε : map ε z = 1) :
    ∃ (m : ℕ) (u : Steinberg m R), 3 ≤ m ∧ of R m u = z ∧
      Elementary.representation u = 1 ∧ Steinberg.map ε u = 1 := by
  obtain ⟨n₀, u₀, hzu⟩ := Chain.exists_stage (steinbergStep R) z
  have hzu' : z = of R n₀ u₀ := hzu
  have hn₀ : n₀ ≤ max n₀ 3 := le_max_left _ _
  have hn3 : 3 ≤ max n₀ 3 := le_max_right _ _
  have hu₁ := of_castLE R hn₀ u₀
  have hε' : of S (max n₀ 3) (Steinberg.map ε
      (Steinberg.coordinateMap (Fin.castLE hn₀) (Fin.castLE_injective _) u₀)) = 1 := by
    rw [← map_of, hu₁, ← hzu']
    exact hε
  obtain ⟨m, hnm, hm⟩ := (of_eq_one_iff S (max n₀ 3) _).mp hε'
  rw [connect_eq_castLE S, ← Steinberg.coordinateMap_ringMap] at hm
  have hu := (of_castLE R hnm
    (Steinberg.coordinateMap (Fin.castLE hn₀) (Fin.castLE_injective _) u₀)).trans hu₁
  generalize Steinberg.coordinateMap (Fin.castLE hnm) (Fin.castLE_injective _)
    (Steinberg.coordinateMap (Fin.castLE hn₀) (Fin.castLE_injective _) u₀) = u at hm hu
  exact ⟨m, u, hn3.trans hnm, hu.trans hzu'.symm,
    finite_matrix_kernel R m u (by rw [hu, ← hzu']; exact hz), hm⟩

/-- Manuscript Proposition 9.1 in the stable group: relative torsion and wrap removal reduce
stable separation to the identity `W_z(C_m) = z^m` for arbitrarily large moduli m prime to
the characteristic. -/
theorem eq_one_of_cyclic_evaluation {ℓ : ℕ} [Fact ℓ.Prime] [Algebra (ZMod ℓ) R]
    (ε : R →+* ZMod ℓ) (γ : R →+* Polynomial R)
    (h1 : (Kernel.scalarEval (1 : ZMod ℓ)).comp γ = RingHom.id R)
    (h0 : (Kernel.scalarEval (0 : ZMod ℓ)).comp γ = (algebraMap (ZMod ℓ) R).comp ε)
    (z : StableSteinberg R) (hz : representation R z = 1) (hε : map ε z = 1)
    (hcyc : ∀ B : ℕ, ∃ m : ℕ, B < m ∧ m.Coprime ℓ ∧
      ∀ (n : ℕ) (u : Steinberg n R), 3 ≤ n → of R n u = z → Elementary.representation u = 1 →
        Steinberg.map ε u = 1 →
        of R (n * m) (Kernel.matrixSteinbergEval (Kernel.cyclicShift m (ZMod ℓ))
          (Steinberg.map γ u)) = z ^ m) :
    z = 1 := by
  obtain ⟨a, ha⟩ := relative_torsion ε γ h1 h0 z hz hε
  obtain ⟨n, u, hn, hu, hrep, hground⟩ := exists_kernel_representative ε z hz hε
  have hû : Elementary.representation (Steinberg.map γ u) = 1 := Elementary.map_kernel γ u hrep
  have hv : Steinberg.map (Kernel.scalarEval (0 : ZMod ℓ)) (Steinberg.map γ u) = 1 := by
    rw [Steinberg.map_map, h0, ← Steinberg.map_map, hground, map_one]
  obtain ⟨B, hB⟩ := Kernel.cyclic_evaluation_eq_one hn (Steinberg.map γ u) hû hv
  obtain ⟨m, hBm, hcop, hm⟩ := hcyc B
  have hzm : z ^ m = 1 := by
    rw [← hm n u hn hu hrep hground, hB m hBm, map_one]
  exact eq_one_of_coprime_powers z (hcop.pow_right a) hzm ha

end Stable
end
end AllPrimeGroups
