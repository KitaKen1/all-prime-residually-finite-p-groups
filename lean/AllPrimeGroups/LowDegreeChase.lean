import Mathlib.Algebra.Group.Hom.Basic

/-! A finite double-complex chase for lifting a horizontal degree-two cohomology cycle.

Only horizontal exactness in columns one through three, vertical H¹ vanishing in column three,
and injectivity on vertical H⁰ in column four are needed. No spectral sequence is constructed. -/

namespace AllPrimeGroups

universe u

/-- A closed element in bidegree `(1,2)` whose horizontal image is a vertical boundary
comes from a closed element in column zero, up to a vertical boundary. -/
theorem low_degree_lift
    {C : ℕ → ℕ → Type u} [∀ k q, AddCommGroup (C k q)]
    (h : ∀ k q, C k q →+ C (k + 1) q)
    (v : ∀ k q, C k q →+ C k (q + 1))
    (hh : ∀ k q x, h (k + 1) q (h k q x) = 0)
    (vv : ∀ k q x, v k (q + 1) (v k q x) = 0)
    (comm : ∀ k q x, h k (q + 1) (v k q x) = v (k + 1) q (h k q x))
    (hex : ∀ k, k ≤ 2 → ∀ q (x : C (k + 1) q),
      h (k + 1) q x = 0 → ∃ y, h k q y = x)
    (hinj : Function.Injective (h 0 3))
    (hv1 : ∀ x : C 3 1, v 3 1 x = 0 → ∃ y, v 3 0 y = x)
    (hv0 : ∀ x : C 4 0, v 4 0 x = 0 → h 4 0 x = 0 → x = 0)
    (c : C 1 2) (hc : v 1 2 c = 0)
    (b : C 2 1) (hb : h 1 2 c = v 2 1 b) :
    ∃ (z : C 0 2) (d : C 1 1), v 0 2 z = 0 ∧ h 0 2 z = c - v 1 1 d := by
  have hclosed : v 3 1 (h 2 1 b) = 0 := by
    rw [← comm, ← hb, hh]
  obtain ⟨a, ha⟩ := hv1 (h 2 1 b) hclosed
  have hva : v 4 0 (h 3 0 a) = 0 := by
    rw [← comm, ha, hh]
  have hha : h 3 0 a = 0 := hv0 _ hva (hh 3 0 a)
  obtain ⟨e, he⟩ := hex 2 (by decide) 0 a hha
  have hbe : h 2 1 (b - v 2 0 e) = 0 := by
    rw [map_sub, comm, he, ha, sub_self]
  obtain ⟨d, hd⟩ := hex 1 (by decide) 1 (b - v 2 0 e) hbe
  have hcd : h 1 2 (c - v 1 1 d) = 0 := by
    rw [map_sub, comm, hd, map_sub, vv, sub_zero, hb, sub_self]
  obtain ⟨z, hz⟩ := hex 0 (by decide) 2 (c - v 1 1 d) hcd
  refine ⟨z, d, ?_, hz⟩
  apply hinj
  rw [map_zero, comm, hz, map_sub, hc, vv, sub_self]

end AllPrimeGroups
