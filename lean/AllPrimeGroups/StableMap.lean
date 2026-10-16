import AllPrimeGroups.StableGroup

/-! Functoriality of the stable Steinberg group in the coefficient ring.
Applying a ring homomorphism and then stabilizing agrees with stabilizing first
(manuscript Section 2, "naturality"). -/

namespace AllPrimeGroups
noncomputable section

variable {R S T : Type*} [Ring R] [Ring S] [Ring T]

namespace Kernel

theorem padSteinberg_map (f : R →+* S) (n : ℕ) :
    (padSteinberg (n := n) (R := S)).comp (Steinberg.map f) =
      (Steinberg.map f).comp (padSteinberg (n := n) (R := R)) := by
  apply Steinberg.hom_ext
  intro p a
  simp only [MonoidHom.comp_apply, padSteinberg, Steinberg.map_x, Steinberg.coordinateMap_x]

end Kernel

namespace Stable

/-- The homomorphism of stable Steinberg groups induced by a ring homomorphism. -/
def map (f : R →+* S) : StableSteinberg R →* StableSteinberg S :=
  Chain.lift (steinbergStep R) (fun n => (of S n).comp (Steinberg.map f)) (by
    intro n
    apply MonoidHom.ext
    intro g
    have he := DFunLike.congr_fun (Kernel.padSteinberg_map f n) g
    simp only [MonoidHom.comp_apply] at he ⊢
    rw [← he]
    exact Chain.of_step (steinbergStep S) n (Steinberg.map f g))

@[simp] theorem map_of (f : R →+* S) (n : ℕ) (g : Steinberg n R) :
    map f (of R n g) = of S n (Steinberg.map f g) := by
  simp only [map, of, Chain.lift_of, MonoidHom.comp_apply]

/-- Two homomorphisms out of the stable group agree if they agree on every finite stage. -/
theorem hom_ext {G : Type*} [Group G] {φ ψ : StableSteinberg R →* G}
    (h : ∀ n (g : Steinberg n R), φ (of R n g) = ψ (of R n g)) : φ = ψ := by
  apply MonoidHom.ext
  intro z
  obtain ⟨n, g, rfl⟩ := Chain.exists_stage (steinbergStep R) z
  exact h n g

theorem map_comp (f : R →+* S) (g : S →+* T) :
    map (g.comp f) = (map g).comp (map f) := by
  apply hom_ext
  intro n x
  have hx : Steinberg.map (g.comp f) x = Steinberg.map g (Steinberg.map f x) := by
    have hc : Steinberg.map (n := n) (g.comp f) = (Steinberg.map g).comp (Steinberg.map f) := by
      apply Steinberg.hom_ext
      intro p a
      simp only [MonoidHom.comp_apply, Steinberg.map_x, RingHom.comp_apply]
    exact DFunLike.congr_fun hc x
  simp only [MonoidHom.comp_apply, map_of, hx]

/-- The stable kernel of a coefficient homomorphism contains every root with parameter
in the ring-theoretic kernel. -/
theorem map_root_eq_one (f : R →+* S) (n : ℕ) (p : Root n) {a : R} (ha : f a = 0) :
    map f (of R n (Steinberg.x p a)) = 1 := by
  rw [map_of, Steinberg.map_x, ha, Steinberg.x_zero, map_one]

end Stable
end
end AllPrimeGroups
