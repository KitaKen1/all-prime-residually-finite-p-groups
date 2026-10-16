import AllPrimeGroups.K1Stability
import AllPrimeGroups.MatrixGeometry

/-! K1 stability along an arbitrary injection of coordinates.

The common diagonal quotient from `K1Stability` is insensitive to relabelling, so reflection
of elementary membership does not require iterating one-coordinate padding. The matrix
embedding and its entry formulas are reused from the pinned upstream source. -/

namespace AllPrimeGroups
namespace MatrixCoordinates
noncomputable section

open GLPres LocalGL Matrix

variable {B : Type*} [Ring B] {k n : ℕ}

abbrev embed (f : Fin k → Fin n) (hf : Function.Injective f) :=
  AllPrimeGroups.MatrixGeometry.embed (R := B) ⟨f, hf⟩

theorem embed_e (f : Fin k → Fin n) (hf : Function.Injective f) (p : Root k) (a : B) :
    embed f hf (Elementary.e p a) = Elementary.e (p.map f hf) a :=
  AllPrimeGroups.MatrixGeometry.embed_elementary ⟨f, hf⟩ p.row p.col p.ne a

theorem upstream_d (i : Fin k) (u : Bˣ) :
    AllPrimeGroups.MatrixGeometry.singleDiagonal i u = d i u := by
  apply Units.ext
  change Matrix.diagonal (fun j => ((if j = i then u else 1 : Bˣ) : B)) =
    Matrix.diagonal (Function.update (1 : Fin k → B) i (u : B))
  congr 1
  funext j
  by_cases h : j = i
  · subst h
    simp
  · simp [h]

theorem embed_d (f : Fin k → Fin n) (hf : Function.Injective f) (i : Fin k) (u : Bˣ) :
    embed f hf (d i u) = d (f i) u := by
  rw [← upstream_d, embed,
    AllPrimeGroups.MatrixGeometry.embed_singleDiagonal, upstream_d]
  rfl

theorem ev_relabel (f : Fin k → Fin n) (hf : Function.Injective f) :
    ev.comp (GLPres.relabel (B := B) f hf) = (embed f hf).comp ev := by
  apply FreeGroup.ext_hom
  intro g
  simp only [MonoidHom.comp_apply, GLPres.relabel_of, ev_of]
  cases g with
  | elem p a => exact (embed_e f hf p a).symm
  | diag i u => exact (embed_d f hf i u).symm

theorem supported_relabel (f : Fin k → Fin n) (hf : Function.Injective f) (T : Finset (Fin k)) :
    supported (B := B) T ≤ (supported (T.map ⟨f, hf⟩)).comap (GLPres.relabel f hf) := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨g, hg, rfl⟩
  change GLPres.relabel f hf (FreeGroup.of g) ∈ supported (T.map ⟨f, hf⟩)
  rw [GLPres.relabel_of]
  apply of_mem_supported
  rw [Gen.supp_relabel]
  exact Finset.map_subset_map.mpr hg

def presMap (f : Fin k → Fin n) (hf : Function.Injective f) : Pres k B →* Pres n B :=
  PresentedGroup.map (GLPres.relabel f hf) (by
    rintro w ⟨T, hT, hw, he⟩
    refine ⟨T.map ⟨f, hf⟩, by simpa using hT, supported_relabel f hf T hw, ?_⟩
    rw [← MonoidHom.comp_apply, ev_relabel, MonoidHom.comp_apply, he, map_one])

theorem presMap_of (f : Fin k → Fin n) (hf : Function.Injective f) (g : Gen k B) :
    presMap f hf (PresentedGroup.of g) = PresentedGroup.of (g.relabel f hf) := by
  change mk (GLPres.relabel f hf (FreeGroup.of g)) = _
  rw [GLPres.relabel_of]
  rfl

theorem π_presMap (f : Fin k → Fin n) (hf : Function.Injective f) :
    π.comp (presMap (B := B) f hf) = (embed f hf).comp π := by
  apply PresentedGroup.ext
  intro g
  simp only [MonoidHom.comp_apply, presMap_of, GLPres.π_of]
  cases g with
  | elem p a => exact (embed_e f hf p a).symm
  | diag i u => exact (embed_d f hf i u).symm

theorem D_presMap (f : Fin k → Fin n) (hf : Function.Injective f) (hk : 5 ≤ k) (hn : 5 ≤ n) :
    (K1.D hn).comp (presMap (B := B) f hf) = K1.D hk := by
  apply PresentedGroup.ext
  intro g
  simp only [MonoidHom.comp_apply, presMap_of, K1.D_of]
  cases g <;> rfl

theorem representation_coordinateMap (f : Fin k → Fin n) (hf : Function.Injective f) :
    Elementary.representation.comp (Steinberg.coordinateMap (R := B) f hf) =
      (embed f hf).comp Elementary.representation := by
  apply Steinberg.hom_ext
  intro p a
  simp only [MonoidHom.comp_apply, Steinberg.coordinateMap_x, Elementary.representation_x]
  exact (embed_e f hf p a).symm

theorem embed_mem_E (f : Fin k → Fin n) (hf : Function.Injective f)
    {A : (Matrix (Fin k) (Fin k) B)ˣ} (hA : A ∈ K1.E k B) : embed f hf A ∈ K1.E n B := by
  obtain ⟨z, rfl⟩ := hA
  exact ⟨Steinberg.coordinateMap f hf z,
    DFunLike.congr_fun (representation_coordinateMap f hf) z⟩

section Local
variable {K : Type*} [Field K] (ε : B →+* K) (hunit : ∀ b : B, ε b ≠ 0 → IsUnit b)

include hunit in
/-- Elementary membership is reflected by every coordinate embedding once the source rank
is at least five. No Steinberg injectivity is assumed. -/
theorem mem_E_of_embed (f : Fin k → Fin n) (hf : Function.Injective f) (hk : 5 ≤ k)
    {A : (Matrix (Fin k) (Fin k) B)ˣ} (hA : embed f hf A ∈ K1.E n B) : A ∈ K1.E k B := by
  have hkn : k ≤ n := by simpa using Fintype.card_le_of_injective f hf
  have hn : 5 ≤ n := hk.trans hkn
  obtain ⟨x, rfl⟩ := π_surjective ε hunit A
  have hx : π (presMap f hf x) ∈ K1.E n B := by
    rw [← MonoidHom.comp_apply, π_presMap, MonoidHom.comp_apply]
    exact hA
  rw [← K1.map_N ε hunit] at hx
  obtain ⟨y, hy, hxy⟩ := hx
  have hy' : y = presMap f hf x := π_injective_all ε hunit _ hxy
  have hy2 : presMap f hf x ∈ K1.N n B := hy' ▸ hy
  rw [K1.mem_N_iff hn] at hy2
  have hxD : K1.D hk x = 1 := by
    rw [← DFunLike.congr_fun (D_presMap f hf hk hn) x]
    exact hy2
  rw [← K1.map_N ε hunit]
  exact ⟨x, (K1.mem_N_iff hk x).mpr hxD, rfl⟩

end Local
end
end MatrixCoordinates
end AllPrimeGroups
