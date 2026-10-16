import AllPrimeGroups.GLPresentation

/-! Ingredients of the induction step of manuscript Lemma 11.1.

* `shift`: the map `Pres m B → Pres (m + 1) B` induced by the first `m` coordinates; it covers the
  padding of matrices.
* `Col m B`: columns with the action of invertible matrices; invertible matrices preserve the
  independence of reductions, so they act on the column complex.
-/

namespace AllPrimeGroups
namespace GLPres

open LocalGL ColumnComplex Matrix

variable {B : Type*} [Ring B] {m : ℕ}

/-- Generators on the first `m` of `m + 1` coordinates. -/
def Gen.cast : Gen m B → Gen (m + 1) B
  | .elem p a => .elem (p.map (Kernel.coordinateIndex m) (Kernel.coordinateIndex_injective m)) a
  | .diag i u => .diag (Kernel.coordinateIndex m i) u

theorem Gen.cast_val (g : Gen m B) : (Gen.cast g).val = Kernel.padUnitsHom g.val := by
  cases g with
  | elem p a => exact (Kernel.padUnitsHom_e p a).symm
  | diag i u => exact (pad_d i u).symm

theorem ev_comp_map_cast :
    (ev (m := m + 1) (B := B)).comp (FreeGroup.map Gen.cast) = Kernel.padUnitsHom.comp ev := by
  apply FreeGroup.ext_hom
  intro g
  simp only [MonoidHom.comp_apply, FreeGroup.map.of, ev_of, Gen.cast_val]

theorem Gen.supp_cast (g : Gen m B) :
    (Gen.cast g).supp = g.supp.map ⟨Kernel.coordinateIndex m, Kernel.coordinateIndex_injective m⟩ := by
  cases g with
  | elem p a =>
    simp [Gen.cast, Gen.supp, Root.map, Finset.map_insert, Finset.map_singleton]
  | diag i u => simp [Gen.cast, Gen.supp]

theorem map_cast_supported {T : Finset (Fin m)} {w : FreeGroup (Gen m B)} (hw : w ∈ supported T) :
    FreeGroup.map Gen.cast w ∈
      supported (T.map ⟨Kernel.coordinateIndex m, Kernel.coordinateIndex_injective m⟩) := by
  have h : supported (B := B) T ≤ (supported (T.map ⟨Kernel.coordinateIndex m,
      Kernel.coordinateIndex_injective m⟩)).comap (FreeGroup.map Gen.cast) := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨g, hg, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, FreeGroup.map.of]
    apply of_mem_supported
    rw [Gen.supp_cast]
    exact Finset.map_subset_map.mpr hg
  exact h hw

theorem map_cast_rels {w : FreeGroup (Gen m B)} (hw : w ∈ rels) :
    FreeGroup.map Gen.cast w ∈ rels (m := m + 1) (B := B) := by
  obtain ⟨T, hT, hs, he⟩ := hw
  refine ⟨T.map ⟨Kernel.coordinateIndex m, Kernel.coordinateIndex_injective m⟩, by
    rw [Finset.card_map]; exact hT, map_cast_supported hs, ?_⟩
  have := DFunLike.congr_fun (ev_comp_map_cast (B := B) (m := m)) w
  simp only [MonoidHom.comp_apply] at this
  rw [this, he, map_one]

/-- The map on presentations induced by the first `m` coordinates. -/
def shift : Pres m B →* Pres (m + 1) B :=
  PresentedGroup.toGroup (f := fun g => PresentedGroup.of (Gen.cast g)) (fun r hr => by
    have h1 : FreeGroup.lift (fun g => (PresentedGroup.of (Gen.cast g) : Pres (m + 1) B)) =
        (mk (m := m + 1) (B := B)).comp (FreeGroup.map Gen.cast) := by
      apply FreeGroup.ext_hom
      intro g
      simp only [FreeGroup.lift_apply_of, MonoidHom.comp_apply, FreeGroup.map.of]
      rfl
    rw [h1, MonoidHom.comp_apply]
    exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.subset_normalClosure (map_cast_rels hr)))

theorem shift_of (g : Gen m B) : shift (PresentedGroup.of g) = PresentedGroup.of (Gen.cast g) :=
  PresentedGroup.toGroup.of _

theorem π_shift : (π (m := m + 1) (B := B)).comp shift = Kernel.padUnitsHom.comp π := by
  apply PresentedGroup.ext
  intro g
  simp only [MonoidHom.comp_apply, shift_of]
  rw [show (PresentedGroup.of (Gen.cast g) : Pres (m + 1) B) = mk (FreeGroup.of (Gen.cast g)) from rfl,
    show (PresentedGroup.of g : Pres m B) = mk (FreeGroup.of g) from rfl, π_mk, π_mk, ev_of, ev_of,
    Gen.cast_val]

/-- Columns, with the action of invertible matrices. -/
def Col (m : ℕ) (B : Type*) := Fin m → B

instance : MulAction (Matrix (Fin m) (Fin m) B)ˣ (Col m B) where
  smul g v := (g : Matrix (Fin m) (Fin m) B) *ᵥ v
  one_smul v := Matrix.one_mulVec (v : Fin m → B)
  mul_smul g h v := (Matrix.mulVec_mulVec (v : Fin m → B) (g : Matrix (Fin m) (Fin m) B)
    (h : Matrix (Fin m) (Fin m) B)).symm

theorem smul_def (g : (Matrix (Fin m) (Fin m) B)ˣ) (v : Col m B) :
    g • v = ((g : Matrix (Fin m) (Fin m) B) *ᵥ (v : Fin m → B) : Fin m → B) := rfl

section Reduction
variable {K : Type*} [Field K] (ε : B →+* K)

/-- The reduction of a column. -/
def red (v : Col m B) : Fin m → K := fun i => ε (v i)

theorem red_smul (g : (Matrix (Fin m) (Fin m) B)ˣ) (v : Col m B) :
    red ε (g • v) = ((g : Matrix (Fin m) (Fin m) B).map ε) *ᵥ red ε v := by
  funext i
  exact RingHom.map_mulVec ε (g : Matrix (Fin m) (Fin m) B) v i

theorem red_inv_smul_red (g : (Matrix (Fin m) (Fin m) B)ˣ) (x : Fin m → K) :
    ((((g⁻¹ : (Matrix (Fin m) (Fin m) B)ˣ) : Matrix (Fin m) (Fin m) B).map ε) *ᵥ
      (((g : Matrix (Fin m) (Fin m) B).map ε) *ᵥ x)) = x := by
  rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ ε.map_zero ε.map_one,
    Matrix.one_mulVec]

theorem adj_smul (g : (Matrix (Fin m) (Fin m) B)ˣ) (u v : Col m B) (h : Adj (red ε) u v) :
    Adj (red ε) (g • u) (g • v) := by
  intro a b hab
  apply h a b
  rw [red_smul, red_smul, ← Matrix.mulVec_smul, ← Matrix.mulVec_smul, ← Matrix.mulVec_add] at hab
  have := congrArg ((((g⁻¹ : (Matrix (Fin m) (Fin m) B)ˣ) : Matrix (Fin m) (Fin m) B).map ε) *ᵥ ·)
    hab
  simp only [red_inv_smul_red, Matrix.mulVec_zero] at this
  exact this

theorem tri_smul (g : (Matrix (Fin m) (Fin m) B)ˣ) (u v w : Col m B) (h : Tri (red ε) u v w) :
    Tri (red ε) (g • u) (g • v) (g • w) := by
  intro a b c habc
  apply h a b c
  rw [red_smul, red_smul, red_smul, ← Matrix.mulVec_smul, ← Matrix.mulVec_smul,
    ← Matrix.mulVec_smul, ← Matrix.mulVec_add, ← Matrix.mulVec_add] at habc
  have := congrArg ((((g⁻¹ : (Matrix (Fin m) (Fin m) B)ˣ) : Matrix (Fin m) (Fin m) B).map ε) *ᵥ ·)
    habc
  simp only [red_inv_smul_red, Matrix.mulVec_zero] at this
  exact this

theorem red_single (i : Fin m) : red ε (Pi.single i (1 : B) : Col m B) = Pi.single i (1 : K) := by
  funext l
  by_cases hl : l = i
  · subst hl
    simp [red]
  · simp [red, hl]

end Reduction

end GLPres
end AllPrimeGroups
