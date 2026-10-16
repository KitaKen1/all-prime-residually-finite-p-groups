import AllPrimeGroups.GLAction
import AllPrimeGroups.GLRelabel
import Mathlib.Algebra.Group.Subgroup.Pointwise

/-! Stability of `GL_n(B)/E_n(B)` (manuscript Lemma 11.2, second part).

Killing the elementary generators in the presentation of Lemma 11.1 leaves the diagonal
generators, whose positions are identified by the elementary signed interchange, subject to the
true relations on at most five coordinates with the elementary letters deleted. Relabelling
coordinates along an injection from `Fin 5` shows that this list does not depend on `n ≥ 5`. So
one group `Q` receives every `Pres n B` (`D`), its kernel is the normal closure of the elementary
generators (`mem_N_iff`), and `D` is compatible with adding a coordinate. Through Lemma 11.1 this
gives the stability of `GL_n(B)/E_n(B)`: a matrix whose padding is elementary is elementary
(`mem_E_of_pad`), and every matrix is elementary up to a diagonal unit in a given position
(`exists_mul_d_mem_E`). -/

namespace AllPrimeGroups
namespace K1

open LocalGL GLPres Matrix

variable {B : Type*} [Ring B] {n : ℕ}

/-! ### Deleting elementary letters -/

/-- The letter of a generator once elementary generators are deleted and diagonal positions are
forgotten. -/
def letter : Gen n B → FreeGroup Bˣ
  | .elem _ _ => 1
  | .diag _ u => FreeGroup.of u

/-- Deleting elementary letters. -/
def δ : FreeGroup (Gen n B) →* FreeGroup Bˣ := FreeGroup.lift letter

@[simp] theorem δ_of (g : Gen n B) : δ (FreeGroup.of g) = letter g := FreeGroup.lift_apply_of

theorem δ_relabel {k : ℕ} {f : Fin k → Fin n} (hf : Function.Injective f)
    (w : FreeGroup (Gen k B)) : δ (relabel f hf w) = δ w := by
  have h : (δ (n := n) (B := B)).comp (relabel f hf) = δ := by
    apply FreeGroup.ext_hom
    intro g
    cases g <;> simp [relabel_of, Gen.relabel, letter]
  exact DFunLike.congr_fun h w

/-- The relations of `GL/E` on five coordinates. -/
def relsQ : Set (FreeGroup Bˣ) := {r | ∃ w : FreeGroup (Gen 5 B), ev w = 1 ∧ δ w = r}

/-- The common quotient of `GL_n(B)` by its elementary subgroup, for `n ≥ 5`. -/
abbrev Q (B : Type*) [Ring B] := PresentedGroup (relsQ (B := B))

/-- The class in the common quotient. -/
def D (hn : 5 ≤ n) : Pres n B →* Q B :=
  PresentedGroup.toGroup (f := fun g => PresentedGroup.mk relsQ (letter g)) (fun r hr => by
    have e : FreeGroup.lift (fun g : Gen n B => (PresentedGroup.mk relsQ (letter g) : Q B)) =
        (PresentedGroup.mk relsQ).comp δ := by
      apply FreeGroup.ext_hom
      intro g
      simp
    rw [e, MonoidHom.comp_apply]
    obtain ⟨T, hT, hs, he⟩ := hr
    obtain ⟨f, hf, hTf⟩ := exists_embedding_five hT hn
    obtain ⟨w', rfl⟩ := exists_relabel hf (supported_mono hTf hs)
    rw [δ_relabel]
    exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.subset_normalClosure
      ⟨w', (ev_relabel_eq_one_iff hf w').mp he, rfl⟩))

theorem D_of (hn : 5 ≤ n) (g : Gen n B) :
    D hn (PresentedGroup.of g) = PresentedGroup.mk relsQ (letter g) :=
  PresentedGroup.toGroup.of _

theorem D_shift (hn : 5 ≤ n) (x : Pres n B) : D (n := n + 1) (by omega) (shift x) = D hn x := by
  have h : (D (n := n + 1) (by omega)).comp (shift (m := n) (B := B)) = D hn := by
    apply PresentedGroup.ext
    intro g
    cases g <;> simp only [MonoidHom.comp_apply, shift_of, D_of, Gen.cast, letter]
  exact DFunLike.congr_fun h x

/-! ### The elementary signed interchange -/

/-- The elementary signed interchange of two coordinates. -/
def sgnWord (i j : Fin n) (h : i ≠ j) : FreeGroup (Gen n B) :=
  FreeGroup.of (Gen.elem ⟨i, j, h⟩ 1) * FreeGroup.of (Gen.elem ⟨j, i, h.symm⟩ (-1)) *
    FreeGroup.of (Gen.elem ⟨i, j, h⟩ 1)

theorem sgnWord_mulVec (i j : Fin n) (h : i ≠ j) (x : Fin n → B) :
    ((ev (sgnWord (B := B) i j h) : (Matrix (Fin n) (Fin n) B)ˣ) : Matrix (Fin n) (Fin n) B) *ᵥ x =
      fun l => if l = i then x j else if l = j then -x i else x l := by
  simp only [sgnWord, map_mul, ev_of, Gen.val, Units.val_mul, ← Matrix.mulVec_mulVec, e_mulVec]
  funext l
  by_cases hli : l = i
  · simp only [hli, ↓reduceIte, h, Ne.symm h, one_mul, neg_one_mul]
    abel
  · by_cases hlj : l = j
    · simp only [hlj, ↓reduceIte, Ne.symm h, one_mul, neg_one_mul]
      abel
    · simp only [hli, hlj, ↓reduceIte]

theorem sgn_d (i j : Fin n) (h : i ≠ j) (u : Bˣ) :
    ev (sgnWord (B := B) i j h) * d i u = d j u * ev (sgnWord i j h) := by
  apply units_ext_mulVec
  intro x
  rw [Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, sgnWord_mulVec,
    sgnWord_mulVec, d_mulVec, d_mulVec]
  funext l
  by_cases hli : l = i
  · simp [hli, h, Ne.symm h]
  · by_cases hlj : l = j
    · simp [hlj, Ne.symm h]
    · simp [hli, hlj]

theorem sgnWord_mem (i j : Fin n) (h : i ≠ j) : sgnWord (B := B) i j h ∈ supported {i, j} := by
  unfold sgnWord
  refine Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ ?_) ?_ <;>
    exact of_mem_supported (by simp [Gen.supp, Finset.insert_subset_iff])

theorem sgn_diag (i j : Fin n) (h : i ≠ j) (u : Bˣ) :
    mk (sgnWord (B := B) i j h) * PresentedGroup.of (Gen.diag i u) =
      PresentedGroup.of (Gen.diag j u) * mk (sgnWord i j h) := by
  rw [show (PresentedGroup.of (Gen.diag i u) : Pres n B) = mk (FreeGroup.of (Gen.diag i u)) from rfl,
    show (PresentedGroup.of (Gen.diag j u) : Pres n B) = mk (FreeGroup.of (Gen.diag j u)) from rfl,
    ← map_mul, ← map_mul]
  apply mk_eq_of_ev_eq (T := {i, j}) (Finset.card_le_two.trans (by norm_num))
  · exact Subgroup.mul_mem _ (sgnWord_mem i j h) (of_mem_supported (by simp [Gen.supp]))
  · exact Subgroup.mul_mem _ (of_mem_supported (by simp [Gen.supp])) (sgnWord_mem i j h)
  · rw [map_mul, map_mul, ev_of, ev_of]
    exact sgn_d i j h u

/-! ### The normal closure of the elementary generators -/

/-- The normal subgroup generated by the elementary generators. -/
def N (n : ℕ) (B : Type*) [Ring B] : Subgroup (Pres n B) :=
  Subgroup.normalClosure {x | ∃ (p : Root n) (a : B), PresentedGroup.of (Gen.elem p a) = x}

instance N_normal : (N n B).Normal := Subgroup.normalClosure_normal

theorem elem_mem_N (p : Root n) (a : B) : PresentedGroup.of (Gen.elem p a) ∈ N n B :=
  Subgroup.subset_normalClosure ⟨p, a, rfl⟩

theorem sgnWord_mem_N (i j : Fin n) (h : i ≠ j) : mk (sgnWord (B := B) i j h) ∈ N n B := by
  simp only [sgnWord, map_mul]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (elem_mem_N _ _) (elem_mem_N _ _)) (elem_mem_N _ _)

/-- All diagonal positions have the same class. -/
theorem diag_class (i j : Fin n) (u : Bˣ) :
    (QuotientGroup.mk (PresentedGroup.of (Gen.diag i u)) : Pres n B ⧸ N n B) =
      QuotientGroup.mk (PresentedGroup.of (Gen.diag j u)) := by
  by_cases h : i = j
  · rw [h]
  · rw [QuotientGroup.eq]
    have e : (PresentedGroup.of (Gen.diag j u) : Pres n B) =
        mk (sgnWord i j h) * PresentedGroup.of (Gen.diag i u) * (mk (sgnWord i j h))⁻¹ := by
      rw [sgn_diag, mul_inv_cancel_right]
    rw [e]
    have hS := sgnWord_mem_N (B := B) i j h
    have := Subgroup.mul_mem _ ((N_normal (n := n) (B := B)).conj_mem _ hS
      (PresentedGroup.of (Gen.diag i u))⁻¹) (Subgroup.inv_mem _ hS)
    simpa only [inv_inv, mul_assoc] using this

/-- The inverse of `D` on the quotient, through a fixed diagonal position. -/
def Dinv (i₀ : Fin n) (hn : 5 ≤ n) : Q B →* Pres n B ⧸ N n B :=
  PresentedGroup.toGroup
    (f := fun u => (QuotientGroup.mk (PresentedGroup.of (Gen.diag i₀ u)) : Pres n B ⧸ N n B))
    (fun r hr => by
      obtain ⟨w, hw, rfl⟩ := hr
      have hf : Function.Injective (Fin.castLE hn) := Fin.castLE_injective hn
      have e : (FreeGroup.lift (fun u => (QuotientGroup.mk (PresentedGroup.of (Gen.diag i₀ u)) :
          Pres n B ⧸ N n B))).comp δ = (QuotientGroup.mk' (N n B)).comp
            ((mk (m := n) (B := B)).comp (relabel (Fin.castLE hn) hf)) := by
        apply FreeGroup.ext_hom
        intro g
        cases g with
        | elem p a =>
          rw [MonoidHom.comp_apply, δ_of, letter, map_one, MonoidHom.comp_apply,
            MonoidHom.comp_apply, relabel_of, QuotientGroup.mk'_apply]
          exact ((QuotientGroup.eq_one_iff _).mpr (elem_mem_N _ a)).symm
        | diag i u =>
          rw [MonoidHom.comp_apply, δ_of, letter, FreeGroup.lift_apply_of, MonoidHom.comp_apply,
            MonoidHom.comp_apply, relabel_of, QuotientGroup.mk'_apply]
          exact diag_class i₀ _ u
      have h1 := DFunLike.congr_fun e w
      simp only [MonoidHom.comp_apply] at h1
      rw [h1]
      have hrel : relabel (Fin.castLE hn) hf w ∈ rels (m := n) (B := B) := by
        refine ⟨_, ?_, relabel_supported hf w, (ev_relabel_eq_one_iff hf w).mpr hw⟩
        rw [Finset.card_map, Finset.card_univ, Fintype.card_fin]
      rw [show mk (relabel (Fin.castLE hn) hf w) = 1 from
        (QuotientGroup.eq_one_iff _).mpr (Subgroup.subset_normalClosure hrel), map_one])

theorem Dinv_D (i₀ : Fin n) (hn : 5 ≤ n) :
    (Dinv i₀ hn).comp (D hn) = QuotientGroup.mk' (N n B) := by
  apply PresentedGroup.ext
  intro g
  cases g with
  | elem p a =>
    rw [MonoidHom.comp_apply, D_of, letter, map_one, map_one, QuotientGroup.mk'_apply]
    exact ((QuotientGroup.eq_one_iff _).mpr (elem_mem_N p a)).symm
  | diag i u =>
    rw [MonoidHom.comp_apply, D_of, letter, QuotientGroup.mk'_apply]
    exact (PresentedGroup.toGroup.of _).trans (diag_class i₀ i u)

/-- The kernel of `D` is the normal closure of the elementary generators. -/
theorem mem_N_iff (hn : 5 ≤ n) (x : Pres n B) : x ∈ N n B ↔ D hn x = 1 := by
  constructor
  · intro hx
    have h : N n B ≤ (D hn).ker := by
      apply Subgroup.normalClosure_le_normal
      rintro _ ⟨p, a, rfl⟩
      rw [SetLike.mem_coe, MonoidHom.mem_ker, D_of, letter, map_one]
    exact h hx
  · intro hx
    have h := DFunLike.congr_fun (Dinv_D ⟨0, by omega⟩ hn) x
    rw [MonoidHom.comp_apply, hx, map_one, QuotientGroup.mk'_apply, eq_comm,
      QuotientGroup.eq_one_iff] at h
    exact h

/-! ### The elementary subgroup -/

/-- The elementary subgroup: the matrix image of the Steinberg group. -/
def E (n : ℕ) (B : Type*) [Ring B] : Subgroup (Matrix (Fin n) (Fin n) B)ˣ :=
  (Elementary.representation (n := n) (R := B)).range

theorem e_mem_E (p : Root n) (a : B) : Elementary.e p a ∈ E n B :=
  ⟨Steinberg.x p a, Elementary.representation_x p a⟩

theorem ev_sgnWord_mem_E (i j : Fin n) (h : i ≠ j) : ev (sgnWord (B := B) i j h) ∈ E n B := by
  simp only [sgnWord, map_mul, ev_of]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (e_mem_E _ _) (e_mem_E _ _)) (e_mem_E _ _)

theorem d_conj_mem_E (i : Fin n) (u : Bˣ) {y : (Matrix (Fin n) (Fin n) B)ˣ} (hy : y ∈ E n B) :
    d i u * y * (d i u)⁻¹ ∈ E n B := by
  obtain ⟨z, rfl⟩ := hy
  exact ⟨GLAct.diagHom i u z, GLAct.representation_diagHom i u z⟩

/-- Diagonal units in one position. -/
def dHom (i : Fin n) : Bˣ →* (Matrix (Fin n) (Fin n) B)ˣ where
  toFun u := d i u
  map_one' := by
    apply units_ext_mulVec
    intro x
    rw [d_mulVec]
    funext l
    by_cases hl : l = i <;> simp [hl]
  map_mul' u v := by
    apply units_ext_mulVec
    intro x
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, d_mulVec, d_mulVec, d_mulVec]
    funext l
    by_cases hl : l = i <;> simp [hl, mul_assoc]

section Local
variable {K : Type*} [Field K] (ε : B →+* K) (hunit : ∀ b : B, ε b ≠ 0 → IsUnit b)

include hunit in
/-- The elementary subgroup is normal. -/
theorem E_normal : (E n B).Normal := by
  have h : GE n B ≤ Subgroup.normalizer (E n B : Set (Matrix (Fin n) (Fin n) B)ˣ) := by
    apply (Subgroup.closure_le _).mpr
    rintro _ (⟨p, a, rfl⟩ | ⟨i, u, rfl⟩)
    · exact Subgroup.le_normalizer (e_mem_E p a)
    · rw [SetLike.mem_coe, Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · exact d_conj_mem_E i u
      · intro hy
        have h1 := d_conj_mem_E i u⁻¹ hy
        have e : (d i u)⁻¹ * (d i u * y * (d i u)⁻¹) * (d i u)⁻¹⁻¹ = y := by group
        rwa [← d_inv, e] at h1
  constructor
  intro y hy g
  exact (Subgroup.mem_normalizer_iff.mp (h (mem_GE ε hunit n g)) y).mp hy

include hunit in
/-- The image of the normal closure of the elementary generators is the elementary subgroup. -/
theorem map_N : (N n B).map π = E n B := by
  have := E_normal ε hunit (n := n) (B := B)
  rw [N, Subgroup.map_normalClosure _ _ (π_surjective ε hunit)]
  have hS : π '' {x : Pres n B | ∃ (p : Root n) (a : B), PresentedGroup.of (Gen.elem p a) = x} =
      {g | ∃ (p : Root n) (a : B), Elementary.e p a = g} := by
    ext g
    constructor
    · rintro ⟨_, ⟨p, a, rfl⟩, rfl⟩
      exact ⟨p, a, (π_of (Gen.elem p a)).symm⟩
    · rintro ⟨p, a, rfl⟩
      exact ⟨_, ⟨p, a, rfl⟩, π_of (Gen.elem p a)⟩
  rw [hS]
  apply le_antisymm
  · apply Subgroup.normalClosure_le_normal
    rintro _ ⟨p, a, rfl⟩
    exact e_mem_E p a
  · have h : (Elementary.representation (n := n) (R := B)).range ≤
        Subgroup.normalClosure {g | ∃ (p : Root n) (a : B), Elementary.e p a = g} := by
      rw [MonoidHom.range_eq_map, ← Steinberg.closure_range_x, MonoidHom.map_closure,
        Subgroup.closure_le]
      rintro _ ⟨_, ⟨⟨p, a⟩, rfl⟩, rfl⟩
      exact Subgroup.subset_normalClosure ⟨p, a, (Elementary.representation_x p a).symm⟩
    exact h

include hunit in
/-- Manuscript Lemma 11.2, second part: a matrix whose padding is elementary is elementary. -/
theorem mem_E_of_pad (hn : 5 ≤ n) {A : (Matrix (Fin n) (Fin n) B)ˣ}
    (h : Kernel.padUnitsHom A ∈ E (n + 1) B) : A ∈ E n B := by
  obtain ⟨x, rfl⟩ := π_surjective ε hunit A
  have h1 : π (shift x) ∈ E (n + 1) B := by
    rw [← MonoidHom.comp_apply π shift, π_shift, MonoidHom.comp_apply]
    exact h
  rw [← map_N ε hunit] at h1
  obtain ⟨y, hy, hxy⟩ := h1
  have hy' : y = shift x := π_injective_all ε hunit _ hxy
  have hy2 : shift x ∈ N (n + 1) B := hy' ▸ hy
  rw [mem_N_iff (n := n + 1) (by omega), D_shift hn, ← mem_N_iff hn] at hy2
  rw [← map_N ε hunit]
  exact ⟨x, hy2, rfl⟩

include hunit in
theorem d_mul_inv_mem_E (i j : Fin n) (u : Bˣ) : d i u * (d j u)⁻¹ ∈ E n B := by
  have := E_normal ε hunit (n := n) (B := B)
  by_cases h : j = i
  · rw [h, mul_inv_cancel]
    exact Subgroup.one_mem _
  · have hW := sgn_d (B := B) j i h u
    have e : d i u * (d j u)⁻¹ = ev (sgnWord (B := B) j i h) *
        (d j u * (ev (sgnWord (B := B) j i h))⁻¹ * (d j u)⁻¹) := by
      rw [show d i u = ev (sgnWord (B := B) j i h) * d j u * (ev (sgnWord (B := B) j i h))⁻¹ by
        rw [hW, mul_inv_cancel_right]]
      group
    rw [e]
    exact Subgroup.mul_mem _ (ev_sgnWord_mem_E j i h)
      (Subgroup.Normal.conj_mem inferInstance _ (Subgroup.inv_mem _ (ev_sgnWord_mem_E j i h)) _)

include hunit in
/-- Every invertible matrix is elementary up to a diagonal unit in a given position. -/
theorem exists_mul_d_mem_E (i₀ : Fin n) (M : (Matrix (Fin n) (Fin n) B)ˣ) :
    ∃ u : Bˣ, M * d i₀ u ∈ E n B := by
  have := E_normal ε hunit (n := n) (B := B)
  have h : GE n B ≤ E n B ⊔ (dHom (B := B) i₀).range := by
    apply (Subgroup.closure_le _).mpr
    rintro _ (⟨p, a, rfl⟩ | ⟨i, u, rfl⟩)
    · exact le_sup_left (a := E n B) (e_mem_E p a)
    · have e : d i u = (d i u * (d i₀ u)⁻¹) * d i₀ u := by group
      rw [SetLike.mem_coe, e]
      exact Subgroup.mul_mem _ (le_sup_left (a := E n B) (d_mul_inv_mem_E ε hunit i i₀ u))
        (le_sup_right (b := (dHom (B := B) i₀).range) ⟨u, rfl⟩)
  have hM := h (mem_GE ε hunit n M)
  rw [← SetLike.mem_coe, Subgroup.normal_mul] at hM
  obtain ⟨y, hy, z, ⟨v, rfl⟩, hyz⟩ := hM
  refine ⟨v⁻¹, ?_⟩
  have e : (dHom (B := B) i₀ v) * d i₀ v⁻¹ = 1 := by
    show dHom (B := B) i₀ v * dHom i₀ v⁻¹ = 1
    rw [← map_mul, mul_inv_cancel, map_one]
  rw [← hyz, mul_assoc, e, mul_one]
  exact hy

end Local

end K1
end AllPrimeGroups
