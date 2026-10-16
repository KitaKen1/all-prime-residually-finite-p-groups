import AllPrimeGroups.GLInduction

/-! The action of `GL_n(B)` on the Steinberg group and centrality of the matrix kernel
(manuscript Lemma 11.2, first part).

Elementary generators act by conjugation with their root, diagonal generators by rescaling the
roots, `x_{jk}(a) ↦ x_{jk}(u_j a u_k⁻¹)`. Both are compatible with the elementary representation.
A word supported on at most five coordinates leaves the incoming and outgoing strips of a sixth
coordinate `t` invariant, and acts on them through its matrix. If the matrix is the identity, the
strips are fixed because they are faithful, and every other root is a commutator through `t`.
Hence the relations of `GLPres.Pres` act trivially. By Lemma 11.1 this is an action of `GL_n(B)`,
in which the image of `z` acts by conjugation with `z`; so the matrix kernel is central. -/

namespace AllPrimeGroups
namespace GLAct

open LocalGL GLPres Matrix

variable {B : Type*} [Ring B] {n : ℕ}

/-! ### Rescaling roots -/

/-- The unit of a diagonal generator at a coordinate. -/
def du (i : Fin n) (u : Bˣ) (j : Fin n) : Bˣ := if j = i then u else 1

theorem du_inv (i : Fin n) (u : Bˣ) (j : Fin n) : du i u⁻¹ j = (du i u j)⁻¹ := by
  unfold du
  split_ifs <;> simp

/-- Rescaling the roots by a diagonal unit. -/
def diagHom (i : Fin n) (u : Bˣ) : Steinberg n B →* Steinberg n B :=
  Steinberg.lift (fun p a => Steinberg.x p ((du i u p.row : B) * a * ((du i u p.col)⁻¹ : Bˣ)))
    (fun p a b => by rw [mul_add, add_mul, Steinberg.x_add])
    (fun p q h₁ h₂ _ _ => Steinberg.x_commute p q h₁ h₂ _ _)
    (fun i' j k hij hjk hik a b => by
      rw [Steinberg.x_mul _ _ _ hij hjk hik]
      congr 1
      simp only [mul_assoc, Units.inv_mul_cancel_left])

theorem diagHom_x (i : Fin n) (u : Bˣ) (p : Root n) (a : B) :
    diagHom i u (Steinberg.x p a) =
      Steinberg.x p ((du i u p.row : B) * a * ((du i u p.col)⁻¹ : Bˣ)) :=
  Steinberg.lift_x _ _ _ _ p a

theorem diagHom_inv_comp (i : Fin n) (u : Bˣ) :
    (diagHom i u⁻¹).comp (diagHom i u) = MonoidHom.id (Steinberg n B) := by
  apply Steinberg.hom_ext
  intro p a
  simp only [MonoidHom.comp_apply, diagHom_x, MonoidHom.id_apply, du_inv, inv_inv]
  congr 1
  simp only [mul_assoc, Units.inv_mul_cancel_left, Units.inv_mul, mul_one]

/-- The automorphism rescaling the roots by a diagonal unit. -/
def diagAut (i : Fin n) (u : Bˣ) : MulAut (Steinberg n B) :=
  MonoidHom.toMulEquiv (diagHom i u) (diagHom i u⁻¹) (diagHom_inv_comp i u) (by
    have := diagHom_inv_comp i u⁻¹
    rwa [inv_inv] at this)

theorem diagAut_apply (i : Fin n) (u : Bˣ) (y : Steinberg n B) : diagAut i u y = diagHom i u y :=
  rfl

theorem diagAut_symm_apply (i : Fin n) (u : Bˣ) (y : Steinberg n B) :
    (diagAut i u)⁻¹ y = diagHom i u⁻¹ y :=
  rfl

theorem d_conj_e (i : Fin n) (u : Bˣ) (p : Root n) (a : B) :
    d i u * Elementary.e p a * (d i u)⁻¹ =
      Elementary.e p ((du i u p.row : B) * a * ((du i u p.col)⁻¹ : Bˣ)) := by
  apply units_ext_mulVec
  intro x
  rw [d_inv, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  simp only [d_mulVec, e_mulVec]
  funext l
  have hrc := p.ne
  by_cases hl : l = p.row
  · subst hl
    by_cases hr : p.row = i
    · subst hr
      simp [du, Ne.symm hrc, mul_add, mul_assoc]
    · by_cases hc : p.col = i
      · subst hc
        simp [du, hr, mul_assoc]
      · simp [du, hr, hc]
  · by_cases hli : l = i
    · subst hli
      simp [hl]
    · simp [hl, hli]

theorem representation_diagHom (i : Fin n) (u : Bˣ) (y : Steinberg n B) :
    Elementary.representation (diagHom i u y) =
      d i u * Elementary.representation y * (d i u)⁻¹ := by
  have h : (Elementary.representation (n := n) (R := B)).comp (diagHom i u) =
      (MulAut.conj (d i u)).toMonoidHom.comp Elementary.representation := by
    apply Steinberg.hom_ext
    intro p a
    simp only [MonoidHom.comp_apply, diagHom_x, Elementary.representation_x,
      MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact (d_conj_e i u p a).symm
  exact DFunLike.congr_fun h y

theorem diagHom_strip (i : Fin n) (u : Bˣ) (H L : Finset (Fin n)) (hHL : Disjoint H L)
    {y : Steinberg n B} (hy : y ∈ Kernel.Strip H L hHL) : diagHom i u y ∈ Kernel.Strip H L hHL := by
  have h : Kernel.Strip (R := B) H L hHL ≤ (Kernel.Strip H L hHL).comap (diagHom i u) := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨q, a, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, diagHom_x]
    exact Subgroup.subset_closure ⟨q, _, rfl⟩
  exact h hy

/-! ### The action of the generators -/

/-- Elementary generators act by conjugation, diagonal generators by rescaling the roots. -/
def act : Gen n B → MulAut (Steinberg n B)
  | .elem p a => MulAut.conj (Steinberg.x p a)
  | .diag i u => diagAut i u

/-- The action of words. -/
def α : FreeGroup (Gen n B) →* MulAut (Steinberg n B) := FreeGroup.lift act

theorem representation_act (g : Gen n B) (y : Steinberg n B) :
    Elementary.representation (act g y) = g.val * Elementary.representation y * g.val⁻¹ := by
  cases g with
  | elem p a =>
    simp only [act, MulAut.conj_apply, map_mul, map_inv, Elementary.representation_x]
    rfl
  | diag i u => exact representation_diagHom i u y

theorem representation_α (w : FreeGroup (Gen n B)) (y : Steinberg n B) :
    Elementary.representation (α w y) = ev w * Elementary.representation y * (ev w)⁻¹ := by
  induction w using FreeGroup.induction_on generalizing y with
  | one => simp
  | of g =>
    show Elementary.representation (α (FreeGroup.of g) y) = ev (FreeGroup.of g) * _ * _
    rw [α, FreeGroup.lift_apply_of, ev_of]
    exact representation_act g y
  | inv_of g _ =>
    show Elementary.representation (α (FreeGroup.of g)⁻¹ y) = ev (FreeGroup.of g)⁻¹ * _ * _
    rw [map_inv, map_inv, α, FreeGroup.lift_apply_of, ev_of]
    have h := representation_act g ((act g)⁻¹ y)
    rw [MulAut.apply_inv_self] at h
    rw [h]
    group
  | mul v w hv hw =>
    rw [map_mul, MulAut.mul_apply, hv, hw, map_mul]
    group

/-! ### Automorphisms preserving the strips -/

/-- Automorphisms mapping a subgroup onto itself. -/
def preserving {G : Type*} [Group G] (S : Subgroup G) : Subgroup (MulAut G) where
  carrier := {φ | S.map φ.toMonoidHom = S}
  one_mem' := by
    show S.map (MonoidHom.id G) = S
    exact Subgroup.map_id S
  mul_mem' := fun {φ ψ} hφ hψ => by
    show S.map (φ.toMonoidHom.comp ψ.toMonoidHom) = S
    rw [← Subgroup.map_map, hψ, hφ]
  inv_mem' := fun {φ} hφ => by
    show S.map φ⁻¹.toMonoidHom = S
    conv_lhs => rw [← hφ]
    rw [Subgroup.map_map]
    have e : φ⁻¹.toMonoidHom.comp φ.toMonoidHom = MonoidHom.id G :=
      MonoidHom.ext fun x => MulAut.inv_apply_self G φ x
    rw [e, Subgroup.map_id]

theorem mem_preserving {G : Type*} [Group G] {S : Subgroup G} {φ : MulAut G}
    (h₁ : ∀ x ∈ S, φ x ∈ S) (h₂ : ∀ x ∈ S, φ⁻¹ x ∈ S) : φ ∈ preserving S := by
  show S.map φ.toMonoidHom = S
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact h₁ x hx
  · intro x hx
    exact ⟨φ⁻¹ x, h₂ x hx, MulAut.apply_inv_self G φ x⟩

theorem apply_mem_of_preserving {G : Type*} [Group G] {S : Subgroup G} {φ : MulAut G}
    (h : φ ∈ preserving S) {x : G} (hx : x ∈ S) : φ x ∈ S := by
  have h' : S.map φ.toMonoidHom = S := h
  rw [← h']
  exact ⟨x, hx, rfl⟩

theorem act_mem (t : Fin n) (g : Gen n B) (ht : t ∉ g.supp) :
    act g ∈ preserving (Kernel.columnStrip (R := B) t) ⊓ preserving (Kernel.rowStrip t) := by
  cases g with
  | elem p a =>
    have hr : p.row ≠ t := fun e => ht (by simp [Gen.supp, e])
    have hc : p.col ≠ t := fun e => ht (by simp [Gen.supp, e])
    have hinv : ∀ y, (act (Gen.elem p a))⁻¹ y =
        Steinberg.x p (-a) * y * (Steinberg.x p (-a))⁻¹ := fun y => by
      show (MulAut.conj (Steinberg.x p a))⁻¹ y = _
      rw [← map_inv, MulAut.conj_apply, Steinberg.x_neg, inv_inv]
    refine ⟨mem_preserving (fun y hy => Kernel.conjugate_column_mem t p hr hc a hy)
      (fun y hy => ?_), mem_preserving (fun y hy => Kernel.conjugate_row_mem t p hr hc a hy)
      (fun y hy => ?_)⟩
    · rw [hinv]
      exact Kernel.conjugate_column_mem t p hr hc (-a) hy
    · rw [hinv]
      exact Kernel.conjugate_row_mem t p hr hc (-a) hy
  | diag i u =>
    exact ⟨mem_preserving (fun y hy => diagHom_strip i u _ _ _ hy)
      (fun y hy => diagHom_strip i u⁻¹ _ _ _ hy),
      mem_preserving (fun y hy => diagHom_strip i u _ _ _ hy)
      (fun y hy => diagHom_strip i u⁻¹ _ _ _ hy)⟩

theorem α_mem (t : Fin n) {T : Finset (Fin n)} (ht : t ∉ T) {w : FreeGroup (Gen n B)}
    (hw : w ∈ supported T) :
    α w ∈ preserving (Kernel.columnStrip (R := B) t) ⊓ preserving (Kernel.rowStrip t) := by
  have h : supported (B := B) T ≤
      (preserving (Kernel.columnStrip (R := B) t) ⊓ preserving (Kernel.rowStrip t)).comap α := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨g, hg, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, α, FreeGroup.lift_apply_of]
    exact act_mem t g (fun h => ht (hg h))
  exact h hw

/-- An automorphism preserving the strips of a coordinate and the elementary representation is
trivial. -/
theorem eq_one_of_strips (t : Fin n) (φ : MulAut (Steinberg n B))
    (hc : φ ∈ preserving (Kernel.columnStrip (R := B) t))
    (hr : φ ∈ preserving (Kernel.rowStrip (R := B) t))
    (hrep : ∀ y, Elementary.representation (φ y) = Elementary.representation y) : φ = 1 := by
  have hcol : ∀ (i : Fin n) (hi : i ≠ t) (a : B),
      φ (Steinberg.x ⟨i, t, hi⟩ a) = Steinberg.x ⟨i, t, hi⟩ a := by
    intro i hi a
    have hx := Kernel.column_root_mem t i hi a
    have h1 := apply_mem_of_preserving hc hx
    have H := Kernel.strip_faithful _ _ _ ((Kernel.columnStrip t).mul_mem h1
      ((Kernel.columnStrip t).inv_mem hx)) (by rw [map_mul, map_inv, hrep, mul_inv_cancel])
    exact mul_inv_eq_one.mp H
  have hrow : ∀ (i : Fin n) (hi : t ≠ i) (a : B),
      φ (Steinberg.x ⟨t, i, hi⟩ a) = Steinberg.x ⟨t, i, hi⟩ a := by
    intro i hi a
    have hx := Kernel.row_root_mem t i hi a
    have h1 := apply_mem_of_preserving hr hx
    have H := Kernel.strip_faithful _ _ _ ((Kernel.rowStrip t).mul_mem h1
      ((Kernel.rowStrip t).inv_mem hx)) (by rw [map_mul, map_inv, hrep, mul_inv_cancel])
    exact mul_inv_eq_one.mp H
  have hx : ∀ (p : Root n) (a : B), φ (Steinberg.x p a) = Steinberg.x p a := by
    intro p a
    by_cases hpr : p.row = t
    · have hp : p = ⟨t, p.col, hpr ▸ p.ne⟩ := by
        cases p
        cases hpr
        rfl
      rw [hp]
      exact hrow _ _ a
    · by_cases hpc : p.col = t
      · have hp : p = ⟨p.row, t, hpc ▸ p.ne⟩ := by
          cases p
          cases hpc
          rfl
        rw [hp]
        exact hcol _ _ a
      · have he := Steinberg.x_mul p.row t p.col hpr (Ne.symm hpc) p.ne a (1 : B)
        rw [mul_one] at he
        rw [← he]
        simp only [bracket, map_mul, map_inv, hcol, hrow]
  have h : φ.toMonoidHom = MonoidHom.id (Steinberg n B) := Steinberg.hom_ext hx
  ext y
  exact DFunLike.congr_fun h y

/-- The relations of the presentation act trivially once a coordinate is spare. -/
theorem α_rels (hn : 6 ≤ n) {w : FreeGroup (Gen n B)} (hw : w ∈ rels) : α w = 1 := by
  obtain ⟨T, hT, hs, he⟩ := hw
  obtain ⟨t, ht⟩ : ∃ t, t ∉ T := by
    by_contra h
    simp only [not_exists, not_not] at h
    have hu : T = Finset.univ := Finset.eq_univ_of_forall h
    rw [hu, Finset.card_univ, Fintype.card_fin] at hT
    omega
  have hm := α_mem t ht hs
  apply eq_one_of_strips t _ hm.1 hm.2
  intro y
  rw [representation_α, he, one_mul, inv_one, mul_one]

/-- The action of the presentation on the Steinberg group. -/
def actPres (hn : 6 ≤ n) : Pres n B →* MulAut (Steinberg n B) :=
  PresentedGroup.toGroup (f := act) (fun _ hr => α_rels hn hr)

theorem actPres_of (hn : 6 ≤ n) (g : Gen n B) : actPres hn (PresentedGroup.of g) = act g :=
  PresentedGroup.toGroup.of _

/-! ### The action of `GL_n(B)` -/

section Local
variable {K : Type*} [Field K] (ε : B →+* K) (hunit : ∀ b : B, ε b ≠ 0 → IsUnit b)

/-- Lemma 11.1 as an isomorphism. -/
noncomputable def presEquiv (n : ℕ) : Pres n B ≃* (Matrix (Fin n) (Fin n) B)ˣ :=
  MulEquiv.ofBijective π ⟨π_injective_all ε hunit n, π_surjective ε hunit⟩

/-- The action of `GL_n(B)` on `St_n(B)` (manuscript Lemma 11.2). -/
noncomputable def actGL (hn : 6 ≤ n) : (Matrix (Fin n) (Fin n) B)ˣ →* MulAut (Steinberg n B) :=
  (actPres hn).comp (presEquiv ε hunit n).symm.toMonoidHom

theorem actGL_e (hn : 6 ≤ n) (p : Root n) (a : B) :
    actGL ε hunit hn (Elementary.e p a) = MulAut.conj (Steinberg.x p a) := by
  have h : (presEquiv ε hunit n).symm (Elementary.e p a) = PresentedGroup.of (Gen.elem p a) := by
    rw [MulEquiv.symm_apply_eq]
    exact (π_of (Gen.elem p a)).symm
  simp only [actGL, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, h, actPres_of]
  rfl

theorem actGL_d (hn : 6 ≤ n) (i : Fin n) (u : Bˣ) : actGL ε hunit hn (d i u) = diagAut i u := by
  have h : (presEquiv ε hunit n).symm (d i u) = PresentedGroup.of (Gen.diag i u) := by
    rw [MulEquiv.symm_apply_eq]
    exact (π_of (Gen.diag i u)).symm
  simp only [actGL, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, h, actPres_of]
  rfl

/-- The matrix of `z` acts by conjugation with `z`. -/
theorem actGL_representation (hn : 6 ≤ n) (z : Steinberg n B) :
    actGL ε hunit hn (Elementary.representation z) = MulAut.conj z := by
  have h : (actGL ε hunit hn).comp Elementary.representation = MulAut.conj := by
    apply Steinberg.hom_ext
    intro p a
    rw [MonoidHom.comp_apply, Elementary.representation_x, actGL_e]
  exact DFunLike.congr_fun h z

include hunit in
/-- Manuscript Lemma 11.2, first part: for `n ≥ 6` the matrix kernel is central. -/
theorem kernel_central (hn : 6 ≤ n) {z : Steinberg n B} (hz : Elementary.representation z = 1) :
    z ∈ Subgroup.center (Steinberg n B) := by
  have h := actGL_representation ε hunit hn z
  rw [hz, map_one] at h
  rw [Subgroup.mem_center_iff]
  intro g
  have hg := DFunLike.congr_fun h g
  rw [MulAut.conj_apply, MulAut.one_apply] at hg
  exact (mul_inv_eq_iff_eq_mul.mp hg.symm).symm

end Local

end GLAct
end AllPrimeGroups
