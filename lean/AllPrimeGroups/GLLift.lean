import AllPrimeGroups.GLSection

/-! The lift of the last row strip to the presentation (manuscript Lemma 11.1, "the strip and its
conjugation laws involve at most three coordinates and also lift").

`rowLift r` is the product of the generators `x_{last, b}(r_b)` in `Pres (m + 1) B`. It is a
homomorphism from rows because the generators of the strip commute and add by relations on at
most three coordinates, and it maps to the row strip of matrices. -/

namespace AllPrimeGroups
namespace GLPres

open LocalGL Matrix

variable {B : Type*} [Ring B] {m : ℕ}

/-- The root in the last row and column `b`. -/
def rowRoot (b : Fin m) : Root (m + 1) :=
  ⟨Fin.last m, b.castSucc, (castSucc_ne_last' b).symm⟩

@[simp] theorem last_ne_castSucc' (b : Fin m) : Fin.last m ≠ b.castSucc :=
  (castSucc_ne_last' b).symm
@[simp] theorem coordinateEquiv_inl (i : Fin m) :
    Kernel.coordinateEquiv m (Sum.inl i) = i.castSucc := rfl
@[simp] theorem rowRoot_row (b : Fin m) : (rowRoot b).row = Fin.last m := rfl
@[simp] theorem rowRoot_col (b : Fin m) : (rowRoot b).col = b.castSucc := rfl
@[simp] theorem castRoot_row (p : Root m) :
    (p.map (Kernel.coordinateIndex m) (Kernel.coordinateIndex_injective m)).row = p.row.castSucc :=
  rfl
@[simp] theorem castRoot_col (p : Root m) :
    (p.map (Kernel.coordinateIndex m) (Kernel.coordinateIndex_injective m)).col = p.col.castSucc :=
  rfl

/-- A generator word on two coordinates is supported on them. -/
theorem elem_supported (p : Root m) (a : B) :
    FreeGroup.of (Gen.elem p a) ∈ supported (B := B) {p.row, p.col} :=
  of_mem_supported (by simp [Gen.supp])

/-- The generator of the strip in column `b`. -/
def rowGen (b : Fin m) (a : B) : Pres (m + 1) B := PresentedGroup.of (Gen.elem (rowRoot b) a)

theorem rowGen_eq_mk (b : Fin m) (a : B) :
    rowGen b a = mk (FreeGroup.of (Gen.elem (rowRoot b) a)) := rfl

theorem rowGen_add (b : Fin m) (a a' : B) : rowGen b (a + a') = rowGen b a * rowGen b a' := by
  rw [rowGen_eq_mk, rowGen_eq_mk, rowGen_eq_mk, ← map_mul]
  apply mk_eq_of_ev_eq (T := {(rowRoot b).row, (rowRoot b).col})
    (le_trans (Finset.card_le_two) (by norm_num)) (elem_supported _ _)
    (Subgroup.mul_mem _ (elem_supported _ _) (elem_supported _ _))
  simp [ev_of, Gen.val, Elementary.e_add]

theorem rowGen_zero (b : Fin m) : rowGen b (0 : B) = 1 := by
  have h := rowGen_add b (0 : B) 0
  rw [add_zero] at h
  exact left_eq_mul.mp h

theorem rowGen_commute (b b' : Fin m) (a a' : B) : Commute (rowGen b a) (rowGen b' a') := by
  by_cases hbb : b = b'
  · subst hbb
    show rowGen b a * rowGen b a' = rowGen b a' * rowGen b a
    rw [← rowGen_add, ← rowGen_add, add_comm a a']
  · show rowGen b a * rowGen b' a' = rowGen b' a' * rowGen b a
    rw [rowGen_eq_mk, rowGen_eq_mk, ← map_mul, ← map_mul]
    apply mk_eq_of_ev_eq (T := {Fin.last m, b.castSucc, b'.castSucc})
      (le_trans Finset.card_le_three (by norm_num))
    · apply Subgroup.mul_mem
      · exact supported_mono (by simp [rowRoot, Finset.insert_subset_iff]) (elem_supported _ _)
      · exact supported_mono (by simp [rowRoot, Finset.insert_subset_iff]) (elem_supported _ _)
    · apply Subgroup.mul_mem
      · exact supported_mono (by simp [rowRoot, Finset.insert_subset_iff]) (elem_supported _ _)
      · exact supported_mono (by simp [rowRoot, Finset.insert_subset_iff]) (elem_supported _ _)
    · simp only [map_mul, ev_of, Gen.val]
      exact Elementary.e_commute _ _ (by simp [rowRoot]) (by simp [rowRoot, Ne.symm (castSucc_ne_last' b')])
        _ _

/-- A product over a list distributes when the factors commute across. -/
theorem list_prod_map_mul {G ι : Type*} [Monoid G] (f g : ι → G) :
    ∀ (L : List ι), (∀ i ∈ L, ∀ j ∈ L, Commute (g i) (f j)) →
      (L.map fun i => f i * g i).prod = (L.map f).prod * (L.map g).prod
  | [], _ => by simp
  | i :: L, h => by
    simp only [List.map_cons, List.prod_cons]
    rw [list_prod_map_mul f g L (fun a ha b hb => h a (List.mem_cons_of_mem i ha) b
      (List.mem_cons_of_mem i hb))]
    have hc : Commute (g i) (L.map f).prod := by
      apply Commute.list_prod_right
      intro x hx
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
      exact h i (List.mem_cons_self) j (List.mem_cons_of_mem i hj)
    rw [mul_assoc, ← mul_assoc (g i), hc.eq, mul_assoc, mul_assoc]

/-- The lift of the row strip. -/
def rowLiftFun (r : Fin m → B) : Pres (m + 1) B :=
  ((List.finRange m).map fun b => rowGen b (r b)).prod

/-- The lift of the row strip as a homomorphism. -/
def rowLift : Row m B →* Pres (m + 1) B where
  toFun r := rowLiftFun (Multiplicative.toAdd r)
  map_one' := by
    simp only [toAdd_one, rowLiftFun, Pi.zero_apply, rowGen_zero]
    exact List.prod_eq_one fun x hx => by
      obtain ⟨b, -, rfl⟩ := List.mem_map.mp hx
      rfl
  map_mul' r r' := by
    simp only [toAdd_mul, rowLiftFun, Pi.add_apply, rowGen_add]
    exact list_prod_map_mul (fun b => rowGen b (Multiplicative.toAdd r b))
      (fun b => rowGen b (Multiplicative.toAdd r' b)) _
      (fun i _ j _ => rowGen_commute _ _ _ _)

theorem π_rowLift (r : Row m B) : π (rowLift r) = rowMatHom r := by
  show π (rowLiftFun (Multiplicative.toAdd r)) = rowMat (Multiplicative.toAdd r)
  rw [rowLiftFun, map_list_prod, List.map_map, rowMat, rowProd]
  congr 1
  apply List.map_congr_left
  intro b _
  simp only [Function.comp_apply, rowGen, rowFactor]
  rw [show (PresentedGroup.of (Gen.elem (rowRoot b) (Multiplicative.toAdd r b)) : Pres (m + 1) B) =
    mk (FreeGroup.of (Gen.elem (rowRoot b) (Multiplicative.toAdd r b))) from rfl, π_mk, ev_of]
  rfl

theorem list_prod_single {G : Type*} [Monoid G] (f : Fin m → G) (b : Fin m) :
    ∀ (L : List (Fin m)), L.Nodup →
      (L.map fun b' => if b' = b then f b else 1).prod = if b ∈ L then f b else 1
  | [], _ => by simp
  | c :: L, hL => by
    have hL' := List.nodup_cons.mp hL
    simp only [List.map_cons, List.prod_cons, list_prod_single f b L hL'.2, List.mem_cons]
    by_cases hcb : c = b
    · subst hcb
      simp [hL'.1]
    · simp [hcb, Ne.symm hcb]

theorem rowLift_single (b : Fin m) (a : B) :
    rowLift (Multiplicative.ofAdd (Pi.single b a)) = rowGen b a := by
  show rowLiftFun (Multiplicative.toAdd (Multiplicative.ofAdd (Pi.single b a))) = rowGen b a
  rw [toAdd_ofAdd, rowLiftFun]
  have e : (fun b' => rowGen b' ((Pi.single b a : Fin m → B) b')) =
      fun b' => if b' = b then rowGen b a else 1 := by
    funext b'
    by_cases h : b' = b
    · subst h
      simp
    · simp [h, rowGen_zero]
  rw [e, list_prod_single (fun _ => rowGen b a) b _ (List.nodup_finRange m)]
  simp

theorem d_inv (i : Fin m) (u : Bˣ) : (d i u)⁻¹ = d i u⁻¹ := by
  apply Units.ext
  rfl

/-- Two homomorphisms from rows agreeing on single entries are equal. -/
theorem row_hom_ext {G : Type*} [Monoid G] {f g : Row m B →* G}
    (h : ∀ b a, f (Multiplicative.ofAdd (Pi.single b a)) = g (Multiplicative.ofAdd (Pi.single b a))) :
    f = g := by
  have hr : ∀ r : Row m B, r =
      ((List.finRange m).map fun b => Multiplicative.ofAdd (Pi.single b (Multiplicative.toAdd r b))).prod := by
    intro r
    apply Multiplicative.toAdd.injective
    rw [toAdd_list_sum, List.map_map]
    simp only [Function.comp_def, toAdd_ofAdd]
    rw [← Fin.sum_univ_def, Finset.univ_sum_single]
  refine MonoidHom.ext fun r => ?_
  rw [hr r, map_list_prod, map_list_prod, List.map_map, List.map_map]
  congr 1
  apply List.map_congr_left
  intro b _
  exact h b _

/-- Conjugating the strip by an elementary matrix in the first `m` coordinates. -/
theorem conj_rowGen_elem (p : Root m) (c : B) (b : Fin m) (a : B) :
    shift (PresentedGroup.of (Gen.elem p c)) * rowGen b a *
      (shift (PresentedGroup.of (Gen.elem p c)))⁻¹ =
      rowGen b a * rowGen p.col (if b = p.row then -(a * c) else 0) := by
  rw [shift_of]
  have hT : ({Fin.last m, b.castSucc, p.row.castSucc, p.col.castSucc} : Finset (Fin (m + 1))).card
      ≤ 5 := le_trans Finset.card_le_four (by norm_num)
  have hsub : ∀ q : Root (m + 1), q.row ∈ ({Fin.last m, b.castSucc, p.row.castSucc,
      p.col.castSucc} : Finset (Fin (m + 1))) → q.col ∈ ({Fin.last m, b.castSucc, p.row.castSucc,
      p.col.castSucc} : Finset (Fin (m + 1))) → ∀ c, FreeGroup.of (Gen.elem q c) ∈
        supported (B := B) {Fin.last m, b.castSucc, p.row.castSucc, p.col.castSucc} := by
    intro q hr hc c
    exact supported_mono (Finset.insert_subset_iff.mpr ⟨hr, Finset.singleton_subset_iff.mpr hc⟩)
      (elem_supported q c)
  simp only [rowGen_eq_mk]
  rw [show (PresentedGroup.of (Gen.cast (Gen.elem p c)) : Pres (m + 1) B) =
      mk (FreeGroup.of (Gen.cast (Gen.elem p c))) from rfl, ← map_inv, ← map_mul, ← map_mul,
    ← map_mul]
  apply mk_eq_of_ev_eq hT
  · have h1 : FreeGroup.of (Gen.cast (Gen.elem p c)) ∈
        supported (B := B) {Fin.last m, b.castSucc, p.row.castSucc, p.col.castSucc} :=
      hsub (p.map (Kernel.coordinateIndex m) (Kernel.coordinateIndex_injective m))
        (by rw [castRoot_row]; simp) (by rw [castRoot_col]; simp) c
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ h1
      (hsub _ (by rw [rowRoot_row]; simp) (by rw [rowRoot_col]; simp) _)) (Subgroup.inv_mem _ h1)
  · exact Subgroup.mul_mem _ (hsub _ (by rw [rowRoot_row]; simp) (by rw [rowRoot_col]; simp) _)
      (hsub _ (by rw [rowRoot_row]; simp) (by rw [rowRoot_col]; simp) _)
  · simp only [map_mul, map_inv, ev_of, Gen.val, Gen.cast]
    by_cases hb : b = p.row
    · subst hb
      simp only [↓reduceIte]
      have key : bracket (Elementary.e (rowRoot p.row) (-a))
          (Elementary.e (p.map (Kernel.coordinateIndex m) (Kernel.coordinateIndex_injective m)) c) =
          Elementary.e (rowRoot p.col) (-a * c) :=
        Elementary.e_mul (Fin.last m) p.row.castSucc p.col.castSucc (castSucc_ne_last' _).symm
          ((Fin.castSucc_injective m).ne p.ne) (castSucc_ne_last' _).symm (-a) c
      rw [show Elementary.e (rowRoot p.row) (-a) = (Elementary.e (rowRoot p.row) a)⁻¹ by
        rw [Elementary.e_inv], bracket, inv_inv, neg_mul] at key
      rw [← key]
      group
    · simp only [hb, ↓reduceIte, Elementary.e_zero, mul_one]
      have hc := Elementary.e_commute
        (p.map (Kernel.coordinateIndex m) (Kernel.coordinateIndex_injective m)) (rowRoot b)
        (by rw [castRoot_col, rowRoot_row]; exact castSucc_ne_last' _)
        (by rw [castRoot_row, rowRoot_col]; exact (Fin.castSucc_injective m).ne (Ne.symm hb)) c a
      rw [hc.eq, mul_inv_cancel_right]

/-- Conjugating the strip by a diagonal unit in the first `m` coordinates. -/
theorem conj_rowGen_diag (i : Fin m) (u : Bˣ) (b : Fin m) (a : B) :
    shift (PresentedGroup.of (Gen.diag i u)) * rowGen b a *
      (shift (PresentedGroup.of (Gen.diag i u)))⁻¹ =
      rowGen b (if b = i then a * ((u⁻¹ : Bˣ) : B) else a) := by
  rw [shift_of]
  have hT : ({Fin.last m, b.castSucc, i.castSucc} : Finset (Fin (m + 1))).card ≤ 5 :=
    le_trans Finset.card_le_three (by norm_num)
  have hd : FreeGroup.of (Gen.cast (Gen.diag i u)) ∈
      supported (B := B) {Fin.last m, b.castSucc, i.castSucc} :=
    of_mem_supported (by simp [Gen.cast, Gen.supp, Kernel.coordinateIndex])
  have he : ∀ a' : B, FreeGroup.of (Gen.elem (rowRoot b) a') ∈
      supported (B := B) {Fin.last m, b.castSucc, i.castSucc} := fun a' =>
    supported_mono (by simp [Finset.insert_subset_iff]) (elem_supported _ _)
  simp only [rowGen_eq_mk]
  rw [show (PresentedGroup.of (Gen.cast (Gen.diag i u)) : Pres (m + 1) B) =
      mk (FreeGroup.of (Gen.cast (Gen.diag i u))) from rfl, ← map_inv, ← map_mul, ← map_mul]
  apply mk_eq_of_ev_eq hT (Subgroup.mul_mem _ (Subgroup.mul_mem _ hd (he a))
    (Subgroup.inv_mem _ hd)) (he _)
  simp only [map_mul, map_inv, ev_of, Gen.val, Gen.cast, d_inv]
  apply units_ext_mulVec
  intro x
  rw [Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, d_mulVec,
    e_mulVec, d_mulVec, e_mulVec]
  funext y
  have hci : Kernel.coordinateIndex m i = i.castSucc := rfl
  rw [hci]
  by_cases hy : y = i.castSucc
  · subst hy
    simp
  · by_cases hyl : y = Fin.last m
    · subst hyl
      by_cases hbi : b = i
      · subst hbi
        simp [mul_assoc]
      · simp [hbi, (Fin.castSucc_injective m).ne hbi]
    · simp [hy, hyl]

set_option linter.unusedSimpArgs false in
theorem single_vecMul_e (b : Fin m) (a : B) (p : Root m) (c : B) :
    (Pi.single b a : Fin m → B) ᵥ* ((Elementary.e p c : (Matrix (Fin m) (Fin m) B)ˣ) :
      Matrix (Fin m) (Fin m) B) =
      Pi.single b a + (if b = p.row then Pi.single p.col (a * c) else 0) := by
  funext k
  rw [Elementary.coe_e, Matrix.vecMul_add, Matrix.vecMul_one]
  by_cases hb : b = p.row
  · subst hb
    by_cases hk : k = p.col
    · subst hk
      simp [Matrix.vecMul, dotProduct, Matrix.single_apply, Pi.single_apply, p.ne]
    · simp [Matrix.vecMul, dotProduct, Matrix.single_apply, Pi.single_apply, hk, Ne.symm hk]
  · simp [Matrix.vecMul, dotProduct, Matrix.single_apply, Pi.single_apply, hb, Ne.symm hb]

set_option linter.unusedSimpArgs false in
theorem single_vecMul_d (b : Fin m) (a : B) (i : Fin m) (u : Bˣ) :
    (Pi.single b a : Fin m → B) ᵥ* ((d i u : (Matrix (Fin m) (Fin m) B)ˣ) :
      Matrix (Fin m) (Fin m) B) = Pi.single b (if b = i then a * (u : B) else a) := by
  funext k
  rw [coe_d, Matrix.vecMul_diagonal]
  by_cases hk : k = b
  · subst hk
    by_cases hi : k = i
    · subst hi
      simp
    · simp [hi]
  · simp [hk, Pi.single_apply]

/-- The conjugation law of the strip lifts to all of `Pres m B`. -/
theorem shift_conj_rowLift (γ : Pres m B) (r : Row m B) :
    shift γ * rowLift r * (shift γ)⁻¹ = rowLift (rowAct (π γ) r) := by
  have hγ : γ ∈ Subgroup.closure (Set.range (PresentedGroup.of (rels := rels (m := m) (B := B)))) := by
    rw [PresentedGroup.closure_range_of]
    trivial
  revert r
  induction hγ using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨g, rfl⟩ := hx
    intro r
    have hext : (MulAut.conj (shift (PresentedGroup.of g))).toMonoidHom.comp rowLift =
        rowLift.comp (rowAct (π (PresentedGroup.of g))).toMonoidHom := by
      apply row_hom_ext
      intro b a
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        rowLift_single]
      rw [show (PresentedGroup.of g : Pres m B) = mk (FreeGroup.of g) from rfl, π_mk, ev_of]
      show _ = rowLift (Multiplicative.ofAdd ((Pi.single b a : Fin m → B) ᵥ*
        ((g.val⁻¹ : (Matrix (Fin m) (Fin m) B)ˣ) : Matrix (Fin m) (Fin m) B)))
      cases g with
      | elem p c =>
        rw [show (mk (FreeGroup.of (Gen.elem p c)) : Pres m B) = PresentedGroup.of (Gen.elem p c)
          from rfl, conj_rowGen_elem]
        simp only [Gen.val, Elementary.e_inv]
        rw [single_vecMul_e, ofAdd_add, map_mul, rowLift_single]
        congr 1
        by_cases hb : b = p.row
        · simp [hb, rowLift_single, mul_neg]
        · simp [hb, rowGen_zero]
      | diag i u =>
        rw [show (mk (FreeGroup.of (Gen.diag i u)) : Pres m B) = PresentedGroup.of (Gen.diag i u)
          from rfl, conj_rowGen_diag]
        simp only [Gen.val, d_inv]
        rw [single_vecMul_d, rowLift_single]
    exact DFunLike.congr_fun hext r
  | one =>
    intro r
    simp
  | mul x y _ _ hx hy =>
    intro r
    rw [map_mul, mul_inv_rev, show shift x * shift y * rowLift r * ((shift y)⁻¹ * (shift x)⁻¹) =
      shift x * (shift y * rowLift r * (shift y)⁻¹) * (shift x)⁻¹ by group, hy, hx, map_mul,
      map_mul, MulAut.mul_apply]
  | inv x _ hx =>
    intro r
    have h := hx (rowAct (π x)⁻¹ r)
    have e : rowAct (π x) (rowAct (π x)⁻¹ r) = r := by
      rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
    rw [e] at h
    rw [map_inv shift x, inv_inv, map_inv π x, ← h]
    group

variable (ψ : (Matrix (Fin m) (Fin m) B)ˣ →* Pres m B) (hψ : ∀ A, π (ψ A) = A)

/-- The lift of the semidirect product to the presentation. -/
def κ : Row m B ⋊[rowAct] (Matrix (Fin m) (Fin m) B)ˣ →* Pres (m + 1) B :=
  SemidirectProduct.lift rowLift (shift.comp ψ) (fun A => MonoidHom.ext fun r => by
    show rowLift (rowAct A r) = shift (ψ A) * rowLift r * (shift (ψ A))⁻¹
    rw [shift_conj_rowLift, hψ])

include hψ in
theorem π_κ : π.comp (κ ψ hψ) = ι := by
  apply SemidirectProduct.hom_ext
  · refine MonoidHom.ext fun r => ?_
    simp only [MonoidHom.comp_apply, κ, SemidirectProduct.lift_inl, ι_inl, π_rowLift]
    rfl
  · refine MonoidHom.ext fun A => ?_
    simp only [MonoidHom.comp_apply, κ, SemidirectProduct.lift_inr, ι_inr]
    rw [← MonoidHom.comp_apply π shift, π_shift, MonoidHom.comp_apply, hψ]

/-- The section of the stabilizer of the last standard column. -/
noncomputable def σ : (ι (m := m) (B := B)).range →* Pres (m + 1) B :=
  (κ ψ hψ).comp (MonoidHom.ofInjective ι_injective).symm.toMonoidHom

include hψ in
theorem π_σ (p : (ι (m := m) (B := B)).range) : π (σ ψ hψ p) = p := by
  have h := DFunLike.congr_fun (π_κ ψ hψ) ((MonoidHom.ofInjective ι_injective).symm p)
  simp only [MonoidHom.comp_apply] at h
  rw [σ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, h]
  have h2 := MonoidHom.ofInjective_apply (ι_injective (m := m) (B := B))
    (x := (MonoidHom.ofInjective ι_injective).symm p)
  rw [← h2, MulEquiv.apply_symm_apply]

end GLPres
end AllPrimeGroups
