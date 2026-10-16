import AllPrimeGroups.GLLift

/-! The literal swap of two coordinates in the presentation (manuscript Lemma 11.1, "let s be
the literal swap of the first two columns, expressed using the allowed elementary and diagonal
generators").

`swapWord a b = x_{ab}(1) x_{ba}(-1) x_{ab}(1) d_a(-1)` evaluates to the permutation matrix of the
transposition of `a` and `b`. Conjugation by it relabels the coordinates of a generator, by a
relation on at most four coordinates. -/

namespace AllPrimeGroups
namespace GLPres

open LocalGL Matrix

variable {B : Type*} [Ring B] {n : ℕ}

/-- The word of the transposition of `a` and `b`. -/
def swapWord (a b : Fin n) (h : a ≠ b) : FreeGroup (Gen n B) :=
  FreeGroup.of (Gen.elem ⟨a, b, h⟩ 1) * FreeGroup.of (Gen.elem ⟨b, a, h.symm⟩ (-1)) *
    FreeGroup.of (Gen.elem ⟨a, b, h⟩ 1) * FreeGroup.of (Gen.diag a (-1))

set_option linter.unusedSimpArgs false in
theorem swapWord_mulVec (a b : Fin n) (h : a ≠ b) (x : Fin n → B) :
    ((ev (swapWord (B := B) a b h) : (Matrix (Fin n) (Fin n) B)ˣ) : Matrix (Fin n) (Fin n) B) *ᵥ x =
      fun k => x (Equiv.swap a b k) := by
  simp only [swapWord, map_mul, ev_of, Gen.val, Units.val_mul, ← Matrix.mulVec_mulVec, e_mulVec,
    d_mulVec]
  funext k
  by_cases hka : k = a
  · subst hka
    simp [h, Ne.symm h, Equiv.swap_apply_left]
  · by_cases hkb : k = b
    · subst hkb
      simp [hka, Ne.symm h, Equiv.swap_apply_right]
    · simp [hka, hkb, Equiv.swap_apply_of_ne_of_ne hka hkb]

/-- Relabelling the coordinates of a generator by a permutation. -/
def Gen.perm (τ : Equiv.Perm (Fin n)) : Gen n B → Gen n B
  | .elem p c => .elem ⟨τ p.row, τ p.col, τ.injective.ne p.ne⟩ c
  | .diag i u => .diag (τ i) u

theorem Gen.supp_perm (τ : Equiv.Perm (Fin n)) (g : Gen n B) :
    (g.perm τ).supp = g.supp.map τ.toEmbedding := by
  cases g with
  | elem p c => simp [Gen.perm, Gen.supp, Finset.map_insert, Finset.map_singleton]
  | diag i u => simp [Gen.perm, Gen.supp]

theorem Gen.supp_card (g : Gen n B) : g.supp.card ≤ 2 := by
  cases g with
  | elem p c => exact Finset.card_le_two
  | diag i u => simp [Gen.supp]

theorem swapWord_mem (a b : Fin n) (h : a ≠ b) : swapWord (B := B) a b h ∈ supported {a, b} := by
  unfold swapWord
  refine Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ ?_) ?_) ?_
  · exact of_mem_supported (by simp [Gen.supp])
  · exact of_mem_supported (by simp [Gen.supp, Finset.insert_subset_iff])
  · exact of_mem_supported (by simp [Gen.supp])
  · exact of_mem_supported (by simp [Gen.supp])

/-- The swap matrix acts on columns by the transposition, so does its inverse. -/
theorem swapWord_inv_mulVec (a b : Fin n) (h : a ≠ b) (x : Fin n → B) :
    (((ev (swapWord (B := B) a b h))⁻¹ : (Matrix (Fin n) (Fin n) B)ˣ) :
      Matrix (Fin n) (Fin n) B) *ᵥ x = fun k => x (Equiv.swap a b k) := by
  have h1 : ((ev (swapWord (B := B) a b h) : (Matrix (Fin n) (Fin n) B)ˣ) :
      Matrix (Fin n) (Fin n) B) *ᵥ (fun k => x (Equiv.swap a b k)) = x := by
    rw [swapWord_mulVec]
    funext k
    simp
  calc (((ev (swapWord (B := B) a b h))⁻¹ : (Matrix (Fin n) (Fin n) B)ˣ) :
        Matrix (Fin n) (Fin n) B) *ᵥ x =
      (((ev (swapWord (B := B) a b h))⁻¹ : (Matrix (Fin n) (Fin n) B)ˣ) :
        Matrix (Fin n) (Fin n) B) *ᵥ (((ev (swapWord (B := B) a b h) :
          (Matrix (Fin n) (Fin n) B)ˣ) : Matrix (Fin n) (Fin n) B) *ᵥ
            (fun k => x (Equiv.swap a b k))) := by rw [h1]
    _ = fun k => x (Equiv.swap a b k) := by
      rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]

/-- Conjugation by the swap relabels a generator. -/
theorem conj_swap (a b : Fin n) (h : a ≠ b) (g : Gen n B) :
    mk (swapWord a b h) * PresentedGroup.of g * (mk (swapWord a b h))⁻¹ =
      PresentedGroup.of (g.perm (Equiv.swap a b)) := by
  have hT : ({a, b} ∪ g.supp).card ≤ 5 :=
    le_trans (Finset.card_union_le _ _) (by have := Gen.supp_card g; have := Finset.card_le_two (a := a) (b := b); omega)
  have hsw : swapWord (B := B) a b h ∈ supported ({a, b} ∪ g.supp) :=
    supported_mono Finset.subset_union_left (swapWord_mem a b h)
  have hg : FreeGroup.of g ∈ supported (B := B) ({a, b} ∪ g.supp) :=
    of_mem_supported Finset.subset_union_right
  have hg' : FreeGroup.of (g.perm (Equiv.swap a b)) ∈ supported (B := B) ({a, b} ∪ g.supp) := by
    apply of_mem_supported
    rw [Gen.supp_perm]
    intro k hk
    obtain ⟨l, hl, rfl⟩ := Finset.mem_map.mp hk
    simp only [Equiv.toEmbedding_apply, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    by_cases hla : l = a
    · subst hla
      simp
    · by_cases hlb : l = b
      · subst hlb
        simp
      · rw [Equiv.swap_apply_of_ne_of_ne hla hlb]
        exact Or.inr hl
  rw [show (PresentedGroup.of g : Pres n B) = mk (FreeGroup.of g) from rfl,
    show (PresentedGroup.of (g.perm (Equiv.swap a b)) : Pres n B) =
      mk (FreeGroup.of (g.perm (Equiv.swap a b))) from rfl, ← map_inv, ← map_mul, ← map_mul]
  apply mk_eq_of_ev_eq hT (Subgroup.mul_mem _ (Subgroup.mul_mem _ hsw hg) (Subgroup.inv_mem _ hsw)) hg'
  rw [map_mul, map_mul, map_inv, ev_of, ev_of]
  apply units_ext_mulVec
  intro x
  rw [Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    swapWord_inv_mulVec, swapWord_mulVec]
  funext k
  cases g with
  | elem p c =>
    simp only [Gen.val, Gen.perm, e_mulVec, Equiv.swap_apply_self]
    by_cases hk : Equiv.swap a b k = p.row
    · have hk' : k = Equiv.swap a b p.row := by rw [← hk, Equiv.swap_apply_self]
      simp [hk']
    · have hk' : k ≠ Equiv.swap a b p.row := by
        intro e
        apply hk
        rw [e, Equiv.swap_apply_self]
      simp [hk, hk']
  | diag i u =>
    simp only [Gen.val, Gen.perm, d_mulVec, Equiv.swap_apply_self]
    by_cases hk : Equiv.swap a b k = i
    · have hk' : k = Equiv.swap a b i := by rw [← hk, Equiv.swap_apply_self]
      simp [hk']
    · have hk' : k ≠ Equiv.swap a b i := by
        intro e
        apply hk
        rw [e, Equiv.swap_apply_self]
      simp [hk, hk']

theorem swap_sq (a b : Fin n) (h : a ≠ b) :
    mk (swapWord (B := B) a b h) * mk (swapWord a b h) = 1 := by
  rw [← map_mul, ← map_one (mk (m := n) (B := B))]
  apply mk_eq_of_ev_eq (T := {a, b}) (le_trans Finset.card_le_two (by norm_num))
    (Subgroup.mul_mem _ (swapWord_mem a b h) (swapWord_mem a b h)) (Subgroup.one_mem _)
  rw [map_mul, map_one]
  apply units_ext_mulVec
  intro x
  rw [Units.val_mul, ← Matrix.mulVec_mulVec, swapWord_mulVec, swapWord_mulVec, Units.val_one,
    Matrix.one_mulVec]
  funext k
  simp

end GLPres
end AllPrimeGroups
