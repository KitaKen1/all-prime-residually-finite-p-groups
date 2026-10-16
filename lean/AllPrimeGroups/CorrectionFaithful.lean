import AllPrimeGroups.CorrectionSubgroup

/-! Faithfulness of the correction subgroup (manuscript Lemma 20.3).

Generators of the correction subgroup are recorded by codes: an off-diagonal wrong-row root, or
an opposite-root commutator at a coordinate. Every element of the subgroup is a product of
generators, since in characteristic ℓ inverses are powers. The matrix of a generator minus the
identity is a single entry, and any two of these products vanish, so the matrix of a product of
generators is the identity plus the sum of their entries.

If that sum vanishes, the off-diagonal generators at one position multiply to a root with
parameter zero. The diagonal generators at a coordinate depend only on their word, by the
nonzero case of manuscript Lemma 20.2 (`CutIndependent`), and each has order ℓ. Linear
independence of the words over `ZMod ℓ` shows that each of them occurs a multiple of ℓ times.
Hence a product of generators with identity matrix is trivial. -/

namespace AllPrimeGroups
noncomputable section
namespace Kernel
open Classical

theorem one_add_bracket_matrix {M : Type*} [Ring M] (A B : M) (hAA : A * A = 0)
    (hBB : B * B = 0) (hBA : B * A = 0) :
    (1 + A) * (1 + B) * (1 - A) * (1 - B) = 1 + A * B := by
  have e1 : (1 + A) * (1 + B) * (1 - A) = 1 + B + A * B := by
    calc (1 + A) * (1 + B) * (1 - A) = 1 + B + A * B - A * A - B * A - A * (B * A) := by
          noncomm_ring
      _ = 1 + B + A * B := by rw [hAA, hBA, mul_zero, sub_zero, sub_zero, sub_zero]
  calc (1 + A) * (1 + B) * (1 - A) * (1 - B) = (1 + B + A * B) * (1 - B) := by rw [e1]
    _ = 1 + A * B - B * B - A * (B * B) := by noncomm_ring
    _ = 1 + A * B := by rw [hBB, mul_zero, sub_zero, sub_zero]

theorem single_mul_single_eq {K : ℕ} {R : Type*} [Ring R] (i j k l : Fin K) (x y : R) :
    Matrix.single i j x * Matrix.single k l y = if j = k then Matrix.single i l (x * y) else 0 := by
  split_ifs with h
  · subst h
    exact Matrix.single_mul_single_same _ _ _ _ _
  · exact Matrix.single_mul_single_of_ne (c := x) i j k h y

theorem indexedRoot_of_ne {K : ℕ} {R : Type*} [Ring R] {i j : Fin K} (h : i ≠ j) (a : R) :
    Steinberg.indexedRoot i j a = Steinberg.x ⟨i, j, h⟩ a := by
  simp [Steinberg.indexedRoot, h]

theorem list_sum_apply {K : ℕ} {R : Type*} [Ring R] (L : List (Matrix (Fin K) (Fin K) R))
    (i j : Fin K) : L.sum i j = (L.map (fun M => M i j)).sum := by
  induction L with
  | nil => simp
  | cons M L ih => simp [List.sum_cons, Matrix.add_apply, ih]

theorem sum_map_ite_filter {α M : Type*} [AddCommMonoid M] (L : List α) (q : α → Prop)
    [DecidablePred q] (f : α → M) :
    (L.map (fun x => if q x then f x else 0)).sum = ((L.filter (fun x => decide (q x))).map f).sum := by
  induction L with
  | nil => simp
  | cons x L ih =>
    by_cases h : q x
    · simp [h, ih]
    · simp [h, ih]

theorem sum_indicator_eq_length {α S : Type*} [AddCommMonoidWithOne S] (L : List α)
    (q : α → Prop) [DecidablePred q] :
    (L.map (fun x => if q x then (1 : S) else 0)).sum = ((L.filter (fun x => decide (q x))).length : S) := by
  rw [sum_map_ite_filter]
  simp

/-- Codes of the generators of the correction subgroup. -/
inductive GenCode (K : ℕ) (R : Type*)
  | root : Fin K → Fin K → R → GenCode K R
  | diag : Fin K → Fin K → R → R → GenCode K R

namespace GenCode
variable {K : ℕ} {R : Type*} [Ring R]

/-- The group element of a code. -/
def ev : GenCode K R → Steinberg K R
  | root i j a => Steinberg.indexedRoot i j a
  | diag i j a b => bracket (Steinberg.indexedRoot i j a) (Steinberg.indexedRoot j i b)

/-- The matrix of a code, minus the identity. -/
def mat : GenCode K R → Matrix (Fin K) (Fin K) R
  | root i j a => Matrix.single i j a
  | diag i _ a b => Matrix.single i i (a * b)

/-- Whether a code is a root at a given position. -/
def IsRootAt (i j : Fin K) : GenCode K R → Prop
  | root i' j' _ => i' = i ∧ j' = j
  | diag _ _ _ _ => False

/-- Whether a code is a diagonal generator at a given coordinate. -/
def IsDiagAt (i : Fin K) : GenCode K R → Prop
  | root _ _ _ => False
  | diag i' _ _ _ => i' = i

/-- The parameter of a root code. -/
def param : GenCode K R → R
  | root _ _ a => a
  | diag _ _ _ _ => 0

/-- The word of a diagonal code. -/
def word : GenCode K R → R
  | root _ _ _ => 0
  | diag _ _ a b => a * b

theorem prod_ev_of_isRootAt (i j : Fin K) (L : List (GenCode K R)) (h : ∀ c ∈ L, c.IsRootAt i j) :
    (L.map ev).prod = Steinberg.indexedRoot i j (L.map param).sum := by
  induction L with
  | nil =>
    simp only [List.map_nil, List.prod_nil, List.sum_nil]
    exact ((Steinberg.rootFamily (n := K) (R := R)).zero i j).symm
  | cons c L ih =>
    have hc := h c (List.mem_cons.mpr (Or.inl rfl))
    rw [List.map_cons, List.map_cons, List.prod_cons, List.sum_cons,
      ih (fun d hd => h d (List.mem_cons.mpr (Or.inr hd))), Steinberg.indexedRoot_add]
    cases c with
    | root i' j' a =>
      obtain ⟨rfl, rfl⟩ := hc
      rfl
    | diag _ _ _ _ => exact absurd hc id

theorem sum_mat_of_isRootAt (i j : Fin K) (L : List (GenCode K R)) (h : ∀ c ∈ L, c.IsRootAt i j) :
    (L.map mat).sum = Matrix.single i j (L.map param).sum := by
  induction L with
  | nil => simp
  | cons c L ih =>
    have hc := h c (List.mem_cons.mpr (Or.inl rfl))
    rw [List.map_cons, List.map_cons, List.sum_cons, List.sum_cons,
      ih (fun d hd => h d (List.mem_cons.mpr (Or.inr hd))), Matrix.single_add]
    cases c with
    | root i' j' a =>
      obtain ⟨rfl, rfl⟩ := hc
      rfl
    | diag _ _ _ _ => exact absurd hc id

theorem mat_apply_offdiag {i j : Fin K} (hij : i ≠ j) (c : GenCode K R)
    (hc : ∀ i' j' a, c = root i' j' a → i' ≠ j') :
    c.mat i j = if c.IsRootAt i j then c.param else 0 := by
  cases c with
  | root i' j' a =>
    have := hc i' j' a rfl
    simp only [mat, IsRootAt, param, Matrix.single_apply]
    by_cases h1 : i' = i <;> by_cases h2 : j' = j <;> simp [h1, h2]
  | diag i' _ a b =>
    simp only [mat, IsRootAt, Matrix.single_apply]
    by_cases h1 : i' = i
    · subst h1
      simp [hij]
    · simp [h1]

theorem mat_apply_diag (i : Fin K) (c : GenCode K R)
    (hc : ∀ i' j' a, c = root i' j' a → i' ≠ j') :
    c.mat i i = if c.IsDiagAt i then c.word else 0 := by
  cases c with
  | root i' j' a =>
    have := hc i' j' a rfl
    simp only [mat, IsDiagAt, Matrix.single_apply]
    by_cases h1 : i' = i
    · subst h1
      simp [Ne.symm this]
    · simp [h1]
  | diag i' _ a b =>
    simp only [mat, IsDiagAt, word, Matrix.single_apply]
    by_cases h1 : i' = i <;> simp [h1]

end GenCode

namespace CyclicPhases
variable {m : ℕ} [NeZero m] {R : Type*} [Ring R] (P : CyclicPhases R m)

/-- Manuscript Lemma 20.2, nonzero case, as a hypothesis: an opposite-root commutator of words
with mismatched outer phases depends only on their product and not on the auxiliary
coordinate. -/
def CutIndependent (k : ℕ) : Prop :=
  ∀ (i j j' : Fin k) (hij : i ≠ j) (hij' : i ≠ j'), ∀ a ∈ P.W, ∀ b ∈ P.W, ∀ a' ∈ P.W,
    ∀ b' ∈ P.W, P.σ a ≠ P.τ b → P.σ a' ≠ P.τ b' → a * b = a' * b' →
    bracket (Steinberg.x ⟨i, j, hij⟩ a) (Steinberg.x ⟨j, i, hij.symm⟩ b) =
      bracket (Steinberg.x ⟨i, j', hij'⟩ a') (Steinberg.x ⟨j', i, hij'.symm⟩ b')

end CyclicPhases

namespace PhaseGrading
variable {ℓ : ℕ} {R : Type*} [Ring R] [Algebra (ZMod ℓ) R]
variable {m : ℕ} [NeZero m] (G : PhaseGrading ℓ R m) {K : ℕ} (P : Fin K → Fin m)

/-- Validity of a code: it describes a generator of the correction subgroup. -/
def ValidCode : GenCode K R → Prop
  | .root i j a => i ≠ j ∧ a ∈ G.W ∧ P i ≠ G.σ a ∧ P j = G.τ a
  | .diag i j a b => i ≠ j ∧ a ∈ G.W ∧ b ∈ G.W ∧ P i ≠ G.σ a ∧ P i = G.τ b

theorem ValidCode.root_ne {c : GenCode K R} (hc : G.ValidCode P c) :
    ∀ i' j' a, c = .root i' j' a → i' ≠ j' := by
  rintro i' j' a rfl
  exact hc.1

theorem ev_mem_gens {c : GenCode K R} (hc : G.ValidCode P c) :
    c.ev ∈ G.wrongRoots P ∪ G.wrongDiagonals P := by
  cases c with
  | root i j a =>
    obtain ⟨hij, ha, hi, hj⟩ := hc
    exact Or.inl ⟨i, j, hij, a, ha, hi, hj, indexedRoot_of_ne hij a⟩
  | diag i j a b =>
    obtain ⟨hij, ha, hb, hi, hi'⟩ := hc
    refine Or.inr ⟨i, j, hij, a, b, ha, hb, hi, hi', ?_⟩
    change bracket (Steinberg.indexedRoot i j a) (Steinberg.indexedRoot j i b) = _
    rw [indexedRoot_of_ne hij, indexedRoot_of_ne hij.symm]

theorem rep_ev {c : GenCode K R} (hc : G.ValidCode P c) :
    (Elementary.representation c.ev).val = 1 + c.mat := by
  cases c with
  | root i j a =>
    obtain ⟨hij, -, -, -⟩ := hc
    change (Elementary.representation (Steinberg.indexedRoot i j a)).val =
      1 + Matrix.single i j a
    rw [indexedRoot_of_ne hij, Elementary.representation_x]
    rfl
  | diag i j a b =>
    obtain ⟨hij, ha, hb, hi, hi'⟩ := hc
    have hba : b * a = 0 := G.mul_eq_zero b hb a ha (by rw [← hi']; exact hi)
    change (Elementary.representation (bracket (Steinberg.indexedRoot i j a)
      (Steinberg.indexedRoot j i b))).val = 1 + Matrix.single i i (a * b)
    rw [indexedRoot_of_ne hij, indexedRoot_of_ne hij.symm, bracket, ← Steinberg.x_neg,
      ← Steinberg.x_neg, map_mul, map_mul, map_mul, Elementary.representation_x,
      Elementary.representation_x, Elementary.representation_x, Elementary.representation_x]
    change (1 + Matrix.single i j a) * (1 + Matrix.single j i b) * (1 + Matrix.single i j (-a)) *
      (1 + Matrix.single j i (-b)) = 1 + Matrix.single i i (a * b)
    have hneg : ∀ (p q : Fin K) (r : R), Matrix.single p q (-r) = -Matrix.single p q r := by
      intro p q r
      ext x y
      simp only [Matrix.single_apply, Matrix.neg_apply]
      split_ifs <;> simp
    rw [hneg, hneg, ← sub_eq_add_neg, ← sub_eq_add_neg, one_add_bracket_matrix,
      Matrix.single_mul_single_same]
    · rw [single_mul_single_eq]
      simp [Ne.symm hij]
    · rw [single_mul_single_eq]
      simp [hij]
    · rw [single_mul_single_eq]
      simp [hba]

theorem mat_mul_mat {c d : GenCode K R} (hc : G.ValidCode P c) (hd : G.ValidCode P d) :
    c.mat * d.mat = 0 := by
  have vanish : ∀ {x y : R}, x ∈ G.W → y ∈ G.W → G.τ x ≠ G.σ y → x * y = 0 :=
    fun hx hy h => G.mul_eq_zero _ hx _ hy h
  cases c with
  | root i j a =>
    obtain ⟨_, ha, _, hj⟩ := hc
    cases d with
    | root k l b =>
      obtain ⟨_, hb, hk, _⟩ := hd
      change Matrix.single i j a * Matrix.single k l b = 0
      rw [single_mul_single_eq]
      split_ifs with h
      · rw [vanish ha hb (by rw [← hj, h]; exact hk), Matrix.single_zero]
      · rfl
    | diag k l c d' =>
      obtain ⟨_, hc', _, hk, _⟩ := hd
      change Matrix.single i j a * Matrix.single k k (c * d') = 0
      rw [single_mul_single_eq]
      split_ifs with h
      · rw [← mul_assoc, vanish ha hc' (by rw [← hj, h]; exact hk), zero_mul, Matrix.single_zero]
      · rfl
  | diag i j a b =>
    obtain ⟨_, _, hb, _, hi'⟩ := hc
    cases d with
    | root k l c =>
      obtain ⟨_, hc', hk, _⟩ := hd
      change Matrix.single i i (a * b) * Matrix.single k l c = 0
      rw [single_mul_single_eq]
      split_ifs with h
      · rw [mul_assoc, vanish hb hc' (by rw [← hi', h]; exact hk), mul_zero, Matrix.single_zero]
      · rfl
    | diag k l c d' =>
      obtain ⟨_, hc', _, hk, _⟩ := hd
      change Matrix.single i i (a * b) * Matrix.single k k (c * d') = 0
      rw [single_mul_single_eq]
      split_ifs with h
      · rw [mul_assoc, ← mul_assoc b, vanish hb hc' (by rw [← hi', h]; exact hk), zero_mul,
          mul_zero, Matrix.single_zero]
      · rfl

theorem mat_mul_sum {c : GenCode K R} (hc : G.ValidCode P c) (L : List (GenCode K R))
    (hL : ∀ d ∈ L, G.ValidCode P d) : c.mat * (L.map GenCode.mat).sum = 0 := by
  induction L with
  | nil => simp
  | cons d L ih =>
    rw [List.map_cons, List.sum_cons, mul_add,
      G.mat_mul_mat P hc (hL d (List.mem_cons.mpr (Or.inl rfl))),
      ih (fun e he => hL e (List.mem_cons.mpr (Or.inr he))), add_zero]

theorem rep_prod (L : List (GenCode K R)) (hL : ∀ c ∈ L, G.ValidCode P c) :
    (Elementary.representation (L.map GenCode.ev).prod).val = 1 + (L.map GenCode.mat).sum := by
  induction L with
  | nil => simp
  | cons c L ih =>
    have hc := hL c (List.mem_cons.mpr (Or.inl rfl))
    have hL' : ∀ d ∈ L, G.ValidCode P d := fun d hd => hL d (List.mem_cons.mpr (Or.inr hd))
    have hzero := G.mat_mul_sum P hc L hL'
    rw [List.map_cons, List.prod_cons, map_mul, Units.val_mul, G.rep_ev P hc, ih hL',
      List.map_cons, List.sum_cons, mul_add, add_mul, add_mul, one_mul, mul_one, one_mul, hzero,
      add_zero]
    abel

/-- Generators of the correction subgroup have order dividing ℓ. -/
theorem ev_pow_char (hK : 5 ≤ K) {c : GenCode K R} (hc : G.ValidCode P c) : c.ev ^ ℓ = 1 := by
  cases c with
  | root i j a =>
    obtain ⟨hij, -, -, -⟩ := hc
    change Steinberg.indexedRoot i j a ^ ℓ = 1
    rw [indexedRoot_of_ne hij, x_pow_char]
  | diag i j a b =>
    obtain ⟨hij, ha, hb, hi, hi'⟩ := hc
    have hba : b * a = 0 := G.mul_eq_zero b hb a ha (by rw [← hi']; exact hi)
    obtain ⟨h, h1, h2, -, -⟩ := exists_fresh hK i j i j
    have hcomm := ((Steinberg.rootFamily (n := K) (R := R)).opposite_commutator_centralizes
      (Ne.symm h1) h2 hij a b hba).1.symm
    have hp := hcomm.commutatorElement_pow_left ℓ
    change bracket (Steinberg.indexedRoot i j a) (Steinberg.indexedRoot j i b) ^ ℓ =
      bracket (Steinberg.indexedRoot i j a ^ ℓ) (Steinberg.indexedRoot j i b) at hp
    rw [indexedRoot_of_ne hij a, x_pow_char] at hp
    change bracket (Steinberg.indexedRoot i j a) (Steinberg.indexedRoot j i b) ^ ℓ = 1
    rw [indexedRoot_of_ne hij a, hp]
    simp [bracket]

theorem gens_pairwise (hK : 5 ≤ K) (hopp : G.OppositeCommute K) (L : List (GenCode K R))
    (hL : ∀ c ∈ L, G.ValidCode P c) : (L.map GenCode.ev).Pairwise Commute := by
  apply List.pairwise_of_forall_mem_list
  intro x hx y hy
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hy
  exact G.gens_commute P hK hopp (G.ev_mem_gens P (hL c hc)) (G.ev_mem_gens P (hL d hd))

theorem prod_split (hK : 5 ≤ K) (hopp : G.OppositeCommute K) (L : List (GenCode K R))
    (hL : ∀ c ∈ L, G.ValidCode P c) (p : GenCode K R → Bool) :
    (L.map GenCode.ev).prod =
      ((L.filter p).map GenCode.ev).prod * ((L.filter (fun c => !p c)).map GenCode.ev).prod := by
  rw [← List.prod_append, ← List.map_append]
  exact ((List.filter_append_perm p L).map GenCode.ev).symm.prod_eq'
    (G.gens_pairwise P hK hopp L hL)

theorem sum_split (L : List (GenCode K R)) (p : GenCode K R → Bool) :
    (L.map GenCode.mat).sum =
      ((L.filter p).map GenCode.mat).sum + ((L.filter (fun c => !p c)).map GenCode.mat).sum := by
  rw [← List.sum_append, ← List.map_append]
  exact ((List.filter_append_perm p L).map GenCode.mat).sum_eq.symm

/-- The inverse of a product of generators is a product of generators. -/
theorem prod_inv_codes [Fact ℓ.Prime] (hK : 5 ≤ K) (L : List (GenCode K R))
    (hL : ∀ c ∈ L, G.ValidCode P c) :
    ((L.reverse.flatMap (fun c => List.replicate (ℓ - 1) c)).map GenCode.ev).prod =
      ((L.map GenCode.ev).prod)⁻¹ := by
  induction L with
  | nil => simp
  | cons c L ih =>
    have hc := hL c (List.mem_cons.mpr (Or.inl rfl))
    rw [List.reverse_cons, List.flatMap_append, List.map_append, List.prod_append,
      ih (fun d hd => hL d (List.mem_cons.mpr (Or.inr hd))), List.flatMap_singleton,
      List.map_replicate, List.prod_replicate, List.map_cons, List.prod_cons, mul_inv_rev]
    congr 1
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_succ, Nat.sub_add_cancel (Fact.out : ℓ.Prime).one_lt.le, G.ev_pow_char P hK hc]

/-- Every element of the correction subgroup is a product of generators. -/
theorem exists_codes [Fact ℓ.Prime] (hK : 5 ≤ K) {u : Steinberg K R} (hu : u ∈ G.correction P) :
    ∃ L : List (GenCode K R), (∀ c ∈ L, G.ValidCode P c) ∧ (L.map GenCode.ev).prod = u := by
  induction hu using Subgroup.closure_induction with
  | mem g hg =>
    rcases hg with ⟨i, j, hij, a, ha, hi, hj, rfl⟩ | ⟨i, j, hij, a, b, ha, hb, hi, hi', rfl⟩
    · refine ⟨[.root i j a], ?_, ?_⟩
      · intro c hc
        rw [List.mem_singleton.mp hc]
        exact ⟨hij, ha, hi, hj⟩
      · simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
        exact indexedRoot_of_ne hij a
    · refine ⟨[.diag i j a b], ?_, ?_⟩
      · intro c hc
        rw [List.mem_singleton.mp hc]
        exact ⟨hij, ha, hb, hi, hi'⟩
      · simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
        change bracket (Steinberg.indexedRoot i j a) (Steinberg.indexedRoot j i b) = _
        rw [indexedRoot_of_ne hij, indexedRoot_of_ne hij.symm]
  | one => exact ⟨[], by simp, by simp⟩
  | mul g h _ _ ihg ihh =>
    obtain ⟨L, hL, rfl⟩ := ihg
    obtain ⟨M, hM, rfl⟩ := ihh
    exact ⟨L ++ M, fun c hc => (List.mem_append.mp hc).elim (hL c) (hM c), by simp⟩
  | inv g _ ih =>
    obtain ⟨L, hL, rfl⟩ := ih
    refine ⟨L.reverse.flatMap (fun c => List.replicate (ℓ - 1) c), ?_, G.prod_inv_codes P hK L hL⟩
    intro c hc
    obtain ⟨d, hd, hmem⟩ := List.mem_flatMap.mp hc
    rw [List.eq_of_mem_replicate hmem]
    exact hL d (List.mem_reverse.mp hd)

theorem word_mem_or_zero {c : GenCode K R} (hc : G.ValidCode P c) : c.word ∈ G.W ∨ c.word = 0 := by
  cases c with
  | root _ _ _ => exact Or.inr rfl
  | diag i j a b =>
    obtain ⟨_, ha, hb, _, _⟩ := hc
    by_cases h : a * b = 0
    · exact Or.inr h
    · exact Or.inl (G.mul_mem a ha b hb h).1

/-- A product of generators whose matrices sum to zero is trivial. -/
theorem prod_eq_one [Fact ℓ.Prime] (hK : 5 ≤ K) (hopp : G.OppositeCommute K)
    (hind : G.CutIndependent K) (hli : LinearIndependent (ZMod ℓ) (fun w : G.W => (w : R))) :
    ∀ L : List (GenCode K R), (∀ c ∈ L, G.ValidCode P c) → (L.map GenCode.mat).sum = 0 →
      (L.map GenCode.ev).prod = 1 := by
  suffices H : ∀ n, ∀ L : List (GenCode K R), L.length = n → (∀ c ∈ L, G.ValidCode P c) →
      (L.map GenCode.mat).sum = 0 → (L.map GenCode.ev).prod = 1 from
    fun L => H L.length L rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro L hlen hL hsum
  cases L with
  | nil => simp
  | cons c L' =>
  have hc := hL c (List.mem_cons.mpr (Or.inl rfl))
  -- the rest after removing a class of generators
  have rest : ∀ p : GenCode K R → Bool, p c = true →
      (((c :: L').filter p).map GenCode.ev).prod = 1 →
      (((c :: L').filter p).map GenCode.mat).sum = 0 →
      ((c :: L').map GenCode.ev).prod = 1 := by
    intro p hpc hprod hmat
    rw [G.prod_split P hK hopp _ hL p, hprod, one_mul]
    apply ih (((c :: L').filter (fun d => !p d)).length) _ _ rfl
    · intro d hd
      exact hL d (List.mem_of_mem_filter hd)
    · rw [sum_split (c :: L') p, hmat, zero_add] at hsum
      exact hsum
    · rw [← hlen]
      apply List.length_filter_lt_length_iff_exists.mpr
      exact ⟨c, List.mem_cons.mpr (Or.inl rfl), by simp [hpc]⟩
  cases c with
  | root i j a =>
    obtain ⟨hij, ha, hi, hj⟩ := hc
    let p : GenCode K R → Bool := fun d => decide (d.IsRootAt i j)
    have hp : ∀ d ∈ (GenCode.root i j a :: L').filter p, d.IsRootAt i j := by
      intro d hd
      have h := List.of_mem_filter hd
      simpa [p] using h
    have hentry : (((GenCode.root i j a :: L').filter p).map GenCode.param).sum = 0 := by
      have h := congrFun (congrFun hsum i) j
      rw [list_sum_apply, Matrix.zero_apply, List.map_map] at h
      rw [← h, ← sum_map_ite_filter]
      congr 1
      apply List.map_congr_left
      intro d hd
      exact (GenCode.mat_apply_offdiag hij d (ValidCode.root_ne G P (hL d hd))).symm
    apply rest p (by simp [p, GenCode.IsRootAt])
    · rw [GenCode.prod_ev_of_isRootAt i j _ hp, hentry]
      exact (Steinberg.rootFamily (n := K) (R := R)).zero i j
    · rw [GenCode.sum_mat_of_isRootAt i j _ hp, hentry, Matrix.single_zero]
  | diag i j a b =>
    have hcv := hc
    obtain ⟨hij, ha, hb, hi, hi'⟩ := hc
    have hσ : G.σ a ≠ G.τ b := by rw [← hi']; exact Ne.symm hi
    by_cases hab : a * b = 0
    · have hev : (GenCode.diag i j a b : GenCode K R).ev = 1 := by
        change bracket (Steinberg.indexedRoot i j a) (Steinberg.indexedRoot j i b) = 1
        rw [indexedRoot_of_ne hij, indexedRoot_of_ne hij.symm]
        exact (bracket_eq_one_iff _ _).mpr (hopp i j hij a ha b hb hσ hab)
      have hmat : (GenCode.diag i j a b : GenCode K R).mat = 0 := by
        change Matrix.single i i (a * b) = 0
        rw [hab, Matrix.single_zero]
      rw [List.map_cons, List.prod_cons, hev, one_mul]
      apply ih L'.length _ L' rfl
      · intro d hd
        exact hL d (List.mem_cons.mpr (Or.inr hd))
      · rw [List.map_cons, List.sum_cons, hmat, zero_add] at hsum
        exact hsum
      · rw [← hlen]
        exact Nat.lt_succ_self _
    · obtain ⟨hv, hσv, hτv⟩ := G.mul_mem a ha b hb hab
      let v := a * b
      let p : GenCode K R → Bool := fun d => decide (d.IsDiagAt i ∧ d.word = v)
      have hpmem : ∀ d ∈ (GenCode.diag i j a b :: L').filter p, d.ev = (GenCode.diag i j a b).ev ∧
          d.mat = Matrix.single i i v := by
        intro d hd
        have hpd : d.IsDiagAt i ∧ d.word = v := by
          have h := List.of_mem_filter hd
          simpa [p] using h
        have hvd := hL d (List.mem_of_mem_filter hd)
        cases d with
        | root _ _ _ => exact absurd hpd.1 id
        | diag i' j' a' b' =>
          obtain ⟨hi'', hw⟩ := hpd
          change i' = i at hi''
          change a' * b' = v at hw
          subst hi''
          obtain ⟨hij', ha', hb', hia', hib'⟩ := hvd
          refine ⟨?_, ?_⟩
          · change bracket (Steinberg.indexedRoot i' j' a') (Steinberg.indexedRoot j' i' b') =
              bracket (Steinberg.indexedRoot i' j a) (Steinberg.indexedRoot j i' b)
            rw [indexedRoot_of_ne hij', indexedRoot_of_ne hij'.symm, indexedRoot_of_ne hij,
              indexedRoot_of_ne hij.symm]
            exact hind i' j' j hij' hij a' ha' b' hb' a ha b hb
              (by rw [← hib']; exact Ne.symm hia') hσ hw
          · change Matrix.single i' i' (a' * b') = Matrix.single i' i' v
            rw [hw]
      have hcount : ((((GenCode.diag i j a b : GenCode K R) :: L').filter p).length : ZMod ℓ) = 0 := by
        let D := (GenCode.diag i j a b :: L').filter (fun d => decide (d.IsDiagAt i))
        let F : G.W →₀ ZMod ℓ := (D.map (fun d => if h : d.word ∈ G.W then
          Finsupp.single (⟨d.word, h⟩ : G.W) (1 : ZMod ℓ) else 0)).sum
        have hF : Finsupp.linearCombination (ZMod ℓ) (fun w : G.W => (w : R)) F = 0 := by
          have h := congrFun (congrFun hsum i) i
          rw [list_sum_apply, Matrix.zero_apply, List.map_map] at h
          rw [map_list_sum, List.map_map, ← h]
          have h2 : List.map ((fun M : Matrix (Fin K) (Fin K) R => M i i) ∘ GenCode.mat)
              (GenCode.diag i j a b :: L') =
              List.map (fun d => if d.IsDiagAt i then d.word else 0)
                (GenCode.diag i j a b :: L') := by
            apply List.map_congr_left
            intro d hd
            exact GenCode.mat_apply_diag i d (ValidCode.root_ne G P (hL d hd))
          rw [h2, sum_map_ite_filter]
          congr 1
          apply List.map_congr_left
          intro d hd
          simp only [Function.comp_apply]
          split_ifs with hw
          · rw [Finsupp.linearCombination_single, one_smul]
          · rw [map_zero]
            rcases G.word_mem_or_zero P (hL d (List.mem_of_mem_filter hd)) with h3 | h3
            · exact absurd h3 hw
            · exact h3.symm
        have hF0 := (linearIndependent_iff.mp hli) F hF
        have happ : F ⟨v, hv⟩ = 0 := by
          rw [hF0, Finsupp.coe_zero, Pi.zero_apply]
        rw [← happ]
        change _ = Finsupp.applyAddHom (⟨v, hv⟩ : G.W) F
        rw [map_list_sum, List.map_map]
        have h4 : List.map (⇑(Finsupp.applyAddHom (⟨v, hv⟩ : G.W)) ∘ fun d =>
            if h : d.word ∈ G.W then Finsupp.single (⟨d.word, h⟩ : G.W) (1 : ZMod ℓ) else 0) D =
            List.map (fun d => if d.word = v then (1 : ZMod ℓ) else 0) D := by
          apply List.map_congr_left
          intro d _
          simp only [Function.comp_apply, Finsupp.applyAddHom_apply]
          split_ifs with h5 h6 h6
          · simp [h6]
          · simp [h6]
          · exact absurd (h6 ▸ hv) h5
          · rfl
        rw [h4, sum_indicator_eq_length, List.filter_filter]
        congr 2
        apply List.filter_congr
        intro d _
        simp [p]
        exact Bool.and_comm _ _
      have hdvd : ℓ ∣ (((GenCode.diag i j a b : GenCode K R) :: L').filter p).length :=
        (ZMod.natCast_eq_zero_iff _ _).mp hcount
      apply rest p (by simp [p, GenCode.IsDiagAt, GenCode.word, v])
      · rw [List.prod_eq_pow_length _ _ (fun g hg => by
            obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hg
            exact (hpmem d hd).1), List.length_map]
        obtain ⟨k, hk⟩ := hdvd
        rw [hk, pow_mul, G.ev_pow_char P hK hcv, one_pow]
      · rw [List.sum_eq_length_nsmul _ _ (fun M hM => by
            obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hM
            exact (hpmem d hd).2), List.length_map]
        have hℓR : ((ℓ : ℕ) : R) = 0 := by
          rw [← map_natCast (algebraMap (ZMod ℓ) R), ZMod.natCast_self, map_zero]
        obtain ⟨k, hk⟩ := hdvd
        rw [Matrix.smul_single, hk, nsmul_eq_mul, Nat.cast_mul, hℓR, zero_mul, zero_mul,
          Matrix.single_zero]

/-- Manuscript Lemma 20.3, faithfulness: an element of the correction subgroup with identity
matrix is trivial. -/
theorem correction_faithful [Fact ℓ.Prime] (hK : 5 ≤ K) (hopp : G.OppositeCommute K)
    (hind : G.CutIndependent K) (hli : LinearIndependent (ZMod ℓ) (fun w : G.W => (w : R)))
    {u : Steinberg K R} (hu : u ∈ G.correction P) (hrep : Elementary.representation u = 1) :
    u = 1 := by
  obtain ⟨L, hL, rfl⟩ := G.exists_codes P hK hu
  apply G.prod_eq_one P hK hopp hind hli L hL
  have h := G.rep_prod P L hL
  rw [hrep, Units.val_one] at h
  simpa using h.symm

end PhaseGrading
end Kernel
end
end AllPrimeGroups
