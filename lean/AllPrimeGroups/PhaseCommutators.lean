import AllPrimeGroups.RootCalculus
import Mathlib.Logic.Relation
import Mathlib.Data.List.Basic
import Mathlib.Algebra.GroupWithZero.Basic

/-! Opposite-root commutators of long words with mismatched phases (manuscript Lemma 20.2).

The statement is proved for an abstract interface: an evaluation of literal words in a ring,
elementary replacements of bounded width, and phases of long nonzero words with the prefix,
suffix, replacement and mismatch properties of manuscript Section 19. Nothing here asserts
that the constructed algebra satisfies this interface.

For a word cut into two long nonzero parts whose outer phases differ, the commutator of the
two opposite roots does not depend on the cut, is unchanged by replacements, and is trivial
as soon as some word on a replacement path contains a factor that evaluates to zero. The last
assertion is the zero-product alternative; it is an identity in the group, not only in
matrices. -/

namespace AllPrimeGroups

namespace RootFamily
variable {ι R G : Type*} [Ring R] [Group G] (s : RootFamily ι R G)

/-- Shifting the cut of an opposite-root commutator, keeping the auxiliary index. -/
theorem shift_cut {i h j : ι} (hih : i ≠ h) (hhj : h ≠ j) (hij : i ≠ j)
    (a b c : R) (hca : c * a = 0) :
    bracket (s.x i j (a * b)) (s.x j i c) = bracket (s.x i j a) (s.x j i (b * c)) := by
  have h1 := s.move_cut hih hhj hij a b c hca
  have h2 := s.move_cut hih hhj hij a 1 (b * c) (by rw [mul_assoc, hca, mul_zero])
  rw [mul_one, one_mul] at h2
  exact h1.trans h2.symm

end RootFamily

/-- The combinatorial data of manuscript Sections 19 and 20: literal words evaluated in a
ring, elementary replacements, and phases of long nonzero words. -/
structure PhasedWords (α R Φ : Type*) [Ring R] where
  /-- The ring element of a literal word. -/
  ev : List α → R
  ev_append : ∀ u v, ev (u ++ v) = ev u * ev v
  /-- An elementary replacement of one factor by another. -/
  Rule : List α → List α → Prop
  rule_ev : ∀ {l r}, Rule l r → ev l = ev r
  rule_length : ∀ {l r}, Rule l r → l.length = r.length
  /-- A bound for the length of replaced factors. -/
  width : ℕ
  rule_width : ∀ {l r}, Rule l r → l.length ≤ width
  /-- The length threshold above which phases are defined. -/
  N : ℕ
  /-- The start phase. -/
  σ : List α → Φ
  /-- The end phase. -/
  τ : List α → Φ
  mismatch : ∀ {u v}, N ≤ u.length → N ≤ v.length → ev u ≠ 0 → ev v ≠ 0 → τ u ≠ σ v →
    ev u * ev v = 0
  σ_prefix : ∀ {u v}, N ≤ u.length → ev (u ++ v) ≠ 0 → σ (u ++ v) = σ u
  τ_suffix : ∀ {u v}, N ≤ v.length → ev (u ++ v) ≠ 0 → τ (u ++ v) = τ v
  σ_rule : ∀ {x l r y}, Rule l r → N ≤ (x ++ l ++ y).length → ev (x ++ l ++ y) ≠ 0 →
    σ (x ++ r ++ y) = σ (x ++ l ++ y)
  τ_rule : ∀ {x l r y}, Rule l r → N ≤ (x ++ l ++ y).length → ev (x ++ l ++ y) ≠ 0 →
    τ (x ++ r ++ y) = τ (x ++ l ++ y)

namespace PhasedWords
variable {α R Φ : Type*} [Ring R] (P : PhasedWords α R Φ)

/-- One replacement inside a word. -/
def Step (w w' : List α) : Prop :=
  ∃ x l r y, P.Rule l r ∧ w = x ++ l ++ y ∧ w' = x ++ r ++ y

theorem step_ev {w w' : List α} (h : P.Step w w') : P.ev w' = P.ev w := by
  obtain ⟨x, l, r, y, hr, rfl, rfl⟩ := h
  simp only [P.ev_append, P.rule_ev hr]

theorem step_length {w w' : List α} (h : P.Step w w') : w'.length = w.length := by
  obtain ⟨x, l, r, y, hr, rfl, rfl⟩ := h
  simp only [List.length_append, P.rule_length hr]

/-- A cut into two long nonzero parts whose outer phases differ. -/
structure Valid (u v : List α) : Prop where
  left_long : P.N ≤ u.length
  right_long : P.N ≤ v.length
  left_ne : P.ev u ≠ 0
  right_ne : P.ev v ≠ 0
  phase : P.σ u ≠ P.τ v

/-- Another cut of the same word into long nonzero parts is again valid. -/
theorem Valid.of_cut {u v u' v' : List α} (hv : P.Valid u v) (hw : u ++ v = u' ++ v')
    (hu' : P.N ≤ u'.length) (hv' : P.N ≤ v'.length) (hu0 : P.ev u' ≠ 0) (hv0 : P.ev v' ≠ 0) :
    P.Valid u' v' := by
  refine ⟨hu', hv', hu0, hv0, ?_⟩
  rcases List.append_eq_append_iff.mp hw with ⟨b, rfl, rfl⟩ | ⟨c, rfl, rfl⟩
  · rw [P.σ_prefix hv.left_long hu0, ← P.τ_suffix hv' hv.right_ne]
    exact hv.phase
  · rw [← P.σ_prefix hu' hv.left_ne, P.τ_suffix hv.right_long hv0]
    exact hv.phase

variable {ι G : Type*} [Group G] (s : RootFamily ι R G)

/-- The opposite-root commutator of a cut. -/
def cutValue (i j : ι) (u v : List α) : G :=
  bracket (s.x i j (P.ev u)) (s.x j i (P.ev v))

theorem cutValue_eq_one_of_left (i j : ι) {u v : List α} (h : P.ev u = 0) :
    cutValue P s i j u v = 1 := by
  unfold cutValue
  rw [h, s.zero]
  simp [bracket]

theorem cutValue_eq_one_of_right (i j : ι) {u v : List α} (h : P.ev v = 0) :
    cutValue P s i j u v = 1 := by
  unfold cutValue
  rw [h, s.zero]
  simp [bracket]

variable {i h j : ι} (hih : i ≠ h) (hhj : h ≠ j) (hij : i ≠ j)
include hih hhj hij

/-- The commutator of a valid cut does not depend on the auxiliary index. -/
theorem cutValue_index {u v : List α} (hv : P.Valid u v) :
    cutValue P s i j u v = cutValue P s i h u v := by
  have hca := P.mismatch hv.right_long hv.left_long hv.right_ne hv.left_ne hv.phase.symm
  have hm := s.move_cut hih hhj hij (P.ev u) 1 (P.ev v) hca
  simpa only [cutValue, mul_one, one_mul] using hm

/-- Cut independence: from a valid cut, the commutator is the same at every other cut of
the same word into long parts, whether or not those parts are nonzero. -/
theorem cutValue_eq_of_cut {u v u' v' : List α} (hv : P.Valid u v) (hw : u ++ v = u' ++ v')
    (hu' : P.N ≤ u'.length) (hv' : P.N ≤ v'.length) :
    cutValue P s i j u v = cutValue P s i j u' v' := by
  rcases List.append_eq_append_iff.mp hw with ⟨b, rfl, rfl⟩ | ⟨c, rfl, rfl⟩
  · have hv0 : P.ev v' ≠ 0 := by
      have hr := hv.right_ne
      rw [P.ev_append] at hr
      exact right_ne_zero_of_mul hr
    have hτ : P.τ v' ≠ P.σ u := by
      rw [← P.τ_suffix hv' hv.right_ne]
      exact hv.phase.symm
    have hca := P.mismatch hv' hv.left_long hv0 hv.left_ne hτ
    unfold cutValue
    rw [P.ev_append, P.ev_append]
    exact (s.shift_cut hih hhj hij _ _ _ hca).symm
  · have hu0 : P.ev u' ≠ 0 := by
      have hl := hv.left_ne
      rw [P.ev_append] at hl
      exact left_ne_zero_of_mul hl
    have hτ : P.τ v ≠ P.σ u' := by
      rw [← P.σ_prefix hu' hv.left_ne]
      exact hv.phase.symm
    have hca := P.mismatch hv.right_long hu' hv.right_ne hu0 hτ
    unfold cutValue
    rw [P.ev_append, P.ev_append]
    exact s.shift_cut hih hhj hij _ _ _ hca

/-- Moving to a cut whose right part is then replaced by a part with the same value. -/
theorem transfer_right {u v a t t' : List α} (hv : P.Valid u v) (hcut : u ++ v = a ++ t)
    (ha : P.N ≤ a.length) (ht : P.N ≤ t.length) (hlen : t'.length = t.length)
    (hev : P.ev t' = P.ev t) (hτ : P.ev t ≠ 0 → P.τ t' = P.τ t) :
    cutValue P s i j u v = cutValue P s i j a t' ∧
      (P.ev a ≠ 0 → P.ev t' ≠ 0 → P.Valid a t') := by
  constructor
  · rw [cutValue_eq_of_cut P s hih hhj hij hv hcut ha ht]
    unfold cutValue
    rw [hev]
  · intro ha0 ht0
    have ht0' : P.ev t ≠ 0 := by
      rw [← hev]
      exact ht0
    have hvalid := hv.of_cut P hcut ha ht ha0 ht0'
    refine ⟨ha, by omega, ha0, ht0, ?_⟩
    rw [hτ ht0']
    exact hvalid.phase

/-- Moving to a cut whose left part is then replaced by a part with the same value. -/
theorem transfer_left {u v t t' c : List α} (hv : P.Valid u v) (hcut : u ++ v = t ++ c)
    (ht : P.N ≤ t.length) (hc : P.N ≤ c.length) (hlen : t'.length = t.length)
    (hev : P.ev t' = P.ev t) (hσ : P.ev t ≠ 0 → P.σ t' = P.σ t) :
    cutValue P s i j u v = cutValue P s i j t' c ∧
      (P.ev t' ≠ 0 → P.ev c ≠ 0 → P.Valid t' c) := by
  constructor
  · rw [cutValue_eq_of_cut P s hih hhj hij hv hcut ht hc]
    unfold cutValue
    rw [hev]
  · intro ht0 hc0
    have ht0' : P.ev t ≠ 0 := by
      rw [← hev]
      exact ht0
    have hvalid := hv.of_cut P hcut ht hc ht0' hc0
    refine ⟨by omega, hc, ht0, hc0, ?_⟩
    rw [hσ ht0']
    exact hvalid.phase

/-- A valid cut is carried across one replacement, by first moving the cut away from the
replaced factor. -/
theorem step_transfer {w w₁ u v : List α} (hstep : P.Step w w₁)
    (hlen : 2 * P.N + P.width ≤ w.length) (hv : P.Valid u v) (huv : u ++ v = w) :
    ∃ u₁ v₁, u₁ ++ v₁ = w₁ ∧ cutValue P s i j u v = cutValue P s i j u₁ v₁ ∧
      (P.ev u₁ ≠ 0 → P.ev v₁ ≠ 0 → P.Valid u₁ v₁) := by
  obtain ⟨x, l, r, y, hr, rfl, rfl⟩ := hstep
  have hl := P.rule_length hr
  have hwd := P.rule_width hr
  simp only [List.length_append] at hlen
  by_cases hx : P.N ≤ x.length
  · obtain ⟨x₁, x₂, rfl, hx₁⟩ : ∃ x₁ x₂, x = x₁ ++ x₂ ∧ x₁.length = P.N :=
      ⟨x.take P.N, x.drop P.N, (List.take_append_drop _ _).symm, List.length_take_of_le hx⟩
    simp only [List.length_append] at hlen
    have ht : P.N ≤ (x₂ ++ l ++ y).length := by
      simp only [List.length_append]
      omega
    obtain ⟨h1, h2⟩ := transfer_right P s hih hhj hij (a := x₁) (t := x₂ ++ l ++ y)
      (t' := x₂ ++ r ++ y) hv
      (by rw [huv]; simp only [List.append_assoc]) (by omega) ht
      (by simp only [List.length_append]; omega)
      (by simp only [P.ev_append, P.rule_ev hr])
      (fun h0 => P.τ_rule hr ht h0)
    exact ⟨x₁, x₂ ++ r ++ y, by simp only [List.append_assoc], h1, h2⟩
  · obtain ⟨y₁, y₂, rfl, hy₂⟩ : ∃ y₁ y₂, y = y₁ ++ y₂ ∧ y₂.length = P.N :=
      ⟨y.take (y.length - P.N), y.drop (y.length - P.N), (List.take_append_drop _ _).symm, by
        rw [List.length_drop]
        omega⟩
    simp only [List.length_append] at hlen
    have ht : P.N ≤ (x ++ l ++ y₁).length := by
      simp only [List.length_append]
      omega
    obtain ⟨h1, h2⟩ := transfer_left P s hih hhj hij (t := x ++ l ++ y₁)
      (t' := x ++ r ++ y₁) (c := y₂) hv
      (by rw [huv]; simp only [List.append_assoc]) ht (by omega)
      (by simp only [List.length_append]; omega)
      (by simp only [P.ev_append, P.rule_ev hr])
      (fun h0 => P.σ_rule hr ht h0)
    exact ⟨x ++ r ++ y₁, y₂, by simp only [List.append_assoc], h1, h2⟩

/-- A valid cut of a word containing a short factor that evaluates to zero has trivial
commutator. -/
theorem cutValue_eq_one_of_zero_factor {u v x z y : List α} (hv : P.Valid u v)
    (huv : u ++ v = x ++ z ++ y) (hz : P.ev z = 0) (hzw : z.length ≤ P.width)
    (hlen : 2 * P.N + P.width ≤ (x ++ z ++ y).length) : cutValue P s i j u v = 1 := by
  simp only [List.length_append] at hlen
  by_cases hx : P.N ≤ x.length
  · obtain ⟨x₁, x₂, rfl, hx₁⟩ : ∃ x₁ x₂, x = x₁ ++ x₂ ∧ x₁.length = P.N :=
      ⟨x.take P.N, x.drop P.N, (List.take_append_drop _ _).symm, List.length_take_of_le hx⟩
    simp only [List.length_append] at hlen
    rw [cutValue_eq_of_cut P s hih hhj hij hv (u' := x₁) (v' := x₂ ++ z ++ y)
      (by rw [huv]; simp only [List.append_assoc]) (by omega)
      (by simp only [List.length_append]; omega)]
    apply cutValue_eq_one_of_right
    simp only [P.ev_append, hz, mul_zero, zero_mul]
  · obtain ⟨y₁, y₂, rfl, hy₂⟩ : ∃ y₁ y₂, y = y₁ ++ y₂ ∧ y₂.length = P.N :=
      ⟨y.take (y.length - P.N), y.drop (y.length - P.N), (List.take_append_drop _ _).symm, by
        rw [List.length_drop]
        omega⟩
    simp only [List.length_append] at hlen
    rw [cutValue_eq_of_cut P s hih hhj hij hv (u' := x ++ z ++ y₁) (v' := y₂)
      (by rw [huv]; simp only [List.append_assoc])
      (by simp only [List.length_append]; omega) (by omega)]
    apply cutValue_eq_one_of_left
    simp only [P.ev_append, hz, mul_zero, zero_mul]

/-- The zero-product alternative along a replacement path that ends at a word with a short
zero factor. -/
theorem cutValue_eq_one_of_path {w w' : List α} (hpath : Relation.ReflTransGen P.Step w w')
    (hzero : ∃ x z y, w' = x ++ z ++ y ∧ P.ev z = 0 ∧ z.length ≤ P.width) :
    2 * P.N + P.width ≤ w.length → ∀ u v, P.Valid u v → u ++ v = w →
      cutValue P s i j u v = 1 := by
  induction hpath using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro hlen u v hv huv
    obtain ⟨x, z, y, rfl, hz, hzw⟩ := hzero
    exact cutValue_eq_one_of_zero_factor P s hih hhj hij hv huv hz hzw hlen
  | head hstep _ ih =>
    intro hlen u v hv huv
    obtain ⟨u₁, v₁, huv₁, hval, hvalid⟩ := step_transfer P s hih hhj hij hstep hlen hv huv
    rw [hval]
    by_cases hu0 : P.ev u₁ = 0
    · exact cutValue_eq_one_of_left P s i j hu0
    by_cases hv0 : P.ev v₁ = 0
    · exact cutValue_eq_one_of_right P s i j hv0
    exact ih (by rw [P.step_length hstep]; exact hlen) u₁ v₁ (hvalid hu0 hv0) huv₁

/-- Independence of the representative along a replacement path of nonzero words. -/
theorem cutValue_eq_of_path {w w' : List α} (hpath : Relation.ReflTransGen P.Step w w') :
    P.ev w ≠ 0 → 2 * P.N + P.width ≤ w.length → ∀ u v u' v', P.Valid u v → u ++ v = w →
      P.Valid u' v' → u' ++ v' = w' → cutValue P s i j u v = cutValue P s i j u' v' := by
  induction hpath using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro _ _ u v u' v' hv huv hv' huv'
    exact cutValue_eq_of_cut P s hih hhj hij hv (huv.trans huv'.symm) hv'.left_long hv'.right_long
  | head hstep _ ih =>
    intro hne hlen u v u' v' hv huv hv' huv'
    obtain ⟨u₁, v₁, huv₁, hval, hvalid⟩ := step_transfer P s hih hhj hij hstep hlen hv huv
    have hne₁ := hne
    rw [← P.step_ev hstep] at hne₁
    have hprod : P.ev u₁ * P.ev v₁ ≠ 0 := by
      rw [← P.ev_append, huv₁]
      exact hne₁
    rw [hval]
    exact ih hne₁ (by rw [P.step_length hstep]; exact hlen) u₁ v₁ u' v'
      (hvalid (left_ne_zero_of_mul hprod) (right_ne_zero_of_mul hprod)) huv₁ hv' huv'

/-- Manuscript Lemma 20.2, zero alternative: if the product of the two parts of a valid cut
is zero and vanishing words are connected to words with a short zero factor, the opposite
roots commute. -/
theorem cutValue_eq_one_of_mul_eq_zero
    (hvanish : ∀ w, P.ev w = 0 → ∃ w', Relation.ReflTransGen P.Step w w' ∧
      ∃ x z y, w' = x ++ z ++ y ∧ P.ev z = 0 ∧ z.length ≤ P.width)
    {u v : List α} (hv : P.Valid u v) (hlen : 2 * P.N + P.width ≤ u.length + v.length)
    (h0 : P.ev u * P.ev v = 0) : cutValue P s i j u v = 1 := by
  obtain ⟨w', hpath, hzero⟩ := hvanish (u ++ v) (by rw [P.ev_append, h0])
  exact cutValue_eq_one_of_path P s hih hhj hij hpath hzero
    (by rw [List.length_append]; exact hlen) u v hv rfl

/-- Manuscript Lemma 20.2, nonzero case: the commutator of a valid cut depends only on the
ring element of the whole word, provided words with the same nonzero value are connected by
replacements. -/
theorem cutValue_eq_of_mul_eq
    (hconn : ∀ w w', P.ev w = P.ev w' → P.ev w ≠ 0 → Relation.ReflTransGen P.Step w w')
    {u v u' v' : List α} (hv : P.Valid u v) (hv' : P.Valid u' v')
    (hlen : 2 * P.N + P.width ≤ u.length + v.length)
    (heq : P.ev u * P.ev v = P.ev u' * P.ev v') (hne : P.ev u * P.ev v ≠ 0) :
    cutValue P s i j u v = cutValue P s i j u' v' := by
  have hne' : P.ev (u ++ v) ≠ 0 := by rw [P.ev_append]; exact hne
  have hpath := hconn (u ++ v) (u' ++ v') (by rw [P.ev_append, P.ev_append, heq]) hne'
  exact cutValue_eq_of_path P s hih hhj hij hpath hne'
    (by rw [List.length_append]; exact hlen) u v u' v' hv rfl hv' rfl

end PhasedWords
end AllPrimeGroups
