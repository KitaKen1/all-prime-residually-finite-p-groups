/-
Monomial root words and the lift out of the free-algebra Steinberg group, adapted from
OpenAI PeriodicGroups/Steinberg/MonomialPresentation.lean (commit pinned in
upstream/provenance.json; Apache-2.0, see upstream/OpenAI-LICENSE).

The upstream file is written for the two-element field: root words square to the identity
and polynomial coefficients are 0 or 1. Here the coefficient field is `ZMod ℓ`, the relation
is "ℓ-th powers are trivial", and a coefficient acts by the corresponding power.
The reassociation and cut-independence arguments are the upstream ones.
-/
import AllPrimeGroups.SteinbergCore
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Card
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.Subgroup.Centralizer

namespace AllPrimeGroups
universe u v

theorem exists_fresh {n : ℕ} (hn : 5 ≤ n) (i j k l : Fin n) :
    ∃ a : Fin n, a ≠ i ∧ a ≠ j ∧ a ≠ k ∧ a ≠ l := by
  have hcard : ({i, j, k, l} : Finset (Fin n)).card < (Finset.univ : Finset (Fin n)).card := by
    have := (Finset.card_le_four : ({i, j, k, l} : Finset (Fin n)).card ≤ 4)
    simpa using (lt_of_le_of_lt this (show 4 < n by omega))
  obtain ⟨a, _, ha⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  exact ⟨a, by simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using ha⟩

/-- If a commutator commutes with its first entry, powers pass through that entry. -/
theorem bracket_pow_eq_one {G : Type v} [Group G] {a b : G} (ℓ : ℕ) (ha : a ^ ℓ = 1)
    (hc : Commute (bracket a b) a) : bracket a b ^ ℓ = 1 := by
  have hp := hc.symm.commutatorElement_pow_left ℓ
  change bracket a b ^ ℓ = bracket (a ^ ℓ) b at hp
  rw [ha] at hp
  simpa [bracket] using hp

namespace MonomialCompletion

variable {ℓ n : ℕ} {α : Type u} {G : Type v} [Group G]

/-- Root elements for words of length at most two, with the relations among them. -/
structure Seed (ℓ n : ℕ) (α : Type u) (G : Type v) [Group G] where
  g : Root n → List α → G
  power : ∀ p w, w.length ≤ 2 → g p w ^ ℓ = 1
  commute : ∀ p q u v, u.length ≤ 2 → v.length ≤ 2 →
    p.col ≠ q.row → p.row ≠ q.col → Commute (g p u) (g q v)
  product : ∀ (i j k : Fin n) hij hjk hik (u v : List α),
    u.length + v.length ≤ 2 →
    bracket (g ⟨i, j, hij⟩ u) (g ⟨j, k, hjk⟩ v) = g ⟨i, k, hik⟩ (u ++ v)

noncomputable def middle (hn : 5 ≤ n) (p : Root n) : Fin n :=
  (exists_fresh hn p.row p.col p.row p.col).choose

theorem middle_ne_row (hn : 5 ≤ n) (p : Root n) : middle hn p ≠ p.row :=
  (exists_fresh hn p.row p.col p.row p.col).choose_spec.1

theorem middle_ne_col (hn : 5 ≤ n) (p : Root n) : middle hn p ≠ p.col :=
  (exists_fresh hn p.row p.col p.row p.col).choose_spec.2.1

noncomputable def word (s : Seed ℓ n α G) (hn : 5 ≤ n) (p : Root n) : List α → G
  | [] => s.g p []
  | [a] => s.g p [a]
  | [a, b] => s.g p [a, b]
  | a :: b :: c :: w =>
    bracket (s.g ⟨p.row, middle hn p, (middle_ne_row hn p).symm⟩ [a])
      (word s hn ⟨middle hn p, p.col, middle_ne_col hn p⟩ (b :: c :: w))

theorem word_short (s : Seed ℓ n α G) (hn : 5 ≤ n) (p : Root n) (w : List α)
    (hw : w.length ≤ 2) : word s hn p w = s.g p w := by
  match w with
  | [] | [_] | [_, _] => rfl
  | _ :: _ :: _ :: _ => simp only [List.length_cons] at hw; omega

theorem word_long (s : Seed ℓ n α G) (hn : 5 ≤ n) (p : Root n) (a : α) (v : List α)
    (hv : 2 ≤ v.length) :
    word s hn p (a :: v) =
      bracket (word s hn ⟨p.row, middle hn p, (middle_ne_row hn p).symm⟩ [a])
        (word s hn ⟨middle hn p, p.col, middle_ne_col hn p⟩ v) := by
  match v with
  | [] | [_] => simp only [List.length_cons, List.length_nil] at hv; omega
  | _ :: _ :: _ => rfl

abbrev RootWords (n : ℕ) (α : Type u) (G : Type v) := Root n → List α → G

def ProductUpTo (y : RootWords n α G) (N : ℕ) : Prop :=
  ∀ (i j k : Fin n) hij hjk hik (u v : List α), u.length + v.length ≤ N →
    bracket (y ⟨i, j, hij⟩ u) (y ⟨j, k, hjk⟩ v) = y ⟨i, k, hik⟩ (u ++ v)

def CommuteUpTo (y : RootWords n α G) (N : ℕ) : Prop :=
  ∀ p q u v, u.length ≤ N → v.length ≤ N → p.col ≠ q.row → p.row ≠ q.col →
    Commute (y p u) (y q v)

def PowersUpTo (ℓ : ℕ) (y : RootWords n α G) (N : ℕ) : Prop :=
  ∀ p w, w.length ≤ N → y p w ^ ℓ = 1

def Good (ℓ : ℕ) (y : RootWords n α G) (N : ℕ) : Prop :=
  ProductUpTo y N ∧ CommuteUpTo y N ∧ PowersUpTo ℓ y N

theorem base_good (s : Seed ℓ n α G) (hn : 5 ≤ n) (N : ℕ) (hN : N ≤ 2) :
    Good ℓ (word s hn) N := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j k hij hjk hik u v huv
    rw [word_short _ _ _ _ (by omega), word_short _ _ _ _ (by omega),
      word_short _ _ _ _ (by simp only [List.length_append]; omega)]
    exact s.product i j k hij hjk hik u v (by omega)
  · intro p q u v hu hv h₁ h₂
    rw [word_short _ _ _ _ (by omega), word_short _ _ _ _ (by omega)]
    exact s.commute p q u v (by omega) (by omega) h₁ h₂
  · intro p w hw
    rw [word_short _ _ _ _ (by omega)]
    exact s.power p w (by omega)

theorem reassociate_of (y : RootWords n α G) {M : ℕ}
    (hc : CommuteUpTo y M)
    (i a b j : Fin n) (hia : i ≠ a) (hib : i ≠ b) (hij : i ≠ j)
    (hab : a ≠ b) (haj : a ≠ j) (hbj : b ≠ j)
    (u v z : List α) (huv : u.length + v.length ≤ M) (hvz : v.length + z.length ≤ M)
    (hA : bracket (y ⟨i, a, hia⟩ u) (y ⟨a, b, hab⟩ v) = y ⟨i, b, hib⟩ (u ++ v))
    (hB : bracket (y ⟨a, b, hab⟩ v) (y ⟨b, j, hbj⟩ z) = y ⟨a, j, haj⟩ (v ++ z)) :
    bracket (y ⟨i, b, hib⟩ (u ++ v)) (y ⟨b, j, hbj⟩ z) =
      bracket (y ⟨i, a, hia⟩ u) (y ⟨a, j, haj⟩ (v ++ z)) := by
  have h := CommutatorCalculus.three_factor
    (y ⟨i, a, hia⟩ u) (y ⟨a, b, hab⟩ v) (y ⟨b, j, hbj⟩ z)
    (by rw [hA]; exact hc _ _ _ _ (by simp only [List.length_append]; omega) (by omega) hib.symm hia)
    (by rw [hA]; exact hc _ _ _ _ (by simp only [List.length_append]; omega) (by omega) hab.symm hib)
    (by rw [hB]; exact hc _ _ _ _ (by simp only [List.length_append]; omega) (by omega) haj.symm hab)
    (by rw [hB]; exact hc _ _ _ _ (by simp only [List.length_append]; omega) (by omega) hbj.symm haj)
    (by
      rw [hA, hB]
      exact hc _ _ _ _ (by simp only [List.length_append]; omega)
        (by simp only [List.length_append]; omega) hab.symm hij)
    (hc _ _ _ _ (by omega) (by omega) hab hij)
  simpa only [hA, hB] using h.1

theorem reassociate (y : RootWords n α G) {M : ℕ}
    (hp : ProductUpTo y M) (hc : CommuteUpTo y M)
    (i a b j : Fin n) (hia : i ≠ a) (hib : i ≠ b) (hij : i ≠ j)
    (hab : a ≠ b) (haj : a ≠ j) (hbj : b ≠ j)
    (u v z : List α) (huv : u.length + v.length ≤ M) (hvz : v.length + z.length ≤ M) :
    bracket (y ⟨i, b, hib⟩ (u ++ v)) (y ⟨b, j, hbj⟩ z) =
      bracket (y ⟨i, a, hia⟩ u) (y ⟨a, j, haj⟩ (v ++ z)) :=
  reassociate_of y hc i a b j hia hib hij hab haj hbj u v z huv hvz
    (hp i a b hia hab hib u v huv) (hp a b j hab hbj haj v z hvz)

theorem first_cut_independent (y : RootWords n α G) (hn : 5 ≤ n) {M : ℕ}
    (hp : ProductUpTo y M) (hc : CommuteUpTo y M)
    (i j h h' : Fin n) (hij : i ≠ j) (hih : i ≠ h) (hhj : h ≠ j)
    (hih' : i ≠ h') (hh'j : h' ≠ j) (a b : α) (v : List α)
    (hM : 2 ≤ M) (hv : 1 + v.length ≤ M) :
    bracket (y ⟨i, h, hih⟩ [a]) (y ⟨h, j, hhj⟩ (b :: v)) =
      bracket (y ⟨i, h', hih'⟩ [a]) (y ⟨h', j, hh'j⟩ (b :: v)) := by
  obtain ⟨c, hci, hcj, hch, hch'⟩ := exists_fresh hn i j h h'
  have h₁ := reassociate y hp hc i h c j hih hci.symm hij hch.symm hhj hcj
    [a] [b] v (by simpa) (by simpa [Nat.add_comm] using hv)
  have h₂ := reassociate y hp hc i h' c j hih' hci.symm hij hch'.symm hh'j hcj
    [a] [b] v (by simpa) (by simpa [Nat.add_comm] using hv)
  simpa using h₁.symm.trans h₂

theorem first_cut_next (s : Seed ℓ n α G) (hn : 5 ≤ n) {M : ℕ}
    (hp : ProductUpTo (word s hn) M) (hc : CommuteUpTo (word s hn) M)
    (i h j : Fin n) (hih : i ≠ h) (hhj : h ≠ j) (hij : i ≠ j)
    (a : α) (v : List α) (hv₂ : 2 ≤ v.length) (hvM : v.length ≤ M) :
    bracket (word s hn ⟨i, h, hih⟩ [a]) (word s hn ⟨h, j, hhj⟩ v) =
      word s hn ⟨i, j, hij⟩ (a :: v) := by
  rw [word_long _ _ _ _ _ hv₂]
  cases v with
  | nil => simp at hv₂
  | cons b v =>
    exact first_cut_independent _ hn hp hc i j h (middle hn ⟨i, j, hij⟩)
      hij hih hhj (middle_ne_row hn ⟨i, j, hij⟩).symm (middle_ne_col hn ⟨i, j, hij⟩) a b v
      (by omega) (by simpa [Nat.add_comm] using hvM)

theorem positive_next (s : Seed ℓ n α G) (hn : 5 ≤ n) {M : ℕ} (hM : 2 ≤ M)
    (hp : ProductUpTo (word s hn) M) (hc : CommuteUpTo (word s hn) M)
    (i h j : Fin n) (hih : i ≠ h) (hhj : h ≠ j) (hij : i ≠ j)
    (u v : List α) (hu : 0 < u.length) (hv : 0 < v.length)
    (huv : u.length + v.length ≤ M + 1) :
    bracket (word s hn ⟨i, h, hih⟩ u) (word s hn ⟨h, j, hhj⟩ v) =
      word s hn ⟨i, j, hij⟩ (u ++ v) := by
  by_cases hsmall : u.length + v.length ≤ M
  · exact hp i h j hih hhj hij u v hsmall
  cases u with
  | nil => simp at hu
  | cons a u =>
    cases u with
    | nil =>
      exact first_cut_next s hn hp hc i h j hih hhj hij a v
        (by simp only [List.length_cons, List.length_nil] at hsmall; omega)
        (by simp only [List.length_cons, List.length_nil] at huv; omega)
    | cons b u =>
      obtain ⟨c, hci, hcj, hch, _⟩ := exists_fresh hn i j h h
      have hassoc := reassociate (word s hn) hp hc i c h j hci.symm hih hij
        hch hcj hhj [a] (b :: u) v
        (by simp only [List.length_cons, List.length_nil] at *; omega)
        (by simp only [List.length_cons] at *; omega)
      calc
        bracket (word s hn ⟨i, h, hih⟩ (a :: b :: u)) (word s hn ⟨h, j, hhj⟩ v) =
            bracket (word s hn ⟨i, c, hci.symm⟩ [a])
              (word s hn ⟨c, j, hcj⟩ ((b :: u) ++ v)) := hassoc
        _ = word s hn ⟨i, j, hij⟩ ((a :: b :: u) ++ v) :=
          first_cut_next s hn hp hc i c j hci.symm hcj hij a ((b :: u) ++ v)
            (by simp only [List.length_cons, List.length_append] at *; omega)
            (by simp only [List.length_cons, List.length_append] at *; omega)

theorem commute_next_short (s : Seed ℓ n α G) (hn : 5 ≤ n) {M : ℕ} (hM : 2 ≤ M)
    (hp : ProductUpTo (word s hn) M) (hc : CommuteUpTo (word s hn) M)
    (p q : Root n) (u v : List α) (hu : u.length ≤ M + 1) (hv : v.length ≤ M)
    (hpq : p.col ≠ q.row) (hqp : p.row ≠ q.col) :
    Commute (word s hn p u) (word s hn q v) := by
  by_cases hus : u.length ≤ M
  · exact hc p q u v hus hv hpq hqp
  cases u with
  | nil => simp at hus
  | cons a u =>
    obtain ⟨c, hci, hcj, hck, hcl⟩ := exists_fresh hn p.row p.col q.row q.col
    have he := positive_next s hn hM hp hc p.row c p.col hci.symm hcj p.ne
      [a] u (by simp) (by simp only [List.length_cons] at hus; omega)
      (by simp only [List.length_cons, List.length_nil] at *; omega)
    rw [show word s hn p (a :: u) =
      bracket (word s hn ⟨p.row, c, hci.symm⟩ [a]) (word s hn ⟨c, p.col, hcj⟩ u) from he.symm]
    apply CommutatorCalculus.commute_bracket_left
    · exact hc _ _ _ _ (by simp; omega) hv hck hqp
    · exact hc _ _ _ _ (by simp only [List.length_cons] at hu; omega) hv hpq hcl

theorem commute_next (s : Seed ℓ n α G) (hn : 5 ≤ n) {M : ℕ} (hM : 2 ≤ M)
    (hp : ProductUpTo (word s hn) M) (hc : CommuteUpTo (word s hn) M) :
    CommuteUpTo (word s hn) (M + 1) := by
  intro p q u v hu hv hpq hqp
  by_cases hus : u.length ≤ M
  · exact (commute_next_short s hn hM hp hc q p v u hv hus hqp.symm hpq.symm).symm
  cases u with
  | nil => simp at hus
  | cons a u =>
    obtain ⟨c, hci, hcj, hck, hcl⟩ := exists_fresh hn p.row p.col q.row q.col
    have he := positive_next s hn hM hp hc p.row c p.col hci.symm hcj p.ne
      [a] u (by simp) (by simp only [List.length_cons] at hus; omega)
      (by simp only [List.length_cons, List.length_nil] at *; omega)
    rw [show word s hn p (a :: u) =
      bracket (word s hn ⟨p.row, c, hci.symm⟩ [a]) (word s hn ⟨c, p.col, hcj⟩ u) from he.symm]
    apply CommutatorCalculus.commute_bracket_left
    · exact (commute_next_short s hn hM hp hc q ⟨p.row, c, hci.symm⟩ v [a] hv (by simp; omega)
        hqp.symm hck.symm).symm
    · exact (commute_next_short s hn hM hp hc q ⟨c, p.col, hcj⟩ v u hv
        (by simp only [List.length_cons] at hu; omega) hcl.symm hpq.symm).symm

theorem powers_next (s : Seed ℓ n α G) (hn : 5 ≤ n) {M : ℕ} (hM : 2 ≤ M)
    (hp : ProductUpTo (word s hn) M) (hc : CommuteUpTo (word s hn) M)
    (hs : PowersUpTo ℓ (word s hn) M) : PowersUpTo ℓ (word s hn) (M + 1) := by
  intro p u hu
  by_cases hus : u.length ≤ M
  · exact hs p u hus
  cases u with
  | nil => simp at hus
  | cons a u =>
    let c := middle hn p
    have hci : c ≠ p.row := middle_ne_row hn p
    have hcj : c ≠ p.col := middle_ne_col hn p
    have he := positive_next s hn hM hp hc p.row c p.col hci.symm hcj p.ne
      [a] u (by simp) (by simp only [List.length_cons] at hus; omega)
      (by simp only [List.length_cons, List.length_nil] at *; omega)
    have he' : word s hn p (a :: u) =
      bracket (word s hn ⟨p.row, c, hci.symm⟩ [a]) (word s hn ⟨c, p.col, hcj⟩ u) := he.symm
    rw [he']
    apply bracket_pow_eq_one ℓ (hs _ _ (by simp; omega))
    rw [← he']
    exact commute_next s hn hM hp hc p ⟨p.row, c, hci.symm⟩ _ _ hu
      (by simp only [List.length_cons, List.length_nil]; omega) p.ne.symm hci.symm

theorem product_next (s : Seed ℓ n α G) (hn : 5 ≤ n) {M : ℕ} (hM : 2 ≤ M)
    (hp : ProductUpTo (word s hn) M) (hc : CommuteUpTo (word s hn) M) :
    ProductUpTo (word s hn) (M + 1) := by
  intro i j k hij hjk hik u v huv
  by_cases hsmall : u.length + v.length ≤ M
  · exact hp i j k hij hjk hik u v hsmall
  have hc' := commute_next s hn hM hp hc
  cases u with
  | nil =>
    cases v with
    | nil => simp at hsmall
    | cons a v =>
      obtain ⟨c, hci, hcj, hck, _⟩ := exists_fresh hn i j k k
      have hv : 0 < v.length := by simp only [List.length_nil, List.length_cons] at hsmall; omega
      have hvl : v.length ≤ M := by simp only [List.length_nil, List.length_cons] at huv; omega
      have hpos := positive_next s hn hM hp hc j c k hcj.symm hck hjk [a] v
        (by simp) hv (by simp only [List.length_cons, List.length_nil] at *; omega)
      have hassoc := reassociate_of (word s hn) hc' i j c k hij hci.symm hik
        hcj.symm hjk hck [] [a] v
        (by simp only [List.length_nil, List.length_cons]; omega)
        (by simp only [List.length_nil, List.length_cons] at *; omega)
        (hp i j c hij hcj.symm hci.symm [] [a] (by simp; omega)) hpos
      calc
        bracket (word s hn ⟨i, j, hij⟩ []) (word s hn ⟨j, k, hjk⟩ (a :: v)) =
            bracket (word s hn ⟨i, c, hci.symm⟩ [a]) (word s hn ⟨c, k, hck⟩ v) := by
              simpa using hassoc.symm
        _ = word s hn ⟨i, k, hik⟩ ([] ++ a :: v) :=
          positive_next s hn hM hp hc i c k hci.symm hck hik [a] v (by simp) hv
            (by simp only [List.length_nil, List.length_cons] at *; omega)
  | cons a u =>
    cases v with
    | nil =>
      obtain ⟨c, hci, hcj, hck, _⟩ := exists_fresh hn i j k k
      have hu : 0 < u.length := by simp only [List.length_nil, List.length_cons] at hsmall; omega
      have hul : u.length ≤ M := by simp only [List.length_nil, List.length_cons] at huv; omega
      have hpos := positive_next s hn hM hp hc i c j hci.symm hcj hij [a] u
        (by simp) hu (by simp only [List.length_cons, List.length_nil] at *; omega)
      have hassoc := reassociate_of (word s hn) hc' i c j k hci.symm hij hik
        hcj hck hjk [a] u []
        (by simp only [List.length_nil, List.length_cons] at *; omega)
        (by simp only [List.length_nil]; omega)
        hpos (hp c j k hcj hjk hck u [] (by simpa using hul))
      calc
        bracket (word s hn ⟨i, j, hij⟩ (a :: u)) (word s hn ⟨j, k, hjk⟩ []) =
            bracket (word s hn ⟨i, c, hci.symm⟩ [a]) (word s hn ⟨c, k, hck⟩ u) := by
              simpa using hassoc
        _ = word s hn ⟨i, k, hik⟩ ((a :: u) ++ []) := by
          simpa using positive_next s hn hM hp hc i c k hci.symm hck hik [a] u
            (by simp) hu (by simp only [List.length_cons, List.length_nil] at *; omega)
    | cons b v =>
      exact positive_next s hn hM hp hc i j k hij hjk hik (a :: u) (b :: v)
        (by simp) (by simp) huv

theorem good (s : Seed ℓ n α G) (hn : 5 ≤ n) (N : ℕ) : Good ℓ (word s hn) N := by
  induction N with
  | zero => exact base_good s hn 0 (by omega)
  | succ M ih =>
    by_cases hM : M < 2
    · exact base_good s hn (M + 1) (by omega)
    · exact ⟨product_next s hn (by omega) ih.1 ih.2.1,
        commute_next s hn (by omega) ih.1 ih.2.1,
        powers_next s hn (by omega) ih.1 ih.2.1 ih.2.2⟩

theorem product (s : Seed ℓ n α G) (hn : 5 ≤ n)
    (i j k : Fin n) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (u v : List α) :
    bracket (word s hn ⟨i, j, hij⟩ u) (word s hn ⟨j, k, hjk⟩ v) =
      word s hn ⟨i, k, hik⟩ (u ++ v) :=
  (good s hn (u.length + v.length)).1 i j k hij hjk hik u v le_rfl

theorem commute (s : Seed ℓ n α G) (hn : 5 ≤ n)
    (p q : Root n) (u v : List α) (hpq : p.col ≠ q.row) (hqp : p.row ≠ q.col) :
    Commute (word s hn p u) (word s hn q v) :=
  (good s hn (max u.length v.length)).2.1 p q u v (le_max_left _ _) (le_max_right _ _) hpq hqp

theorem power (s : Seed ℓ n α G) (hn : 5 ≤ n) (p : Root n) (u : List α) :
    word s hn p u ^ ℓ = 1 := (good s hn u.length).2.2 p u le_rfl

/-- Noncommutative polynomials over the prime field. -/
abbrev Polynomial (ℓ : ℕ) (α : Type u) := MonoidAlgebra (ZMod ℓ) (FreeMonoid α)

/-- Additive statements about polynomials over `ZMod ℓ` reduce to monomials with
coefficient one. -/
theorem polynomial_induction [NeZero ℓ] {motive : Polynomial ℓ α → Prop}
    (zero : motive 0) (add : ∀ f g, motive f → motive g → motive (f + g))
    (monomial : ∀ w : FreeMonoid α, motive (MonoidAlgebra.single w 1)) (f : Polynomial ℓ α) :
    motive f := by
  induction f using MonoidAlgebra.induction_linear with
  | zero => exact zero
  | add f g hf hg => exact add f g hf hg
  | single w a =>
    have h : ∀ k : ℕ, motive (MonoidAlgebra.single w (k : ZMod ℓ)) := by
      intro k
      induction k with
      | zero => simpa using zero
      | succ k ih =>
        rw [Nat.cast_succ, MonoidAlgebra.single_add]
        exact add _ _ ih (monomial w)
    have ha := h a.val
    rwa [ZMod.natCast_zmod_val] at ha

open scoped IsMulCommutative

noncomputable def rootSubgroup (s : Seed ℓ n α G) (hn : 5 ≤ n) (p : Root n) : Subgroup G :=
  Subgroup.closure (Set.range (word s hn p))

instance rootSubgroup_comm (s : Seed ℓ n α G) (hn : 5 ≤ n) (p : Root n) :
    IsMulCommutative (rootSubgroup s hn p) := by
  apply Subgroup.isMulCommutative_closure
  rintro _ ⟨u, rfl⟩ _ ⟨v, rfl⟩ _
  exact commute s hn p p u v p.ne.symm p.ne

noncomputable def rootWord (s : Seed ℓ n α G) (hn : 5 ≤ n) (p : Root n) (w : List α) :
    rootSubgroup s hn p := ⟨word s hn p w, Subgroup.subset_closure ⟨w, rfl⟩⟩

theorem rootWord_pow (s : Seed ℓ n α G) (hn : 5 ≤ n) (p : Root n) (w : List α) :
    rootWord s hn p w ^ ℓ = 1 := Subtype.ext (power s hn p w)

/-- The integer powers of a root word, as an additive homomorphism killing `ℓ`. -/
noncomputable def coefficientSource (s : Seed ℓ n α G) (hn : 5 ≤ n) (p : Root n) (w : List α) :
    {f : ℤ →+ Additive (rootSubgroup s hn p) // f ℓ = 0} :=
  ⟨zmultiplesHom _ (Additive.ofMul (rootWord s hn p w)), by
    change ((ℓ : ℕ) : ℤ) • Additive.ofMul (rootWord s hn p w) = 0
    rw [natCast_zsmul, ← ofMul_pow, rootWord_pow, ofMul_one]⟩

/-- A coefficient in the prime field acts on a root word by the corresponding power. -/
noncomputable def coefficient (s : Seed ℓ n α G) (hn : 5 ≤ n) (p : Root n) (w : List α) :
    ZMod ℓ →+ Additive (rootSubgroup s hn p) :=
  ZMod.lift ℓ (coefficientSource s hn p w)

theorem coefficient_one (s : Seed ℓ n α G) (hn : 5 ≤ n) (p : Root n) (w : List α) :
    coefficient s hn p w 1 = Additive.ofMul (rootWord s hn p w) := by
  have h := ZMod.lift_coe ℓ (coefficientSource s hn p w) 1
  rw [Int.cast_one] at h
  rw [coefficient, h]
  change (1 : ℤ) • Additive.ofMul (rootWord s hn p w) = _
  exact one_zsmul _

noncomputable def poly (s : Seed ℓ n α G) (hn : 5 ≤ n) (p : Root n) (f : Polynomial ℓ α) : G :=
  ((Finsupp.liftAddHom (fun w : FreeMonoid α => coefficient s hn p w.toList) f.coeff).toMul : G)

@[simp] theorem poly_zero (s : Seed ℓ n α G) (hn : 5 ≤ n) (p : Root n) :
    poly s hn p 0 = 1 := by simp [poly]

theorem poly_add (s : Seed ℓ n α G) (hn : 5 ≤ n) (p : Root n) (f g : Polynomial ℓ α) :
    poly s hn p (f + g) = poly s hn p f * poly s hn p g := by
  simp [poly]

@[simp] theorem poly_single (s : Seed ℓ n α G) (hn : 5 ≤ n) (p : Root n) (w : FreeMonoid α) :
    poly s hn p (MonoidAlgebra.single w 1) = word s hn p w.toList := by
  simp [poly, coefficient_one, rootWord]

theorem closure_commute {S T : Set G}
    (h : ∀ x ∈ S, ∀ y ∈ T, Commute x y) {x y : G}
    (hx : x ∈ Subgroup.closure S) (hy : y ∈ Subgroup.closure T) : Commute x y := by
  have hle : Subgroup.closure S ≤ Subgroup.centralizer T :=
    (Subgroup.closure_le _).mpr (fun a ha =>
      Subgroup.mem_centralizer_iff.mpr (fun b hb => (h a ha b hb).eq.symm))
  have hxc : x ∈ Subgroup.centralizer (Subgroup.closure T : Set G) := by
    rw [Subgroup.centralizer_closure]
    exact hle hx
  exact (Subgroup.mem_centralizer_iff.mp hxc y hy).symm

theorem poly_mem (s : Seed ℓ n α G) (hn : 5 ≤ n) (p : Root n) (f : Polynomial ℓ α) :
    poly s hn p f ∈ rootSubgroup s hn p :=
  (Finsupp.liftAddHom (fun w : FreeMonoid α => coefficient s hn p w.toList) f.coeff).toMul.property

theorem poly_commute (s : Seed ℓ n α G) (hn : 5 ≤ n)
    (p q : Root n) (f g : Polynomial ℓ α) (hpq : p.col ≠ q.row) (hqp : p.row ≠ q.col) :
    Commute (poly s hn p f) (poly s hn q g) := by
  apply closure_commute (S := Set.range (word s hn p)) (T := Set.range (word s hn q))
    ?_ (poly_mem s hn p f) (poly_mem s hn q g)
  rintro _ ⟨u, rfl⟩ _ ⟨v, rfl⟩
  exact commute s hn p q u v hpq hqp

/-- Additivity of the product relation in the first polynomial. -/
theorem poly_product_add_left (s : Seed ℓ n α G) (hn : 5 ≤ n)
    (i j k : Fin n) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (f₁ f₂ g : Polynomial ℓ α)
    (h₁ : bracket (poly s hn ⟨i, j, hij⟩ f₁) (poly s hn ⟨j, k, hjk⟩ g) =
      poly s hn ⟨i, k, hik⟩ (f₁ * g))
    (h₂ : bracket (poly s hn ⟨i, j, hij⟩ f₂) (poly s hn ⟨j, k, hjk⟩ g) =
      poly s hn ⟨i, k, hik⟩ (f₂ * g)) :
    bracket (poly s hn ⟨i, j, hij⟩ (f₁ + f₂)) (poly s hn ⟨j, k, hjk⟩ g) =
      poly s hn ⟨i, k, hik⟩ ((f₁ + f₂) * g) := by
  rw [poly_add, CommutatorCalculus.mul_left, h₂, h₁,
    CommutatorCalculus.conj_of_commute (poly_commute s hn _ _ f₁ (f₂ * g) hij.symm hik),
    add_mul, poly_add]
  exact (poly_commute s hn _ _ (f₂ * g) (f₁ * g) hik.symm hik).eq

/-- Additivity of the product relation in the second polynomial. -/
theorem poly_product_add_right (s : Seed ℓ n α G) (hn : 5 ≤ n)
    (i j k : Fin n) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (f g₁ g₂ : Polynomial ℓ α)
    (h₁ : bracket (poly s hn ⟨i, j, hij⟩ f) (poly s hn ⟨j, k, hjk⟩ g₁) =
      poly s hn ⟨i, k, hik⟩ (f * g₁))
    (h₂ : bracket (poly s hn ⟨i, j, hij⟩ f) (poly s hn ⟨j, k, hjk⟩ g₂) =
      poly s hn ⟨i, k, hik⟩ (f * g₂)) :
    bracket (poly s hn ⟨i, j, hij⟩ f) (poly s hn ⟨j, k, hjk⟩ (g₁ + g₂)) =
      poly s hn ⟨i, k, hik⟩ (f * (g₁ + g₂)) := by
  rw [poly_add, CommutatorCalculus.mul_right, h₁, h₂, mul_add, poly_add]
  have hconj := CommutatorCalculus.conj_of_commute
    (poly_commute s hn ⟨j, k, hjk⟩ ⟨i, k, hik⟩ g₁ (f * g₂) hik.symm hjk)
  simpa only [mul_assoc] using congrArg
    (fun x => poly s hn ⟨i, k, hik⟩ (f * g₁) * x) hconj

theorem poly_product [NeZero ℓ] (s : Seed ℓ n α G) (hn : 5 ≤ n)
    (i j k : Fin n) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (f g : Polynomial ℓ α) :
    bracket (poly s hn ⟨i, j, hij⟩ f) (poly s hn ⟨j, k, hjk⟩ g) =
      poly s hn ⟨i, k, hik⟩ (f * g) := by
  induction f using polynomial_induction with
  | zero => simp [bracket]
  | add f₁ f₂ h₁ h₂ => exact poly_product_add_left s hn i j k hij hjk hik f₁ f₂ g h₁ h₂
  | monomial u =>
    induction g using polynomial_induction with
    | zero => simp [bracket]
    | add g₁ g₂ h₁ h₂ => exact poly_product_add_right s hn i j k hij hjk hik _ g₁ g₂ h₁ h₂
    | monomial v =>
      rw [MonoidAlgebra.single_mul_single, one_mul, poly_single, poly_single, poly_single]
      exact product s hn i j k hij hjk hik u.toList v.toList

/-- A seed extends to a homomorphism from the Steinberg group of the free algebra. -/
noncomputable def lift [NeZero ℓ] (s : Seed ℓ n α G) (hn : 5 ≤ n) :
    Steinberg n (Polynomial ℓ α) →* G :=
  Steinberg.lift (poly s hn) (poly_add s hn)
    (fun p q h₁ h₂ f g => poly_commute s hn p q f g h₁ h₂) (poly_product s hn)

@[simp] theorem lift_x [NeZero ℓ] (s : Seed ℓ n α G) (hn : 5 ≤ n) (p : Root n)
    (f : Polynomial ℓ α) : lift s hn (Steinberg.x p f) = poly s hn p f :=
  Steinberg.lift_x _ _ _ _ _ _

end MonomialCompletion
end AllPrimeGroups
