import AllPrimeGroups.HierarchyPhases
import AllPrimeGroups.WordBasis
import AllPrimeGroups.PhaseCommutators
import AllPrimeGroups.CorrectionFaithful

/-! The phase grading of one level of a machine hierarchy (manuscript Sections 19 and 20).

Fix phases of long surviving words at a level h of a machine hierarchy, modulo m + 2, with the
prefix and suffix properties (`LevelPhases`). This file derives:

* phases are unchanged by replacements, hence equal on reachable long surviving words;
* the phased words of manuscript Section 20 (`PhasedWords`) for the word algebra over a
  commutative ring K, with the vanishing and connectivity properties of manuscript Lemma 16.1;
* the phase grading (`Kernel.PhaseGrading`) on the classes of long surviving words over
  `ZMod ℓ`, both cases of manuscript Lemma 20.2 in rank at least three, homogeneity for the
  grading, and the linear independence of these classes.

These are the hypotheses on phases of the general stable separation theorem
`Stable.eq_one_of_phaseGradings`. -/

namespace AllPrimeGroups
namespace Phases
open OAI OAI.SourceBurnside OAI.SourceBurnside.FiniteTable
open Classical

noncomputable section

/-- In rank at least three, two indices leave room for a third. -/
theorem exists_third {k : ℕ} (hk : 3 ≤ k) (i j : Fin k) : ∃ c : Fin k, i ≠ c ∧ c ≠ j := by
  have hcard : ({i, j} : Finset (Fin k)).card < (Finset.univ : Finset (Fin k)).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    exact lt_of_le_of_lt Finset.card_le_two (by omega)
  obtain ⟨c, -, hc⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc
  exact ⟨c, fun e => hc.1 e.symm, hc.2⟩

/-- Residues modulo m + 2 are elements of `Fin (m + 2)`; addition of a natural number agrees. -/
theorem zmod_add_natCast {m : ℕ} (a : ZMod (m + 2)) (k : ℕ) :
    (id (a + (k : ZMod (m + 2))) : Fin (m + 2)) = (id a : Fin (m + 2)) + Fin.ofNat (m + 2) k := by
  apply Fin.ext
  change ZMod.val (a + (k : ZMod (m + 2))) = ((id a : Fin (m + 2)) + Fin.ofNat (m + 2) k).val
  rw [ZMod.val_add, ZMod.val_natCast, Fin.val_add, Fin.val_ofNat]
  rfl

namespace Hierarchy
variable {D : ℕ} {hD : 2 ≤ D} (A : SourceMachine.MachineHierarchy D hD)
variable {h : ℕ} (hh : A.threshold ≤ h)

theorem length_of_reach {v w : List (Codec.Raw h)}
    (hr : Codec.Reach (A.height_pos hh) (A.schedule h hh) (10000 * (D * h)) v w) :
    w.length = v.length := by
  induction hr with
  | refl => rfl
  | tail _ hbc ih =>
    obtain ⟨p, s, a, b, rfl, rfl, he⟩ := hbc
    have := (Codec.replacement_lengths (A.threshold_four.trans hh) _ _ a b he).1
    simp only [List.length_append] at ih ⊢
    omega

section Phases
variable {Q : ℕ} (P : LevelPhases (Surv A h hh) Q)

/-- A replacement does not change the phase of a long surviving word. -/
theorem phase_rule {x l r y : List (Codec.Raw h)}
    (hrule : Codec.replacement (A.height_pos hh) (A.schedule h hh) (10000 * (D * h)) l r)
    (hs : Surv A h hh (x ++ l ++ y)) (hs' : Surv A h hh (x ++ r ++ y))
    (hlen : 2 * P.thr + 2 ≤ (x ++ l ++ y).length) :
    P.σ (x ++ r ++ y) = P.σ (x ++ l ++ y) := by
  obtain ⟨hlr, -, hl2⟩ := Codec.replacement_lengths (A.threshold_four.trans hh) _ _ l r hrule
  by_cases hy : P.thr ≤ y.length
  · have h1 := P.suffix (x ++ l) y hs hy
    have h2 := P.suffix (x ++ r) y hs' hy
    have he : (x ++ r).length = (x ++ l).length := by simp [hlr]
    rw [he] at h2
    exact add_right_cancel (h2.trans h1.symm)
  · have hx : P.thr ≤ x.length := by
      simp only [List.length_append] at hlen
      omega
    have h1 := P.pref x (l ++ y) (by rwa [← List.append_assoc]) hx
    have h2 := P.pref x (r ++ y) (by rwa [← List.append_assoc]) hx
    rw [← List.append_assoc] at h1 h2
    rw [h1, h2]

/-- Reachable long surviving words have the same phase. -/
theorem phase_reach {v w : List (Codec.Raw h)}
    (hr : Codec.Reach (A.height_pos hh) (A.schedule h hh) (10000 * (D * h)) v w)
    (hv : Surv A h hh v) (hlen : 2 * P.thr + 2 ≤ v.length) : P.σ w = P.σ v := by
  induction hr with
  | refl => rfl
  | tail hvb hbc ih =>
    have hsb := surv_of_reach A hv hvb
    have hsc := surv_of_reach A hsb (Relation.ReflTransGen.single hbc)
    have hlb := length_of_reach A hh hvb
    obtain ⟨p, s, a, b, rfl, rfl, he⟩ := hbc
    rw [phase_rule A hh P he hsb hsc (by omega), ih]

variable (K : Type*) [CommRing K]

/-- The value of a literal word in the word algebra over K. -/
abbrev wordVal (w : List (Codec.Raw h)) : A.Algebra K h hh :=
  (A.table h hh).word (K := K) (FreeMonoid.ofList w)

omit P in
theorem wordVal_append (u v : List (Codec.Raw h)) :
    wordVal A hh K (u ++ v) = wordVal A hh K u * wordVal A hh K v := by
  simp only [wordVal, FreeMonoid.ofList_append, WordAlgebra.Table.word_mul]

omit P in
theorem surv_of_ne {w : List (Codec.Raw h)} (hw : wordVal A hh K w ≠ 0) : Surv A h hh w :=
  (Codec.survives_iff_not_vanishes w).mpr fun hv =>
    hw ((A.table h hh).word_eq_zero_of_vanishes hv)

omit P in
theorem ne_of_surv [Nontrivial K] {w : List (Codec.Raw h)} (hw : Surv A h hh w) :
    wordVal A hh K w ≠ 0 :=
  (A.table h hh).word_ne_zero ((Codec.survives_iff_not_vanishes w).mp hw)

/-- The phased words of level h (manuscript Section 20). -/
def phasedWords : PhasedWords (Codec.Raw h) (A.Algebra K h hh) (ZMod Q) where
  ev := wordVal A hh K
  ev_append := wordVal_append A hh K
  Rule l r := Codec.replacement (A.height_pos hh) (A.schedule h hh) (10000 * (D * h)) l r
  rule_ev hr := (A.table h hh).word_rep hr
  rule_length hr := (Codec.replacement_lengths (A.threshold_four.trans hh) _ _ _ _ hr).1
  width := 2
  rule_width hr := (Codec.replacement_lengths (A.threshold_four.trans hh) _ _ _ _ hr).2.2
  N := 2 * P.thr + 2
  σ := P.σ
  τ w := P.σ w + (w.length : ZMod Q)
  mismatch {u v} hu hv _ _ hne := by
    by_contra h0
    have hs := surv_of_ne A hh K (by rw [wordVal_append]; exact h0)
    apply hne
    show P.σ u + (u.length : ZMod Q) = P.σ v
    have h1 := P.suffix u v hs (by omega)
    have h2 := P.pref u v hs (by omega)
    rw [← h1, h2]
  σ_prefix {u v} hu h0 := P.pref u v (surv_of_ne A hh K h0) (by omega)
  τ_suffix {u v} hv h0 := by
    have h1 := P.suffix u v (surv_of_ne A hh K h0) (by omega)
    show P.σ (u ++ v) + ((u ++ v).length : ZMod Q) = P.σ v + (v.length : ZMod Q)
    rw [List.length_append, Nat.cast_add, ← h1]
    ring
  σ_rule {x l r y} hr hl h0 := by
    have hs := surv_of_ne A hh K h0
    exact phase_rule A hh P hr hs
      (surv_of_reach A hs (Relation.ReflTransGen.single ⟨x, y, l, r, rfl, rfl, hr⟩)) hl
  τ_rule {x l r y} hr hl h0 := by
    have hs := surv_of_ne A hh K h0
    have hlr := (Codec.replacement_lengths (A.threshold_four.trans hh) _ _ _ _ hr).1
    show P.σ (x ++ r ++ y) + ((x ++ r ++ y).length : ZMod Q) =
      P.σ (x ++ l ++ y) + ((x ++ l ++ y).length : ZMod Q)
    rw [phase_rule A hh P hr hs
      (surv_of_reach A hs (Relation.ReflTransGen.single ⟨x, y, l, r, rfl, rfl, hr⟩)) hl]
    simp only [List.length_append, hlr]

theorem step_of_reach {v w : List (Codec.Raw h)}
    (hr : Codec.Reach (A.height_pos hh) (A.schedule h hh) (10000 * (D * h)) v w) :
    Relation.ReflTransGen (phasedWords A hh P K).Step v w := by
  induction hr with
  | refl => exact .refl
  | tail _ hbc ih =>
    obtain ⟨p, s, a, b, rfl, rfl, he⟩ := hbc
    exact ih.tail ⟨p, a, b, s, he, rfl, rfl⟩

/-- Vanishing words are connected to words with a short zero factor (manuscript Lemma 16.1). -/
theorem vanish_path [Nontrivial K] (w : List (Codec.Raw h))
    (hw : (phasedWords A hh P K).ev w = 0) :
    ∃ w', Relation.ReflTransGen (phasedWords A hh P K).Step w w' ∧
      ∃ x z y, w' = x ++ z ++ y ∧ (phasedWords A hh P K).ev z = 0 ∧
        z.length ≤ (phasedWords A hh P K).width := by
  obtain ⟨p, z, s, hz, hr⟩ := ((A.table h hh).word_eq_zero_iff (K := K) _).mp hw
  have hr' : Codec.Reach (A.height_pos hh) (A.schedule h hh) (10000 * (D * h)) w
      (p.toList ++ z.toList ++ s.toList) := Codec.reach_iff_table.mpr hr
  exact ⟨_, step_of_reach A hh P K hr', p.toList, z.toList, s.toList, rfl,
    (A.table h hh).word_zero hz, (Codec.zero_lengths _ _ _ z.toList hz).2⟩

/-- Literal words with the same nonzero value are connected (manuscript Lemma 16.1). -/
theorem connected [Nontrivial K] (w w' : List (Codec.Raw h))
    (he : (phasedWords A hh P K).ev w = (phasedWords A hh P K).ev w')
    (hne : (phasedWords A hh P K).ev w ≠ 0) :
    Relation.ReflTransGen (phasedWords A hh P K).Step w w' := by
  rcases ((A.table h hh).word_eq_word_iff (K := K) _ _).mp he with hr | ⟨hv, -⟩
  · exact step_of_reach A hh P K (Codec.reach_iff_table.mpr hr)
  · exact absurd ((A.table h hh).word_eq_zero_of_vanishes hv) hne

theorem cutValue_eq {k : ℕ} {i j : Fin k} (hij : i ≠ j) (u v : List (Codec.Raw h)) :
    PhasedWords.cutValue (phasedWords A hh P K) Steinberg.rootFamily i j u v =
      bracket (Steinberg.x ⟨i, j, hij⟩ (wordVal A hh K u))
        (Steinberg.x ⟨j, i, hij.symm⟩ (wordVal A hh K v)) := by
  show bracket (Steinberg.indexedRoot i j (wordVal A hh K u))
    (Steinberg.indexedRoot j i (wordVal A hh K v)) = _
  simp [Steinberg.indexedRoot, hij, hij.symm]

end Phases

section Grading
variable {m : ℕ} (P : LevelPhases (Surv A h hh) (m + 2)) (K : Type*) [CommRing K]

/-- A long surviving literal word representing an element of the word algebra. -/
def Represents (x : A.Algebra K h hh) (w : List (Codec.Raw h)) : Prop :=
  2 * P.thr + 3 ≤ w.length ∧ Surv A h hh w ∧ wordVal A hh K w = x

/-- The classes of long surviving words. -/
def longWords : Set (A.Algebra K h hh) := {x | ∃ w, Represents A hh P K x w}

/-- A chosen long surviving representative. -/
def rep (x : A.Algebra K h hh) : List (Codec.Raw h) :=
  if hx : ∃ w, Represents A hh P K x w then hx.choose else []

/-- The phase of an element: the phase of its chosen representative. -/
def phaseOf (x : A.Algebra K h hh) : ZMod (m + 2) := P.σ (rep A hh P K x)

/-- The length of an element: the length of its chosen representative. -/
def lenOf (x : A.Algebra K h hh) : ℕ := (rep A hh P K x).length

theorem rep_spec [Nontrivial K] {x : A.Algebra K h hh} {w : List (Codec.Raw h)}
    (hw : Represents A hh P K x w) :
    P.σ (rep A hh P K x) = P.σ w ∧ (rep A hh P K x).length = w.length := by
  have hx : ∃ w, Represents A hh P K x w := ⟨w, hw⟩
  have hc := hx.choose_spec
  have hr : rep A hh P K x = hx.choose := by simp only [rep, hx, ↓reduceDIte]
  rw [hr]
  have he : wordVal A hh K hx.choose = wordVal A hh K w := hc.2.2.trans hw.2.2.symm
  rcases ((A.table h hh).word_eq_word_iff (K := K) _ _).mp he with hreach | ⟨hv, -⟩
  · have hreach' : Codec.Reach (A.height_pos hh) (A.schedule h hh) (10000 * (D * h))
        hx.choose w := Codec.reach_iff_table.mpr hreach
    exact ⟨(phase_reach A hh P hreach' hc.2.1 (by have := hc.1; omega)).symm,
      (length_of_reach A hh hreach').symm⟩
  · exact absurd hv ((Codec.survives_iff_not_vanishes _).mp hc.2.1)

theorem phaseOf_eq [Nontrivial K] {x : A.Algebra K h hh} {w : List (Codec.Raw h)}
    (hw : Represents A hh P K x w) : phaseOf A hh P K x = P.σ w :=
  (rep_spec A hh P K hw).1

theorem lenOf_eq [Nontrivial K] {x : A.Algebra K h hh} {w : List (Codec.Raw h)}
    (hw : Represents A hh P K x w) : lenOf A hh P K x = w.length :=
  (rep_spec A hh P K hw).2

variable [Nontrivial K]

/-- Phases of the classes of long surviving words, modulo m + 2. -/
def cyclicPhases : Kernel.CyclicPhases (A.Algebra K h hh) (m + 2) where
  W := longWords A hh P K
  σ x := phaseOf A hh P K x
  τ x := phaseOf A hh P K x + (lenOf A hh P K x : ZMod (m + 2))
  len := lenOf A hh P K
  len_phase x _ := zmod_add_natCast _ _
  mul_eq_zero := by
    rintro x ⟨u, hu⟩ y ⟨v, hv⟩ hne
    by_contra h0
    rw [← hu.2.2, ← hv.2.2, ← wordVal_append] at h0
    have hs := surv_of_ne A hh K h0
    apply hne
    show phaseOf A hh P K x + (lenOf A hh P K x : ZMod (m + 2)) = phaseOf A hh P K y
    rw [phaseOf_eq A hh P K hu, lenOf_eq A hh P K hu, phaseOf_eq A hh P K hv]
    have h1 := P.suffix u v hs (by have := hv.1; omega)
    have h2 := P.pref u v hs (by have := hu.1; omega)
    rw [← h1, h2]

theorem valid {x y : A.Algebra K h hh} {u v : List (Codec.Raw h)}
    (hu : Represents A hh P K x u) (hv : Represents A hh P K y v)
    (hne : (cyclicPhases A hh P K).σ x ≠ (cyclicPhases A hh P K).τ y) :
    (phasedWords A hh P K).Valid u v := by
  refine ⟨by have := hu.1; show 2 * P.thr + 2 ≤ u.length; omega,
    by have := hv.1; show 2 * P.thr + 2 ≤ v.length; omega,
    ne_of_surv A hh K hu.2.1, ne_of_surv A hh K hv.2.1, ?_⟩
  intro he
  apply hne
  show phaseOf A hh P K x = phaseOf A hh P K y + (lenOf A hh P K y : ZMod (m + 2))
  rw [phaseOf_eq A hh P K hu, phaseOf_eq A hh P K hv, lenOf_eq A hh P K hv]
  exact he

/-- Manuscript Lemma 20.2, zero case, in rank at least three. -/
theorem oppositeCommute {k : ℕ} (hk : 3 ≤ k) : (cyclicPhases A hh P K).OppositeCommute k := by
  intro i j hij x hx y hy hne h0
  obtain ⟨u, hu⟩ := hx
  obtain ⟨v, hv⟩ := hy
  obtain ⟨c, hic, hcj⟩ := exists_third hk i j
  have hc := PhasedWords.cutValue_eq_one_of_mul_eq_zero (phasedWords A hh P K)
    Steinberg.rootFamily hic hcj hij (vanish_path A hh P K) (valid A hh P K hu hv hne)
    (by have := hu.1; have := hv.1; show 2 * (2 * P.thr + 2) + 2 ≤ u.length + v.length; omega)
    (by show wordVal A hh K u * wordVal A hh K v = 0; rw [hu.2.2, hv.2.2]; exact h0)
  rw [cutValue_eq A hh P K hij, hu.2.2, hv.2.2] at hc
  exact (bracket_eq_one_iff _ _).mp hc

/-- Manuscript Lemma 20.2, nonzero case, in rank at least three. -/
theorem cutIndependent {k : ℕ} (hk : 3 ≤ k) : (cyclicPhases A hh P K).CutIndependent k := by
  intro i j j' hij hij' a ha b hb a' ha' b' hb' hab hab' heq
  obtain ⟨u, hu⟩ := ha
  obtain ⟨v, hv⟩ := hb
  obtain ⟨u', hu'⟩ := ha'
  obtain ⟨v', hv'⟩ := hb'
  have hval := valid A hh P K hu hv hab
  have hval' := valid A hh P K hu' hv' hab'
  have hlen : 2 * (phasedWords A hh P K).N + (phasedWords A hh P K).width ≤
      u.length + v.length := by
    have := hu.1; have := hv.1; show 2 * (2 * P.thr + 2) + 2 ≤ u.length + v.length; omega
  have hlen' : 2 * (phasedWords A hh P K).N + (phasedWords A hh P K).width ≤
      u'.length + v'.length := by
    have := hu'.1; have := hv'.1; show 2 * (2 * P.thr + 2) + 2 ≤ u'.length + v'.length; omega
  have heq' : (phasedWords A hh P K).ev u * (phasedWords A hh P K).ev v =
      (phasedWords A hh P K).ev u' * (phasedWords A hh P K).ev v' := by
    show wordVal A hh K u * wordVal A hh K v = wordVal A hh K u' * wordVal A hh K v'
    rw [hu.2.2, hv.2.2, hu'.2.2, hv'.2.2]
    exact heq
  rw [← hu.2.2, ← hv.2.2, ← hu'.2.2, ← hv'.2.2, ← cutValue_eq A hh P K hij,
    ← cutValue_eq A hh P K hij']
  obtain ⟨c, hic, hcj⟩ := exists_third hk i j
  obtain ⟨c', hic', hcj'⟩ := exists_third hk i j'
  by_cases h0 : (phasedWords A hh P K).ev u * (phasedWords A hh P K).ev v = 0
  · rw [PhasedWords.cutValue_eq_one_of_mul_eq_zero (phasedWords A hh P K) Steinberg.rootFamily
        hic hcj hij (vanish_path A hh P K) hval hlen h0,
      PhasedWords.cutValue_eq_one_of_mul_eq_zero (phasedWords A hh P K) Steinberg.rootFamily
        hic' hcj' hij' (vanish_path A hh P K) hval' hlen' (heq' ▸ h0)]
  · rw [PhasedWords.cutValue_eq_of_mul_eq (phasedWords A hh P K) Steinberg.rootFamily hic hcj hij
      (connected A hh P K) hval hval' hlen heq' h0]
    by_cases hjj : j = j'
    · subst hjj
      rfl
    · exact PhasedWords.cutValue_index (phasedWords A hh P K) Steinberg.rootFamily hij'
        (Ne.symm hjj) hij hval'

/-- The classes of long surviving words are linearly independent. -/
theorem linearIndependent :
    LinearIndependent K (fun x : (cyclicPhases A hh P K).W => (x : A.Algebra K h hh)) :=
  WordBasis.linearIndependent_words (A.table h hh) _ fun _ ⟨w, hw⟩ =>
    ⟨FreeMonoid.ofList w, (Codec.survives_iff_not_vanishes w).mp hw.2.1, hw.2.2.symm⟩

/-- Long surviving words are homogeneous for the grading. -/
theorem grading_word (x : A.Algebra K h hh) (hx : x ∈ (cyclicPhases A hh P K).W) :
    ((A.table h hh).gradingHom (K := K) (A.table_homogeneous hh)).toRingHom x =
      Polynomial.monomial ((cyclicPhases A hh P K).len x) x := by
  obtain ⟨w, hw⟩ := hx
  show (A.table h hh).gradingHom (K := K) (A.table_homogeneous hh) x =
    Polynomial.monomial (lenOf A hh P K x) x
  rw [lenOf_eq A hh P K hw, ← hw.2.2]
  exact WordAlgebra.Table.gradingHom_word (A.table h hh) (A.table_homogeneous hh)
    (FreeMonoid.ofList w)

end Grading

end Hierarchy

end

end Phases
end AllPrimeGroups
