import AllPrimeGroups.PhaseConstruction
import OAI.GroupTheory.PeriodicGroups.Algebra.MatrixTests

/-! Phases of long surviving words in a machine hierarchy (manuscript Lemma 19.1).

At each level h of an upstream machine hierarchy, upstream's token decomposition splits a long
surviving word into a bounded prefix without cuts, raw tokens, and a bounded last interval
(`Survives.raw_token_decomposition`). Each raw token reaches the encoding of a word of the next
level D h whose length is the token length divided by the block length `2 2^h + 1`
(`rawToken_normalize`). Since the encoding map induces an algebra map from the next level, the
concatenation of these upper words survives at the next level.

This file packages these facts as `TokenData` and obtains, by recursion over n levels, phases of
long surviving words at level h modulo the product of the block lengths of the n levels starting
at h. -/

namespace AllPrimeGroups
namespace Phases
open OAI OAI.SourceBurnside OAI.SourceBurnside.FiniteTable
open Classical

noncomputable section

namespace Hierarchy

/-- The period of the n levels starting at h: the product of their block lengths. -/
def period (D : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 1
  | n + 1, h => (2 * 2 ^ h + 1) * period D n (D * h)

theorem two_pow_le_period (D : ℕ) : ∀ n h : ℕ, 2 ^ n ≤ period D n h
  | 0, _ => le_refl 1
  | n + 1, h => by
    rw [period, pow_succ]
    have := two_pow_le_period D n (D * h)
    have h2 : 2 ≤ 2 * 2 ^ h + 1 := by have := Nat.two_pow_pos h; omega
    calc 2 ^ n * 2 ≤ period D n (D * h) * (2 * 2 ^ h + 1) := Nat.mul_le_mul this h2
      _ = (2 * 2 ^ h + 1) * period D n (D * h) := Nat.mul_comm _ _

theorem period_coprime {D q h₀ : ℕ} (hc : ∀ j : ℕ, (2 ^ (h₀ * D ^ j + 1) + 1).Coprime q) :
    ∀ n j : ℕ, (period D n (h₀ * D ^ j)).Coprime q
  | 0, _ => Nat.coprime_one_left q
  | n + 1, j => by
    rw [period]
    apply Nat.Coprime.mul_left
    · have := hc j
      rwa [pow_succ, mul_comm (2 ^ (h₀ * D ^ j)) 2] at this
    · have := period_coprime hc n (j + 1)
      rwa [pow_succ, ← mul_assoc, mul_comm (h₀ * D ^ j) D] at this

variable {D : ℕ} {hD : 2 ≤ D} (A : SourceMachine.MachineHierarchy D hD)

/-- Surviving words at level h. -/
abbrev Surv (h : ℕ) (hh : A.threshold ≤ h) (w : List (Codec.Raw h)) : Prop :=
  Codec.Survives (A.height_pos hh) (A.schedule h hh) (10000 * (D * h)) w

theorem surv_of_reach {h : ℕ} {hh : A.threshold ≤ h} {v w : List (Codec.Raw h)}
    (hv : Surv A h hh v)
    (hr : Codec.Reach (A.height_pos hh) (A.schedule h hh) (10000 * (D * h)) v w) :
    Surv A h hh w :=
  fun p z s hr' hz => hv p z s (hr.trans hr') hz

theorem reach_flatten {h : ℕ} (hh : A.threshold ≤ h) (f : List (Codec.Raw h) → List (Codec.Raw h)) :
    ∀ ts : List (List (Codec.Raw h)),
      (∀ t ∈ ts, Codec.Reach (A.height_pos hh) (A.schedule h hh) (10000 * (D * h)) t (f t)) →
      Codec.Reach (A.height_pos hh) (A.schedule h hh) (10000 * (D * h)) ts.flatten
        (ts.map f).flatten
  | [], _ => .refl
  | t :: ts, hts => by
    have h1 : Codec.Reach (A.height_pos hh) (A.schedule h hh) (10000 * (D * h))
        (t ++ ts.flatten) (f t ++ ts.flatten) := by
      simpa using Codec.reach_context (hts t (by simp)) [] ts.flatten
    have h2 : Codec.Reach (A.height_pos hh) (A.schedule h hh) (10000 * (D * h))
        (f t ++ ts.flatten) (f t ++ (ts.map f).flatten) := by
      simpa using Codec.reach_context
        (reach_flatten hh f ts fun s hs => hts s (List.mem_cons_of_mem t hs)) (f t) []
    simpa only [List.flatten_cons, List.map_cons] using h1.trans h2

theorem embedding_append (h : ℕ) (u v : List (Codec.Raw (D * h))) :
    SourceMachine.embedding h D (u ++ v) =
      SourceMachine.embedding h D u ++ SourceMachine.embedding h D v := by
  simp [SourceMachine.embedding, encodeWord, List.flatMap_append]

theorem embedding_flatten (h : ℕ) (us : List (List (Codec.Raw (D * h)))) :
    SourceMachine.embedding h D us.flatten = (us.map (SourceMachine.embedding h D)).flatten := by
  induction us with
  | nil => simp [SourceMachine.embedding, encodeWord]
  | cons u us ih => rw [List.flatten_cons, embedding_append, ih, List.map_cons, List.flatten_cons]

/-- A word of the next level survives if its encoding survives. -/
theorem surv_of_embedding {h : ℕ} (hh : A.threshold ≤ h) {u : List (Codec.Raw (D * h))}
    (hu : Surv A h hh (SourceMachine.embedding h D u)) : Surv A (D * h) (A.next_large hh) u := by
  apply (Codec.survives_iff_not_vanishes u).mpr
  intro hv
  have h1 := A.embeddingHom_word (ZMod 2) hh u
  rw [(A.table (D * h) (A.next_large hh)).word_eq_zero_of_vanishes (K := ZMod 2) hv,
    map_zero] at h1
  exact (Codec.survives_iff_not_vanishes _).mp hu
    (((A.table h hh).word_eq_zero_iff (K := ZMod 2) _).mp h1.symm)

/-- The upper word of a raw token. -/
def upWord (h : ℕ) (hh : A.threshold ≤ h) (t : List (Codec.Raw h)) : List (Codec.Raw (D * h)) :=
  if ht : Codec.rawToken (A.height_pos hh) (A.schedule h hh) (10000 * (D * h)) t then
    (Codec.rawToken_normalize (A.threshold_four.trans hh) (A.fits h hh).2.2.2.1 ht).choose
  else []

theorem upWord_spec {h : ℕ} (hh : A.threshold ≤ h) {t : List (Codec.Raw h)}
    (ht : Codec.rawToken (A.height_pos hh) (A.schedule h hh) (10000 * (D * h)) t) :
    t.length = (2 * 2 ^ h + 1) * (upWord A h hh t).length ∧
      Codec.Reach (A.height_pos hh) (A.schedule h hh) (10000 * (D * h)) t
        (SourceMachine.embedding h D (upWord A h hh t)) := by
  have hs := (Codec.rawToken_normalize (A.threshold_four.trans hh) (A.fits h hh).2.2.2.1
    ht).choose_spec
  have hu : upWord A h hh t = (Codec.rawToken_normalize (A.threshold_four.trans hh)
      (A.fits h hh).2.2.2.1 ht).choose := by
    simp only [upWord, ht, ↓reduceDIte]
  rw [hu]
  exact ⟨hs.2.2.1, hs.2.2.2⟩

/-- The parse of a long surviving word: a bounded prefix, raw tokens, and a bounded last
interval. -/
theorem decomposition {h : ℕ} (hh : A.threshold ≤ h) {w : List (Codec.Raw h)}
    (hw : Surv A h hh w) (hl : 2 * fragmentBound (2 ^ h) < w.length) :
    ∃ (ts : List (List (Codec.Raw h))) (s : List (Codec.Raw h)),
      (Cuts.parse (Codec.rawCut (A.height_pos hh)) w).2 = ts ++ [s] ∧
      (Cuts.parse (Codec.rawCut (A.height_pos hh)) w).1.length ≤ fragmentBound (2 ^ h) ∧
      s.length ≤ fragmentBound (2 ^ h) ∧ ts ≠ [] ∧
      (∀ t ∈ ts, Codec.rawToken (A.height_pos hh) (A.schedule h hh) (10000 * (D * h)) t) ∧
      ts.flatten <:+: w := by
  have h4 : 4 ≤ h := A.threshold_four.trans hh
  obtain ⟨p, ts, s, rfl, hp, hs, hpB, hsB, hts, htok⟩ :=
    Codec.Survives.raw_token_decomposition h4 hw hl
  have hint : ∀ t ∈ ts ++ [s], Cuts.Interval (Codec.rawCut (A.height_pos hh)) t := by
    intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · exact Codec.rawToken_interval h4 (htok t ht)
    · rw [List.mem_singleton.mp ht]
      exact hs
  have hparse : Cuts.parse (Codec.rawCut (A.height_pos hh)) (p ++ ts.flatten ++ s) =
      (p, ts ++ [s]) := by
    have he := parse_eq_of (Codec.rawCut (A.height_pos hh)) hp hint
    simpa [List.flatten_append, List.append_assoc] using he
  refine ⟨ts, s, by rw [hparse], by rw [hparse]; exact hpB, hsB, hts, htok, ⟨p, s, rfl⟩⟩

/-- The token data of level h. -/
def tokenData (h : ℕ) (hh : A.threshold ≤ h) :
    TokenData (Surv A h hh) (Surv A (D * h) (A.next_large hh)) where
  cut := Codec.rawCut (A.height_pos hh)
  B := fragmentBound (2 ^ h)
  Lb := 2 * 2 ^ h + 1
  Lb_pos := by omega
  thrTok := 2 * fragmentBound (2 ^ h)
  up := upWord A h hh
  surv_left x z hxz := Codec.Survives.infix hxz ⟨x, [], by simp⟩
  surv_right v y hvy := Codec.Survives.infix hvy ⟨[], y, by simp⟩
  parse_bound w hw hl := by
    obtain ⟨ts, s, hparse, hpB, hsB, hts, -, -⟩ := decomposition A hh hw hl
    exact ⟨hpB, ts, s, hparse, hts, hsB⟩
  token_length w hw hl t ht := by
    obtain ⟨ts, s, hparse, -, -, -, htok, -⟩ := decomposition A hh hw hl
    rw [hparse, List.dropLast_concat] at ht
    exact (upWord_spec A hh (htok t ht)).1
  up_surv w hw hl := by
    obtain ⟨ts, s, hparse, -, -, -, htok, hinf⟩ := decomposition A hh hw hl
    rw [hparse, List.dropLast_concat]
    apply surv_of_embedding A hh
    rw [embedding_flatten, List.map_map]
    exact surv_of_reach A (Codec.Survives.infix hw hinf)
      (reach_flatten A hh _ ts fun t ht => (upWord_spec A hh (htok t ht)).2)

/-- Phases of long surviving words at level h, built from the n levels starting at h. -/
def phases : (n h : ℕ) → (hh : A.threshold ≤ h) → LevelPhases (Surv A h hh) (period D n h)
  | 0, _, _ => trivialPhases _
  | n + 1, h, hh => (tokenData A h hh).step (phases n (D * h) (A.next_large hh))

end Hierarchy

end

end Phases
end AllPrimeGroups
