import AllPrimeGroups.Candidate
import AllPrimeGroups.StableMap
import AllPrimeGroups.FiniteIndexPresentation
import AllPrimeGroups.Separation
import AllPrimeGroups.Target

/-! Assembly of the four properties for the SAME candidate subgroup (manuscript Section 4).

Every theorem below keeps its hypotheses explicit. `CoefficientObligations p` collects the
statements about the coefficient algebra that are still to be proved for `R(p)`:
finite presentation of the fixed-rank Steinberg group, matrix nilpotence, finite-rank
injectivity, relative p-power torsion, and stable separation. `target_of_obligations`
is a reduction of `Target` to those statements; it does not prove any of them. -/

namespace AllPrimeGroups
noncomputable section

namespace Candidate

variable {R S : Type*} [Ring R] [Ring S] (n : ℕ) (ε : R →+* S)

/-- Finite presentation passes to the candidate by finite-index rewriting. -/
theorem finitelyPresented [Finite S] (hn : 3 ≤ n)
    [Group.IsFinitelyPresented (Steinberg n R)] :
    Group.IsFinitelyPresented (CandidateSubgroup n ε) := by
  have := finiteIndex n ε hn
  exact isFinitelyPresented_of_finiteIndex (CandidateSubgroup n ε)

/-- The stable image of a candidate element reduces trivially. -/
theorem stable_reduction_eq_one (g : CandidateSubgroup n ε) :
    Stable.map ε (Stable.of R n g.val) = 1 := by
  have hdet : Stable.detector n ε g.val = 1 := g.property
  rw [Stable.map_of]
  exact congrArg Subtype.val hdet

/-- Elementwise p-power torsion, from matrix nilpotence, relative torsion in the stable
kernel, and finite-rank injectivity. All three are explicit hypotheses. -/
theorem isPGroup {p : ℕ} (hp : p.Prime) [CharP R p] (hn : 3 ≤ n)
    (hnil : ∀ A : Matrix (Fin n) (Fin n) R, ε.mapMatrix A = 0 → IsNilpotent A)
    (hinj : Function.Injective (Stable.of R n))
    (htors : ∀ z : StableSteinberg R, Stable.representation R z = 1 → Stable.map ε z = 1 →
      ∃ a : ℕ, z ^ p ^ a = 1) :
    IsPGroup p (CandidateSubgroup n ε) := by
  intro g
  let : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hU := units_congruence_isPGroup hp (ε.mapMatrix (m := Fin n)) hnil
  obtain ⟨a, ha⟩ := hU (matrixRepresentation n ε g)
  have hrep : Elementary.representation (g.val ^ p ^ a) = 1 := by
    rw [map_pow]
    exact congrArg Subtype.val ha
  have hz1 : Stable.representation R (Stable.of R n (g.val ^ p ^ a)) = 1 := by
    rw [Stable.representation_of, hrep, map_one]
  have hz2 : Stable.map ε (Stable.of R n (g.val ^ p ^ a)) = 1 := by
    rw [map_pow, map_pow, stable_reduction_eq_one n ε g, one_pow]
  obtain ⟨b, hb⟩ := htors _ hz1 hz2
  refine ⟨a + b, Subtype.ext ?_⟩
  change g.val ^ p ^ (a + b) = 1
  apply hinj
  rw [map_one, pow_add, pow_mul, map_pow]
  exact hb

/-- Residual finiteness, from stable separation by finite coefficient quotients and
finite-rank injectivity. The finite quotients are the stable stage images. -/
theorem residuallyFinite (hn : 3 ≤ n)
    (hinj : Function.Injective (Stable.of R n))
    {ι : Type*} {Q : ι → Type*} [∀ i, Ring (Q i)] [∀ i, Finite (Q i)] (q : ∀ i, R →+* Q i)
    (hsep : ∀ z : StableSteinberg R, (∀ i, Stable.map (q i) z = 1) → z = 1) :
    Group.ResiduallyFinite (CandidateSubgroup n ε) := by
  have hfin : ∀ i, Finite (Stable.StageImage (Q i) n) :=
    fun i => Stable.stageImage_finite (Q i) n hn
  refine residuallyFinite_of_separating_family
    (fun i => (Stable.detector n (q i)).comp (CandidateSubgroup n ε).subtype) ?_
  intro g hg
  apply Subtype.ext
  change g.val = 1
  apply hinj
  rw [map_one]
  apply hsep
  intro i
  rw [Stable.map_of]
  exact congrArg Subtype.val (hg i)

end Candidate

/-- The statements about a coefficient ring that remain to be proved for the constructed
algebra `R(p)`. This is a proposition, not an assumption: nothing here is asserted to hold. -/
def CoefficientObligations (p : ℕ) : Prop :=
  ∃ (R : Type) (_ : Ring R) (_ : CharP R p) (_ : Infinite R) (ε : R →+* ZMod p) (n : ℕ),
    3 ≤ n ∧ Group.IsFinitelyPresented (Steinberg n R) ∧
    (∀ A : Matrix (Fin n) (Fin n) R, ε.mapMatrix A = 0 → IsNilpotent A) ∧
    Function.Injective (Stable.of R n) ∧
    (∀ z : StableSteinberg R, Stable.representation R z = 1 → Stable.map ε z = 1 →
      ∃ a : ℕ, z ^ p ^ a = 1) ∧
    ∃ (ι : Type) (Q : ι → Type) (_ : ∀ i, Ring (Q i)) (_ : ∀ i, Finite (Q i))
      (q : ∀ i, R →+* Q i),
      ∀ z : StableSteinberg R, (∀ i, Stable.map (q i) z = 1) → z = 1

/-- Manuscript Section 4 as a reduction: the existence theorem follows once the coefficient
obligations are established for every prime. -/
theorem target_of_obligations (h : ∀ p : ℕ, p.Prime → CoefficientObligations p) : Target := by
  intro p hp
  obtain ⟨R, _, _, _, ε, n, hn, hfp, hnil, hinj, htors, ι, Q, _, _, q, hsep⟩ := h p hp
  have : NeZero p := ⟨hp.ne_zero⟩
  exact ⟨CandidateSubgroup n ε, inferInstance, Candidate.infinite n ε hn,
    Candidate.finitelyPresented n ε hn, Candidate.residuallyFinite n ε hn hinj q hsep,
    Candidate.isPGroup n ε hp hn hnil hinj htors⟩

end
end AllPrimeGroups
