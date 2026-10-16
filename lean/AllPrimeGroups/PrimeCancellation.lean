/-
It imports the upstream modules through Algebra/MatrixTests, which must be built first
(`python3 scripts/build_upstream.py`).

Characteristic-p versions of the characteristic-two cancellation theorems in OpenAI's
PeriodicGroups/Algebra/{WordAlgebra,PacketIntervals,DirectCancellation,MatrixTests}.lean
(commit pinned in upstream/provenance.json; Apache-2.0, see upstream/OpenAI-LICENSE).
The proofs follow the upstream proofs, with complete symmetrization (more than (p-1)d² factors)
in place of the alternating sum (more than d² factors). The upstream modules are imported
untouched; nothing in them is modified.
-/
import OAI.GroupTheory.PeriodicGroups.Algebra.MatrixTests
import AllPrimeGroups.Symmetrization

namespace AllPrimeGroups.PrimeCancellation
open OAI OAI.SourceBurnside
open scoped BigOperators
open Classical
noncomputable section

section Packets
open OAI.SourceBurnside.Cancellation
variable {Γ : Type*} {K : Type*} [CommRing K] {p : ℕ} [CharP K p]

lemma sum_packet_permutations (hp : 0 < p) {d : ℕ} (W : Γ → Matrix (Fin d) (Fin d) K)
    (s : List Γ) (hm : (p - 1) * d ^ 2 < s.length) :
    (∑ σ : Equiv.Perm (Fin s.length), chunkWeight W (List.ofFn (s.get ∘ σ))) = 0 := by
  simpa only [chunkWeight, List.map_ofFn, Function.comp_def] using
    (matrix_symmetrization_eq_zero hp (fun i : Fin s.length => W (s.get i)) hm)

lemma sum_reorder_weight (hp : 0 < p) {d : ℕ} (W : Γ → Matrix (Fin d) (Fin d) K)
    (pk : Packet Γ) (hm : (p - 1) * d ^ 2 < pk.inside.length) :
    (∑ σ : Equiv.Perm (Fin pk.inside.length), chunkWeight W (pk.reorder σ)) = 0 := by
  simp only [Packet.reorder, chunkWeight_append]
  rw [← Finset.sum_mul, ← Finset.mul_sum, sum_packet_permutations hp W pk.inside hm,
    mul_zero, zero_mul]

/-- Upstream `Cancellation.packet_cancellation` with the characteristic-p threshold. -/
theorem packet_cancellation (hp : 0 < p) {d : ℕ} {V : Type*} [AddCommGroup V] [Module K V]
    (S : Finset (List Γ)) (W : Γ → Matrix (Fin d) (Fin d) K)
    (value : List Γ → V) (pick : List Γ → Packet Γ)
    (joins : ∀ s ∈ S, (pick s).join = s)
    (nodup : ∀ s ∈ S, (pick s).inside.Nodup)
    (long : ∀ s ∈ S, (p - 1) * d ^ 2 < (pick s).inside.length)
    (closed : ∀ s ∈ S, ∀ σ, (pick s).reorder σ ∈ S)
    (stable : ∀ s ∈ S, ∀ σ, (pick ((pick s).reorder σ)).key = (pick s).key)
    (same_value : ∀ s ∈ S, ∀ σ, value ((pick s).reorder σ) = value s)
    (i j : Fin d) :
    (∑ s ∈ S, chunkWeight W s i j • value s) = 0 := by
  let key := fun s => (pick s).key
  rw [← Finset.sum_fiberwise_of_maps_to (s := S) (t := S.image key)
    (fun s hs => Finset.mem_image.mpr ⟨s, hs, rfl⟩)
    (fun s => chunkWeight W s i j • value s)]
  apply Finset.sum_eq_zero
  intro z hz
  obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hz
  have hfiber : S.filter (fun t => key t = key s) =
      Finset.univ.image (pick s).reorder := by
    ext t
    constructor
    · intro ht
      obtain ⟨htS,htkey⟩ := Finset.mem_filter.mp ht
      obtain ⟨hb,ha,hperm⟩ := perm_of_key_eq htkey
      obtain ⟨σ,hσ⟩ := packet_perm_exists (pick s).inside (nodup s hs) (pick t).inside hperm
      refine Finset.mem_image.mpr ⟨σ,Finset.mem_univ _,?_⟩
      rw [Packet.reorder, hσ, ← hb, ← ha]
      exact joins t htS
    · intro ht
      obtain ⟨σ,_,rfl⟩ := Finset.mem_image.mp ht
      exact Finset.mem_filter.mpr ⟨closed s hs σ, stable s hs σ⟩
  rw [hfiber, Finset.sum_image]
  · simp_rw [same_value s hs]
    rw [← Finset.sum_smul]
    have hw := congrArg (fun A : Matrix (Fin d) (Fin d) K => A i j)
      (sum_reorder_weight hp W (pick s) (long s hs))
    simp only [Matrix.sum_apply, Matrix.zero_apply] at hw
    rw [hw, zero_smul]
  · exact (Packet.reorder_injective (pick s) (nodup s hs)).injOn

end Packets

section Intervals
variable {Γ : Type*}

/-- Upstream `PacketIntervals.select_long` for an arbitrary threshold `M` in place of `d^2`. -/
theorem select_long (len : Γ → ℕ) (s : List Γ) (a e b M : ℕ)
    (hb : ∀ c ∈ s, len c ≤ b) (he : e ≤ PacketIntervals.total len s)
    (hlong : b * (M + 3) < e - a) :
    M < (PacketIntervals.select len s a e).inside.length := by
  have ha : a + b ≤ e := by
    have hmul : b ≤ b * (M + 3) := by nlinarith
    omega
  have hr := PacketIntervals.select_inside_bound len s a e b hb ha he
  have hm : ∀ c ∈ (PacketIntervals.select len s a e).inside, len c ≤ b := by
    intro c hc
    apply hb
    rw [← PacketIntervals.select_join len s a e, PacketIntervals.Selection.join]
    simp [hc]
  have ht := PacketIntervals.total_le_length_mul len
    (PacketIntervals.select len s a e).inside b hm
  by_contra hn
  have hle : (PacketIntervals.select len s a e).inside.length ≤ M := by omega
  have hmul := Nat.mul_le_mul_right b hle
  nlinarith

end Intervals

section Chunks
open OAI.SourceBurnside.DirectCancellation
variable {Γ α T K A : Type*} [Fintype Γ] [CommRing K] {p : ℕ} [CharP K p]
  [Ring A] [Algebra K A]

/-- Upstream `DirectCancellation.chunkSum_eq_zero_of_ranges`, with a threshold `M` that
dominates the characteristic-p symmetrization bound. -/
theorem chunkSum_eq_zero_of_ranges (hp : 0 < p) {d b n M : ℕ} (hM : (p - 1) * d ^ 2 ≤ M)
    (label : Γ → List α) (hne : ∀ c, label c ≠ [])
    (hb : ∀ c, (label c).length ≤ b)
    (erase : α → T) (range : List T → ℕ × ℕ)
    (W : Γ → Matrix (Fin d) (Fin d) K) (f : α → A)
    (hrun : ∀ s : List Γ, (spell label s).length = n → eval f (spell label s) ≠ 0 →
      let a := (range ((spell label s).map erase)).1
      let e := (range ((spell label s).map erase)).2
      e ≤ (spell label s).length ∧ b*(M+3) < e-a ∧
      (((spell label s).drop a).take (e-a)).Nodup ∧
      ∃ t : T, (∀ x ∈ ((spell label s).drop a).take (e-a), erase x = t) ∧
        ∀ x y, erase x=t → erase y=t → Commute (f x) (f y))
    (i j : Fin d) : chunkSum label W f n i j = 0 := by
  let Q := (candidates Γ n).filter (fun s => (spell label s).length = n)
  let S := Q.filter (fun s => eval f (spell label s) ≠ 0)
  have hS {s : List Γ} (hs : s ∈ S) :
      s.length ≤ n ∧ (spell label s).length = n ∧ eval f (spell label s) ≠ 0 := by
    obtain ⟨hs,hne⟩ := Finset.mem_filter.mp hs
    obtain ⟨hs,hl⟩ := Finset.mem_filter.mp hs
    exact ⟨(mem_candidates n s).mp hs,hl,hne⟩
  let pick := pickPacket label erase range
  have info (s : List Γ) (hs : s ∈ S) :
      (range ((spell label s).map erase)).1 ≤ (spell label s).length ∧
      (spell label (pick s).inside).Nodup ∧ M < (pick s).inside.length ∧
      ∃ t : T, (∀ x ∈ spell label (pick s).inside, erase x=t) ∧
        ∀ x y, erase x=t → erase y=t → Commute (f x) (f y) := by
    obtain ⟨_,hn,hv⟩ := hS hs
    obtain ⟨he,hl,hd,t,hu,hc⟩ := hrun s hn hv
    let a := (range ((spell label s).map erase)).1
    let e := (range ((spell label s).map erase)).2
    have hmul : b ≤ b*(M+3) := by nlinarith
    have ha : a ≤ (spell label s).length := by dsimp [a,e] at *; omega
    have hae : PacketIntervals.total (fun c => (label c).length)
        (PacketIntervals.select (fun c => (label c).length) s a e).before ≤ e := by
      have ht := PacketIntervals.select_before_bound (fun c => (label c).length)
        s a e b (fun c _ => hb c)
      dsimp [a,e] at *
      omega
    have sub := select_spelling_sublist label s a e ha hae
    have lng := select_long (fun c => (label c).length) s a e b M
      (fun c _ => hb c) (by simpa only [length_spell] using he) hl
    refine ⟨ha,hd.sublist sub,lng,t,?_,hc⟩
    exact fun x hx => hu x (sub.subset hx)
  have same (s : List Γ) (hs : s ∈ S) (σ : Equiv.Perm (Fin (pick s).inside.length)) :
      eval f (spell label ((pick s).reorder σ)) = eval f (spell label s) := by
    obtain ⟨_,_,_,t,hu,hc⟩ := info s hs
    exact pickPacket_same_value label erase range f s t hu hc σ
  have hz := packet_cancellation hp S W (fun s => eval f (spell label s)) pick
    (fun s _ => pickPacket_join label erase range s)
    (fun s hs => nodup_of_spell_nodup label hne _ (info s hs).2.1)
    (fun s hs => hM.trans_lt (info s hs).2.2.1)
    (fun s hs σ => by
      obtain ⟨hlen,hn,hv⟩ := hS hs
      have hperm := reordered_perm (pick s) s (pickPacket_join label erase range s) σ
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_filter.mpr ⟨?_,?_⟩,?_⟩
      · exact (mem_candidates n _).mpr (hperm.length_eq.trans_le hlen)
      · exact (spell_perm label hperm).length_eq.trans hn
      · rw [same s hs σ]
        exact hv)
    (fun s hs σ => by
      obtain ⟨ha,_,_,t,hu,_⟩ := info s hs
      exact pickPacket_stable label erase range s ha t hu σ)
    same i j
  change (∑ s ∈ Q, Cancellation.chunkWeight W s i j • eval f (spell label s)) = 0
  rw [← hz]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro s _ hs
  have hv : eval f (spell label s) = 0 := by
    by_contra hv
    exact hs (Finset.mem_filter.mpr ⟨‹s ∈ Q›,hv⟩)
  simp [hv]

/-- Upstream `DirectCancellation.direct_cancellation` in characteristic p
(manuscript Lemma 17.1). -/
theorem direct_cancellation (hp : 0 < p) {d b q N M : ℕ} (hM : (p - 1) * d ^ 2 ≤ M)
    (label : Γ → List α) (hne : ∀ c, label c ≠ [])
    (hb : ∀ c, (label c).length ≤ b)
    (erase : α → T) (eligible : T → Prop) (f : α → A)
    (hcomm : ∀ t, eligible t → ∀ x y, erase x=t → erase y=t → Commute (f x) (f y))
    (hsquare : ∀ x, eligible (erase x) → f x*f x=0)
    (hlong : ∀ w : List α, N ≤ w.length → eval f w ≠ 0 →
      ∃ a e, EligibleInterval eligible q (w.map erase) a e)
    (hbound : 100*b*(M+3) < q)
    (W : Γ → Matrix (Fin d) (Fin d) K) (n : ℕ) (hn : N ≤ n) (i j : Fin d) :
    chunkSum label W f n i j = 0 := by
  apply chunkSum_eq_zero_of_ranges hp hM label hne hb erase (firstLongRun eligible q) W f
  intro s hlen hval
  have hs := firstLongRun_spec eligible q ((spell label s).map erase)
    (hlong _ (hlen ▸ hn) hval)
  obtain ⟨t,ht,hu⟩ := eligibleInterval_uniform erase eligible q (spell label s) _ _ hs
  obtain ⟨ha,he,hq,_⟩ := hs
  refine ⟨?_,?_,?_,t,hu,hcomm t ht⟩
  · simpa only [List.length_map] using he
  · nlinarith
  · apply eval_ne_zero_nodup f _
    · intro x hx y hy
      exact hcomm t ht x y (hu x hx) (hu y hy)
    · intro x hx
      exact hsquare x ((hu x hx).symm ▸ ht)
    · exact interval_eval_ne_zero f _ _ _ hval

end Chunks

section Tests
variable {K A : Type*} [CommRing K] {p : ℕ} [CharP K p] [Ring A] [Algebra K A]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {α Γ : Type*} [Fintype Γ]

/-- Upstream `MatrixTests.direct_vanish` in characteristic p. -/
lemma direct_vanish (hp : 0 < p) {T : Type*} {d b q N M : ℕ} (hM : (p - 1) * d ^ 2 ≤ M)
    (label : Γ → List α) (hne : ∀c,label c≠[]) (hb : ∀c,(label c).length ≤ b)
    (erase : α → T) (eligible : T → Prop) (f : α → A)
    (hcomm : ∀t,eligible t → ∀x y,erase x=t → erase y=t → Commute (f x) (f y))
    (hsquare : ∀x,eligible (erase x) → f x*f x=0)
    (hlong : ∀w : List α,N ≤ w.length → DirectCancellation.eval f w≠0 →
      ∃a e,DirectCancellation.EligibleInterval eligible q (w.map erase) a e)
    (hbound : 100*b*(M+3)<q) (W : Γ → Matrix (Fin d) (Fin d) K) :
    ∀n,N ≤ n → MatrixTests.chunkSum label W f n=0 := by
  intro n hn
  ext i j
  rw [MatrixTests.chunkSum_entry]
  exact direct_cancellation hp hM label hne hb erase eligible f hcomm hsquare hlong hbound
    W n hn i j

/-- Upstream `MatrixTests.direct_vanish_finite` in characteristic p. -/
lemma direct_vanish_finite (hp : 0 < p) {T : Type*} {b q N M : ℕ}
    (hM : (p - 1) * (Fintype.card ι) ^ 2 ≤ M)
    (label : Γ → List α) (hne : ∀c,label c≠[]) (hb : ∀c,(label c).length ≤ b)
    (erase : α → T) (eligible : T → Prop) (f : α → A)
    (hcomm : ∀t,eligible t → ∀x y,erase x=t → erase y=t → Commute (f x) (f y))
    (hsquare : ∀x,eligible (erase x) → f x*f x=0)
    (hlong : ∀w : List α,N ≤ w.length → DirectCancellation.eval f w≠0 →
      ∃a e,DirectCancellation.EligibleInterval eligible q (w.map erase) a e)
    (hbound : 100*b*(M+3)<q) (W : Γ → Matrix ι ι K) :
    ∀n,N ≤ n → MatrixTests.chunkSum label W f n=0 := by
  intro n hn
  apply (Matrix.reindexRingEquiv A (Fintype.equivFin ι)).injective
  rw [map_zero,MatrixTests.reindex_chunkSum]
  exact direct_vanish hp hM label hne hb erase eligible f hcomm hsquare hlong hbound _ n hn

end Tests

end
end AllPrimeGroups.PrimeCancellation
