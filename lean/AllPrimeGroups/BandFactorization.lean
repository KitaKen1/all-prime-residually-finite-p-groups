/-
Strip conjugation, band transport, removal of the wrap entry of a cyclic shift, stable
uniqueness, and stable basis change, adapted from OpenAI
PeriodicGroups/Steinberg/BandFactorization.lean (commit pinned in upstream/provenance.json;
Apache-2.0, see upstream/OpenAI-LICENSE).
The upstream file fixes the two-element field for numerical matrices; here the prime field
is `ZMod ℓ` for a prime ℓ. The parts of the upstream file about the concrete word algebra and
the lifting of invertible numerical matrices are not included here.
-/
import AllPrimeGroups.BlockEmbeddings

namespace AllPrimeGroups

section
universe u v w
variable {ℓ : ℕ} [Fact ℓ.Prime]
namespace Kernel
noncomputable section
open Classical
variable {n N : ℕ} {R : Type*} [Ring R]
lemma left_conjugate_strip_root (H L : Finset (Fin n)) (hd : Disjoint H L)
    (p : Root n) (hr : p.row∈H) (hc : p.col∈H) (a : R)
    (q : RectIndex H L) (b : R) :
    Steinberg.x p a*Steinberg.x (rectPosition H L hd q) b*(Steinberg.x p a)⁻¹∈Strip H L hd := by
  have hrow : p.row≠q.2.val := fun he=>Finset.disjoint_left.mp hd hr (he.symm ▸ q.2.property)
  by_cases he : p.col=q.1.val
  · have hp : p=⟨p.row,q.1.val,he ▸ p.ne⟩ := by cases p;cases he;rfl
    rw [hp]
    dsimp only [rectPosition]
    rw [Steinberg.conjugate_chain p.row q.1.val q.2.val (he ▸ p.ne) (rectPosition H L hd q).ne hrow a b]
    apply (Strip H L hd).mul_mem
    · exact Subgroup.subset_closure ⟨(⟨p.row,hr⟩,q.2),a*b,rfl⟩
    · exact Subgroup.subset_closure ⟨q,b,rfl⟩
  · rw [Steinberg.conjugate_commute p (rectPosition H L hd q) he hrow]
    exact Subgroup.subset_closure ⟨q,b,rfl⟩
lemma left_conjugate_strip (H L : Finset (Fin n)) (hd : Disjoint H L)
    (p : Root n) (hr : p.row∈H) (hc : p.col∈H) (a : R)
    {g : Steinberg n R} (hg : g∈Strip H L hd) :
    Steinberg.x p a*g*(Steinberg.x p a)⁻¹∈Strip H L hd := by
  have Hle : Strip H L hd ≤ (Strip H L hd).comap (MulAut.conj (Steinberg.x p a)).toMonoidHom := by
    apply (Subgroup.closure_le _).mpr
    rintro g ⟨q,b,rfl⟩
    exact left_conjugate_strip_root H L hd p hr hc a q b
  exact Hle hg
lemma side_root_normalizes (H L : Finset (Fin n)) (hd : Disjoint H L)
    (p : Root n) (h : (p.row∈H ∧ p.col∈H) ∨ (p.row∈L ∧ p.col∈L)) (a : R) :
    Steinberg.x p a∈Subgroup.normalizer (Strip (R:=R) H L hd : Set (Steinberg n R)) := by
  have hh (b : R) {g : Steinberg n R} (hg : g∈Strip H L hd) :
      Steinberg.x p b*g*(Steinberg.x p b)⁻¹∈Strip H L hd := by
    rcases h with ⟨hr,hc⟩|⟨hr,hc⟩
    · exact left_conjugate_strip H L hd p hr hc b hg
    · exact right_conjugate_strip H L hd p hr hc b hg
  apply Subgroup.mem_normalizer_iff.mpr
  intro g
  constructor
  · exact hh a
  · intro hg
    have he := hh (-a) hg
    simp only [Steinberg.x_neg,inv_inv] at he
    simpa [mul_assoc] using he
lemma strip_mono {H L H' L' : Finset (Fin n)} (hd : Disjoint H L) (hd' : Disjoint H' L')
    (hH : H⊆H') (hL : L⊆L') : Strip (R:=R) H L hd≤Strip H' L' hd' := by
  apply (Subgroup.closure_le _).mpr
  rintro g ⟨q,a,rfl⟩
  exact Subgroup.subset_closure ⟨(⟨q.1.val,hH q.1.property⟩,⟨q.2.val,hL q.2.property⟩),a,rfl⟩
lemma blockRoot_mem_subgroup (p : Root n) (A : Matrix (Fin N) (Fin N) R)
    (S : Subgroup (Steinberg (n*N) R))
    (h : ∀s t,Steinberg.x (blockPosition p (s,t)) (A s t)∈S) : blockRoot p A∈S := by
  change Finset.noncommProd Finset.univ
    (fun st : Fin N×Fin N=>Steinberg.x (blockPosition p st) (A st.1 st.2))
    (fun st _ uv _ _=>block_factors_commute p st uv _ _)∈S
  apply Subgroup.noncommProd_mem
  intro st _
  exact h st.1 st.2
lemma blockRoot_commutes_element (p : Root n) (A : Matrix (Fin N) (Fin N) R)
    (g : Steinberg (n*N) R)
    (h : ∀s t,Commute (Steinberg.x (blockPosition p (s,t)) (A s t)) g) :
    Commute (blockRoot p A) g := by
  change Commute (Finset.noncommProd Finset.univ
    (fun st : Fin N×Fin N=>Steinberg.x (blockPosition p st) (A st.1 st.2))
    (fun st _ uv _ _=>block_factors_commute p st uv _ _)) g
  exact (Finset.noncommProd_commute _ _ _ g (fun st _=>(h st.1 st.2).symm)).symm

theorem block_conjugate_strip
    (H L H' L' : Finset (Fin (n*N))) (hd : Disjoint H L) (hd' : Disjoint H' L')
    (hH : H⊆H') (hL : L⊆L') (p : Root n) (A : Matrix (Fin N) (Fin N) R)
    (hsource : ∀s t,A s t≠0→blockIndex p.col t∈H→blockIndex p.row s∈H')
    (htarget : ∀s t,A s t≠0→blockIndex p.row s∈L→blockIndex p.col t∈L')
    {g : Steinberg (n*N) R} (hg : g∈Strip H L hd) :
    blockRoot p A*g*(blockRoot p A)⁻¹∈Strip H' L' hd' := by
  let near (s t : Fin N) : Prop :=
    (blockIndex p.row s∈H' ∧ blockIndex p.col t∈H') ∨
    (blockIndex p.row s∈L' ∧ blockIndex p.col t∈L')
  let B : Matrix (Fin N) (Fin N) R := fun s t=>if near s t then A s t else 0
  let C : Matrix (Fin N) (Fin N) R := fun s t=>if near s t then 0 else A s t
  have hs : A=B+C := by ext s t;change A s t=(if near s t then A s t else 0)+(if near s t then 0 else A s t);split_ifs <;> simp
  have hB : blockRoot p B∈Subgroup.normalizer (Strip (R:=R) H' L' hd' : Set (Steinberg (n*N) R)) := by
    apply blockRoot_mem_subgroup
    intro s t
    by_cases hn : near s t
    · change Steinberg.x (blockPosition p (s,t)) (if near s t then A s t else 0)∈_
      rw [ite_eq_left hn]
      exact side_root_normalizes H' L' hd' _ hn _
    · change Steinberg.x (blockPosition p (s,t)) (if near s t then A s t else 0)∈_
      rw [ite_eq_right hn,Steinberg.x_zero]
      exact Subgroup.one_mem _
  have hCroot (q : RectIndex H L) (a : R) :
      Commute (blockRoot p C) (Steinberg.x (rectPosition H L hd q) a) := by
    apply blockRoot_commutes_element
    intro s t
    by_cases hn : near s t
    · simp only [C,ite_eq_left hn,Steinberg.x_zero,Commute.one_left]
    · by_cases hz : A s t=0
      · simp only [C,ite_eq_right hn,hz,Steinberg.x_zero,Commute.one_left]
      · change Commute (Steinberg.x (blockPosition p (s,t)) (if near s t then 0 else A s t)) _
        rw [ite_eq_right hn]
        apply Steinberg.x_commute
        · intro he
          change blockIndex p.col t=q.1.val at he
          have ht : blockIndex p.col t∈H := he.symm ▸ q.1.property
          exact hn (Or.inl ⟨hsource s t hz ht,hH ht⟩)
        · intro he
          change blockIndex p.row s=q.2.val at he
          have hr : blockIndex p.row s∈L := he.symm ▸ q.2.property
          exact hn (Or.inr ⟨hL hr,htarget s t hz hr⟩)
  have hC : blockRoot p C*g*(blockRoot p C)⁻¹=g := by
    have he : Strip H L hd≤(MulAut.conj (blockRoot p C)).toMonoidHom.eqLocus (MonoidHom.id _) := by
      apply (Subgroup.closure_le _).mpr
      rintro _ ⟨q,a,rfl⟩
      exact CommutatorCalculus.conj_of_commute (hCroot q a)
    exact he hg
  rw [hs,blockRoot_add,mul_inv_rev]
  have he : blockRoot p B*blockRoot p C*g*((blockRoot p C)⁻¹*(blockRoot p B)⁻¹)=
      blockRoot p B*(blockRoot p C*g*(blockRoot p C)⁻¹)*(blockRoot p B)⁻¹ := by group
  rw [he,hC]
  exact (Subgroup.mem_normalizer_iff.mp hB g).mp (strip_mono hd hd' hH hL hg)
end
end Kernel

namespace Kernel
noncomputable section
open Classical
variable {n N : ℕ} {R : Type*} [Ring R]
def highBand (w : ℕ) : Finset (Fin (n*N)) := Finset.univ.filter (fun i=>N ≤ innerHeight i+w)
def lowBand (w : ℕ) : Finset (Fin (n*N)) := Finset.univ.filter (fun i=>innerHeight i<w)
lemma bands_disjoint (w : ℕ) (h : 2*w ≤ N) : Disjoint (highBand (n:=n) (N:=N) w) (lowBand w) := by
  apply Finset.disjoint_left.mpr
  intro i hi hl
  simp only [highBand,lowBand,Finset.mem_filter,Finset.mem_univ,true_and] at hi hl
  omega
lemma highBand_mono {v w : ℕ} (h : v ≤ w) : highBand (n:=n) (N:=N) v⊆highBand w := by
  intro i hi
  simp only [highBand,Finset.mem_filter,Finset.mem_univ,true_and] at hi ⊢
  omega
lemma lowBand_mono {v w : ℕ} (h : v ≤ w) : lowBand (n:=n) (N:=N) v⊆lowBand w := by
  intro i hi
  simp only [lowBand,Finset.mem_filter,Finset.mem_univ,true_and] at hi ⊢
  omega
def bandStrip (w : ℕ) (h : 2*w ≤ N) : Subgroup (Steinberg (n*N) R) :=
  Strip (highBand w) (lowBand w) (bands_disjoint w h)
lemma bandStrip_mono {v w : ℕ} (hv : 2*v ≤ N) (hw : 2*w ≤ N) (h : v ≤ w) :
    bandStrip (n:=n) (R:=R) v hv ≤ bandStrip w hw :=
  strip_mono _ _ (highBand_mono h) (lowBand_mono h)
lemma blockRoot_neg (p : Root n) (A : Matrix (Fin N) (Fin N) R) :
    blockRoot p (-A)=(blockRoot p A)⁻¹ := map_inv (blockHom p) _

lemma band_transport (d w : ℕ) (h : 2*(w+d) ≤ N) (hw : 2*w ≤ N)
    (p : Root n) (A : Matrix (Fin N) (Fin N) R)
    (hA : ∀s t,A s t≠0→t.val ≤ s.val+d)
    {g : Steinberg (n*N) R} (hg : g∈bandStrip w hw) :
    blockRoot p A*g*(blockRoot p A)⁻¹∈bandStrip (w+d) h := by
  apply block_conjugate_strip (highBand w) (lowBand w) (highBand (w+d)) (lowBand (w+d))
    (bands_disjoint w hw) (bands_disjoint (w+d) h)
    (highBand_mono (Nat.le_add_right _ _)) (lowBand_mono (Nat.le_add_right _ _)) p A _ _ hg
  · intro s t hst ht
    simp only [highBand,Finset.mem_filter,Finset.mem_univ,true_and,innerHeight_blockIndex] at ht ⊢
    have := hA s t hst
    omega
  · intro s t hst hs
    simp only [lowBand,Finset.mem_filter,Finset.mem_univ,true_and,innerHeight_blockIndex] at hs ⊢
    have := hA s t hst
    omega
lemma wrap_block_mem (d : ℕ) (h : 2*d ≤ N) (p : Root n) (B : Matrix (Fin N) (Fin N) R)
    (hB : ∀s t,B s t≠0→N ≤ s.val+d ∧ t.val<d) : blockRoot p B∈bandStrip d h := by
  apply blockRoot_mem_subgroup
  intro s t
  by_cases hb : B s t=0
  · rw [hb,Steinberg.x_zero];exact Subgroup.one_mem _
  · have he := hB s t hb
    have hs : blockIndex p.row s∈highBand (n:=n) d := by simpa [highBand] using he.1
    have ht : blockIndex p.col t∈lowBand (n:=n) d := by simpa [lowBand] using he.2
    exact Subgroup.subset_closure ⟨(⟨_,hs⟩,⟨_,ht⟩),B s t,rfl⟩
structure BlockFactor (n N : ℕ) (R : Type*) where
  position : Root n
  main : Matrix (Fin N) (Fin N) R
  correction : Matrix (Fin N) (Fin N) R
def wrappedProduct (l : List (BlockFactor n N R)) : Steinberg (n*N) R :=
  (l.map (fun x=>blockRoot x.position (x.main+x.correction))).prod
def truncatedProduct (l : List (BlockFactor n N R)) : Steinberg (n*N) R :=
  (l.map (fun x=>blockRoot x.position x.main)).prod
def BlockFactor.Bounded (d : ℕ) (x : BlockFactor n N R) : Prop :=
  (∀s t,x.main s t≠0→t.val ≤ s.val+d) ∧
  (∀s t,x.correction s t≠0→N ≤ s.val+d ∧ t.val<d)

theorem band_wrap_collect (d : ℕ) (l : List (BlockFactor n N R)) :
    (∀x∈l,x.Bounded d)→∀(h : 2*((l.length+1)*d) ≤ N),
    ∃z∈bandStrip ((l.length+1)*d) h,wrappedProduct l=truncatedProduct l*z := by
  induction l using List.reverseRecOn with
  | nil =>
    intro hl h
    exact ⟨1,Subgroup.one_mem _,by simp [wrappedProduct,truncatedProduct]⟩
  | append_singleton l x ih =>
    intro hl h
    have h' : 2*((l.length+1)*d+d) ≤ N := by
      simp only [List.length_append,List.length_singleton] at h
      convert h using 1; ring
    have hp : 2*((l.length+1)*d) ≤ N := by omega
    have hx := hl x (by simp)
    obtain ⟨z,hz,he⟩ := ih (fun y hy=>hl y (List.mem_append_left _ hy)) hp
    have hneg : ∀s t,(-x.main) s t≠0→t.val ≤ s.val+d := by
      intro s t ht
      exact hx.1 s t (fun hz=>ht (by simp [hz]))
    have hc := band_transport d ((l.length+1)*d) h' hp x.position (-x.main) hneg hz
    rw [blockRoot_neg,inv_inv] at hc
    have hd : 2*d ≤ N := by nlinarith [Nat.zero_le (l.length*d)]
    have hf0 := wrap_block_mem d hd x.position x.correction hx.2
    have hwidth : d ≤ (l.length+1)*d+d := by omega
    have hf := bandStrip_mono hd h' hwidth hf0
    refine ⟨((blockRoot x.position x.main)⁻¹*z*blockRoot x.position x.main)*blockRoot x.position x.correction,?_,?_⟩
    · have hm := Subgroup.mul_mem _ hc hf
      simpa only [List.length_append,List.length_singleton,Nat.add_mul,Nat.one_mul,add_assoc] using hm
    · simp only [wrappedProduct,truncatedProduct,List.map_append,List.map_cons,List.map_nil,
        List.prod_append,List.prod_cons,List.prod_nil,mul_one] at he ⊢
      rw [he,blockRoot_add]
      group

theorem band_wrap_removal (d : ℕ) (l : List (BlockFactor n N R))
    (hl : ∀x∈l,x.Bounded d) (h : 2*((l.length+1)*d) ≤ N)
    (hW : Elementary.representation (wrappedProduct l)=1)
    (hD : Elementary.representation (truncatedProduct l)=1) :
    wrappedProduct l=truncatedProduct l := by
  obtain ⟨z,hz,he⟩ := band_wrap_collect d l hl h
  have hm := congrArg Elementary.representation he
  rw [map_mul,hD,one_mul,hW] at hm
  have hz1 := strip_faithful (highBand ((l.length+1)*d)) (lowBand ((l.length+1)*d))
    (bands_disjoint _ h) hz hm.symm
  simpa only [hz1,mul_one] using he
end
end Kernel

namespace Kernel
noncomputable section
open Classical
variable {N : ℕ} {R : Type*} [Ring R]

def truncatedShift (N : ℕ) (R : Type*) [Zero R] [One R] : Matrix (Fin N) (Fin N) R :=
  fun s t=>if s.val+1=t.val then 1 else 0
def cyclicShift (N : ℕ) (R : Type*) [Zero R] [One R] : Matrix (Fin N) (Fin N) R :=
  fun s t=>if (s.val+1)%N=t.val then 1 else 0
lemma truncatedShift_pow (b : ℕ) (s t : Fin N) :
    (truncatedShift N R^b) s t=if s.val+b=t.val then 1 else 0 := by
  induction b generalizing s t with
  | zero => simp [Matrix.one_apply,Fin.ext_iff]
  | succ b ih =>
    rw [pow_succ,Matrix.mul_apply]
    simp only [ih,truncatedShift]
    by_cases h : s.val+b<N
    · let k : Fin N := ⟨s.val+b,h⟩
      rw [Finset.sum_eq_single k]
      · simp [k,add_assoc]
      · intro u _ huk
        have he : s.val+b≠u.val := by intro he;apply huk;apply Fin.ext;exact he.symm
        simp only [ite_eq_right he,zero_mul]
      · simp
    · have hr : s.val+(b+1)≠t.val := by have := t.isLt;omega
      rw [ite_eq_right hr]
      apply Finset.sum_eq_zero
      intro u _
      have he : s.val+b≠u.val := by have := u.isLt;omega
      simp only [ite_eq_right he,zero_mul]
lemma cyclicShift_pow (hN : 0<N) (b : ℕ) (s t : Fin N) :
    (cyclicShift N R^b) s t=if (s.val+b)%N=t.val then 1 else 0 := by
  induction b generalizing s t with
  | zero => simp [Matrix.one_apply,Fin.ext_iff,Nat.mod_eq_of_lt s.isLt]
  | succ b ih =>
    rw [pow_succ,Matrix.mul_apply]
    simp only [ih,cyclicShift]
    let k : Fin N := ⟨(s.val+b)%N,Nat.mod_lt _ hN⟩
    rw [Finset.sum_eq_single k]
    · simp only [k]
      have he : ((s.val+b)%N+1)%N=(s.val+(b+1))%N := by
        rw [Nat.mod_add_mod,add_assoc]
      rw [he]
      simp
    · intro u _ huk
      have he : (s.val+b)%N≠u.val := by intro he;apply huk;apply Fin.ext;exact he.symm
      simp only [ite_eq_right he,zero_mul]
    · simp
lemma truncatedShift_upper : (truncatedShift N R).IsUpperTriangular := by
  intro s t hts
  have he : s.val+1≠t.val := by change t.val<s.val at hts;omega
  exact ite_eq_right he
lemma truncatedShift_diag (s : Fin N) : truncatedShift N R s s=0 := by
  exact ite_eq_right (by omega)
variable [Algebra (ZMod ℓ) R]
lemma numeric_truncatedShift : numericMatrix (R:=R) (truncatedShift N (ZMod ℓ))=truncatedShift N R := by
  ext s t
  change algebraMap (ZMod ℓ) R (if s.val+1=t.val then 1 else 0)=(if s.val+1=t.val then 1 else 0)
  split_ifs <;> simp
lemma numeric_cyclicShift : numericMatrix (R:=R) (cyclicShift N (ZMod ℓ))=cyclicShift N R := by
  ext s t
  change algebraMap (ZMod ℓ) R (if (s.val+1)%N=t.val then 1 else 0)=(if (s.val+1)%N=t.val then 1 else 0)
  split_ifs <;> simp
lemma truncated_eval_monomial (b : ℕ) (a : R) (s t : Fin N) :
    matrixEval (truncatedShift N (ZMod ℓ)) (Polynomial.monomial b a) s t=
      if s.val+b=t.val then a else 0 := by
  change Polynomial.eval₂ (Matrix.scalar (Fin N)) (numericMatrix (truncatedShift N (ZMod ℓ)))
    (Polynomial.monomial b a) s t=_
  rw [Polynomial.eval₂_monomial,Matrix.scalar_apply,Matrix.diagonal_mul,numeric_truncatedShift,truncatedShift_pow]
  split_ifs <;> simp
lemma cyclic_eval_monomial (hN : 0<N) (b : ℕ) (a : R) (s t : Fin N) :
    matrixEval (cyclicShift N (ZMod ℓ)) (Polynomial.monomial b a) s t=
      if (s.val+b)%N=t.val then a else 0 := by
  change Polynomial.eval₂ (Matrix.scalar (Fin N)) (numericMatrix (cyclicShift N (ZMod ℓ)))
    (Polynomial.monomial b a) s t=_
  rw [Polynomial.eval₂_monomial,Matrix.scalar_apply,Matrix.diagonal_mul,numeric_cyclicShift,cyclicShift_pow hN]
  split_ifs <;> simp
end
end Kernel

namespace Kernel
noncomputable section
open Classical
variable {n N : ℕ} {R : Type*} [Ring R] [Algebra (ZMod ℓ) R]
lemma truncated_eval_outside (d : ℕ) (a : Polynomial R) (ha : a.natDegree ≤ d)
    (s t : Fin N) (hst : s.val+d<t.val) :
    matrixEval (truncatedShift N (ZMod ℓ)) a s t=0 := by
  conv_lhs => rw [a.as_sum_support,map_sum,Matrix.sum_apply]
  apply Finset.sum_eq_zero
  intro b hb
  rw [truncated_eval_monomial]
  have hb' := (Polynomial.le_natDegree_of_mem_supp b hb).trans ha
  exact ite_eq_right (by omega)
lemma truncated_eval_band (d : ℕ) (a : Polynomial R) (ha : a.natDegree ≤ d)
    (s t : Fin N) (hne : matrixEval (truncatedShift N (ZMod ℓ)) a s t≠0) :
    t.val ≤ s.val+d := by
  by_contra h
  exact hne (truncated_eval_outside d a ha s t (by omega))
lemma mod_no_wrap_or_low (_hN : 0<N) (d b : ℕ) (hd : d<N) (hb : b ≤ d)
    (s t : Fin N) (hout : s.val+d<N ∨ d ≤ t.val) :
    ((s.val+b)%N=t.val)↔(s.val+b=t.val) := by
  by_cases hw : s.val+b<N
  · rw [Nat.mod_eq_of_lt hw]
  · have hs := s.isLt
    have ht := t.isLt
    have hmod : (s.val+b)%N=s.val+b-N := Nat.mod_eq_sub_mod (by omega) |>.trans (Nat.mod_eq_of_lt (by omega))
    rw [hmod]
    rcases hout with hout|hout <;> omega
lemma shift_evals_agree_outside (hN : 0<N) (d : ℕ) (hd : d<N)
    (a : Polynomial R) (ha : a.natDegree ≤ d) (s t : Fin N)
    (hout : s.val+d<N ∨ d ≤ t.val) :
    matrixEval (cyclicShift N (ZMod ℓ)) a s t=
      matrixEval (truncatedShift N (ZMod ℓ)) a s t := by
  conv_lhs => rw [a.as_sum_support,map_sum,Matrix.sum_apply]
  conv_rhs => rw [a.as_sum_support,map_sum,Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro b hb
  rw [cyclic_eval_monomial hN,truncated_eval_monomial]
  have hbd := (Polynomial.le_natDegree_of_mem_supp b hb).trans ha
  simp only [mod_no_wrap_or_low hN d b hd hbd s t hout]
lemma cyclic_difference_wrap (hN : 0<N) (d : ℕ) (hd : d<N)
    (a : Polynomial R) (ha : a.natDegree ≤ d) (s t : Fin N)
    (hne : (matrixEval (cyclicShift N (ZMod ℓ)) a-
      matrixEval (truncatedShift N (ZMod ℓ)) a) s t≠0) :
    N ≤ s.val+d ∧ t.val<d := by
  by_contra h
  have hout : s.val+d<N ∨ d ≤ t.val := by omega
  exact hne (sub_eq_zero.mpr (shift_evals_agree_outside hN d hd a ha s t hout))
end
end Kernel

namespace Kernel
noncomputable section
open Classical
variable {n N : ℕ} {R : Type*} [Ring R]
def rootWord (l : List (Root n×R)) : Steinberg n R := (l.map (fun pa=>Steinberg.x pa.1 pa.2)).prod
lemma rootWord_append (l k : List (Root n×R)) : rootWord (l++k)=rootWord l*rootWord k := by
  simp [rootWord]
lemma rootWord_inverse (l : List (Root n×R)) :
    rootWord (l.reverse.map (fun pa=>(pa.1,-pa.2)))=(rootWord l)⁻¹ := by
  induction l with
  | nil => simp [rootWord]
  | cons pa l ih =>
    simp only [List.reverse_cons,List.map_append,rootWord_append,List.map_cons,List.map_nil,ih]
    simp [rootWord,Steinberg.x_neg,mul_inv_rev]
lemma exists_rootWord (g : Steinberg n R) : ∃l : List (Root n×R),rootWord l=g := by
  have hg : g∈Subgroup.closure (Set.range (fun pa : Root n×R=>Steinberg.x pa.1 pa.2)) := by
    rw [Steinberg.closure_range_x];exact Subgroup.mem_top g
  induction hg using Subgroup.closure_induction with
  | mem g hg => obtain ⟨pa,rfl⟩:=hg;exact ⟨[pa],by simp [rootWord]⟩
  | one => exact ⟨[],by simp [rootWord]⟩
  | mul g h hg hh ihg ihh =>
    obtain ⟨l,rfl⟩:=ihg
    obtain ⟨k,rfl⟩:=ihh
    exact ⟨l++k,rootWord_append l k⟩
  | inv g hg ih =>
    obtain ⟨l,rfl⟩:=ih
    exact ⟨l.reverse.map (fun pa=>(pa.1,-pa.2)),rootWord_inverse l⟩
variable [Algebra (ZMod ℓ) R]
@[simp] lemma matrixSteinbergEval_x (T : Matrix (Fin N) (Fin N) (ZMod ℓ))
    (p : Root n) (a : Polynomial R) :
    matrixSteinbergEval T (Steinberg.x p a)=blockRoot p (matrixEval T a) := by
  rw [matrixSteinbergEval,MonoidHom.comp_apply,Steinberg.map_x,blockMap_x]
  rfl
def wrapFactors (l : List (Root n×Polynomial R)) : List (BlockFactor n N R) :=
  l.map (fun pa=>⟨pa.1,matrixEval (truncatedShift N (ZMod ℓ)) pa.2,
    matrixEval (cyclicShift N (ZMod ℓ)) pa.2-matrixEval (truncatedShift N (ZMod ℓ)) pa.2⟩)
lemma wrappedProduct_eq (l : List (Root n×Polynomial R)) :
    wrappedProduct (wrapFactors (ℓ:=ℓ) (N:=N) l)=matrixSteinbergEval (cyclicShift N (ZMod ℓ)) (rootWord l) := by
  induction l with
  | nil => simp [wrappedProduct,wrapFactors,rootWord]
  | cons pa l ih =>
    simp only [wrapFactors,List.map_cons,wrappedProduct,List.prod_cons] at ih ⊢
    rw [ih]
    simp only [rootWord,List.map_cons,List.prod_cons,map_mul,matrixSteinbergEval_x]
    congr 2
    abel
lemma truncatedProduct_eq (l : List (Root n×Polynomial R)) :
    truncatedProduct (wrapFactors (ℓ:=ℓ) (N:=N) l)=matrixSteinbergEval (truncatedShift N (ZMod ℓ)) (rootWord l) := by
  induction l with
  | nil => simp [truncatedProduct,wrapFactors,rootWord]
  | cons pa l ih =>
    simp only [wrapFactors,List.map_cons,truncatedProduct,List.prod_cons] at ih ⊢
    rw [ih]
    simp only [rootWord,List.map_cons,List.prod_cons,map_mul,matrixSteinbergEval_x]
lemma wrapFactors_bounded (hN : 0<N) (d : ℕ) (hd : d<N) (l : List (Root n×Polynomial R))
    (hl : ∀pa∈l,pa.2.natDegree ≤ d) : ∀x∈wrapFactors (ℓ:=ℓ) (N:=N) l,x.Bounded d := by
  rintro _ hx
  obtain ⟨pa,hpa,rfl⟩ := List.mem_map.mp hx
  exact ⟨truncated_eval_band d pa.2 (hl pa hpa),cyclic_difference_wrap hN d hd pa.2 (hl pa hpa)⟩

theorem wrap_removal (l : List (Root n×Polynomial R)) (_hm : 1 ≤ l.length)
    (d : ℕ) (hl : ∀pa∈l,pa.2.natDegree ≤ d)
    (hN : 2*(l.length+1)*max 1 d<N)
    (hu : Elementary.representation (rootWord l)=1) :
    matrixSteinbergEval (cyclicShift N (ZMod ℓ)) (rootWord l)=
      matrixSteinbergEval (truncatedShift N (ZMod ℓ)) (rootWord l) := by
  have hpos : 0<N := by omega
  have hd : max 1 d<N := by nlinarith [Nat.zero_le (l.length*max 1 d)]
  have hb : 2*(((wrapFactors (ℓ:=ℓ) (N:=N) l).length+1)*max 1 d) ≤ N := by
    simp only [wrapFactors,List.length_map]
    nlinarith
  have he := band_wrap_removal (max 1 d) (wrapFactors (ℓ:=ℓ) (N:=N) l)
    (wrapFactors_bounded hpos (max 1 d) hd l (fun pa hpa=>(hl pa hpa).trans (Nat.le_max_right _ _))) hb
  rw [wrappedProduct_eq,truncatedProduct_eq] at he
  exact he (matrixSteinbergEval_kernel _ _ hu) (matrixSteinbergEval_kernel _ _ hu)
end
end Kernel

namespace Kernel
noncomputable section
variable {n m : ℕ} {S R : Type*} [Ring S] [Ring R]

theorem stable_uniqueness (hn : 3 ≤ n) (f g : Steinberg n S →* Steinberg m R)
    (he : ∀u,Elementary.representation (f u)=Elementary.representation (g u)) :
    padSteinberg.comp f=padSteinberg.comp g := by
  let H := Steinberg (m+1) R
  let F : Steinberg n S →* H := padSteinberg.comp f
  let G : Steinberg n S →* H := padSteinberg.comp g
  have hz (u : Steinberg n S) : F u*(G u)⁻¹∈Subgroup.center H := by
    have hh : Elementary.representation (f u*(g u)⁻¹)=1 := by
      rw [map_mul,map_inv,he u,mul_inv_cancel]
    have hc := stabilized_kernel_central (f u*(g u)⁻¹) hh
    simpa only [F,G,H,MonoidHom.comp_apply,map_mul,map_inv] using hc
  let : CommGroup (Subgroup.center H) :=
    { (inferInstance : Group (Subgroup.center H)) with
      mul_comm := fun a b=>Subtype.ext (b.property.comm a).symm }
  let ratio : Steinberg n S →* Subgroup.center H :=
    { toFun := fun u=>⟨F u*(G u)⁻¹,hz u⟩
      map_one' := by apply Subtype.ext;simp
      map_mul' := by
        intro u v
        apply Subtype.ext
        change F (u*v)*(G (u*v))⁻¹=(F u*(G u)⁻¹)*(F v*(G v)⁻¹)
        rw [map_mul,map_mul,mul_inv_rev]
        have hc : (F v*(G v)⁻¹)*(G u)⁻¹=(G u)⁻¹*(F v*(G v)⁻¹) :=
          (Subgroup.mem_center_iff.mp (hz v) ((G u)⁻¹)).symm
        calc
          _ = F u*((F v*(G v)⁻¹)*(G u)⁻¹) := by group
          _ = F u*((G u)⁻¹*(F v*(G v)⁻¹)) := congrArg (fun x=>F u*x) hc
          _ = _ := by group }
  have hr := Steinberg.hom_to_commGroup_trivial hn ratio
  apply MonoidHom.ext
  intro u
  have hu := congrArg Subtype.val (DFunLike.congr_fun hr u)
  change F u*(G u)⁻¹=1 at hu
  exact mul_inv_eq_one.mp hu
end
end Kernel
namespace Kernel
noncomputable section
open Classical
variable {n N : ℕ} {R : Type*} [Ring R]

def coefficientConj (P : (Matrix (Fin N) (Fin N) R)ˣ) :
    @RingHom (Matrix (Fin N) (Fin N) R) (Matrix (Fin N) (Fin N) R)
      (inferInstance : Ring (Matrix (Fin N) (Fin N) R)).toNonAssocSemiring
      (inferInstance : Ring (Matrix (Fin N) (Fin N) R)).toNonAssocSemiring where
  toFun A := P.val*A*P.inv
  map_zero' := by simp
  map_one' := by simp
  map_add' A B := by simp [mul_add,add_mul]
  map_mul' A B := by simp [mul_assoc]
def bigBasisUnits (P : (Matrix (Fin N) (Fin N) R)ˣ) : (Matrix (Fin (n*N)) (Fin (n*N)) R)ˣ :=
  Units.map flattenRing.toMonoidHom (Units.map (scalarRingHom (N:=n)).toMonoidHom P)
lemma scalar_units_conjugates (P : (Matrix (Fin N) (Fin N) R)ˣ)
    (u : (Matrix (Fin n) (Fin n) (Matrix (Fin N) (Fin N) R))ˣ) :
    (Units.map (scalarRingHom (N:=n)).toMonoidHom P)*u*
      (Units.map (scalarRingHom (N:=n)).toMonoidHom P)⁻¹=
      Units.map (coefficientConj P).mapMatrix.toMonoidHom u := by
  apply Units.ext
  apply Matrix.ext
  intro i j
  change ((Matrix.diagonal (fun _ : Fin n=>P.val))*u.val*(Matrix.diagonal (fun _ : Fin n=>P.inv))) i j=
    P.val*(u.val i j)*P.inv
  rw [Matrix.mul_diagonal,Matrix.diagonal_mul]
lemma big_conjugates_elementary (P : (Matrix (Fin N) (Fin N) R)ˣ)
    (p : Root n) (A : Matrix (Fin N) (Fin N) R) :
    bigBasisUnits P*Elementary.representation (blockRoot p A)*(bigBasisUnits P)⁻¹=
      Elementary.representation (blockRoot p (coefficientConj P A)) := by
  have hs := scalar_units_conjugates (n:=n) P (Elementary.e p A)
  have he := congrArg (Units.map (flattenRing (n:=n) (N:=N) (R:=R)).toMonoidHom) hs
  simpa only [map_mul,map_inv,Elementary.map_e,representation_blockRoot,bigBasisUnits] using he

theorem stable_basis_change (hn : 3 ≤ n) (P : (Matrix (Fin N) (Fin N) R)ˣ)
    (b : Steinberg (n*N) R) (hb : Elementary.representation b=bigBasisUnits P)
    (u : Steinberg n (Matrix (Fin N) (Fin N) R)) :
    padSteinberg (b*blockMap u*b⁻¹)=
      padSteinberg (blockMap (Steinberg.map (coefficientConj P) u)) := by
  let f : Steinberg n (Matrix (Fin N) (Fin N) R) →* Steinberg (n*N) R :=
    (MulAut.conj b).toMonoidHom.comp blockMap
  let g : Steinberg n (Matrix (Fin N) (Fin N) R) →* Steinberg (n*N) R :=
    blockMap.comp (Steinberg.map (coefficientConj P))
  have he : Elementary.representation.comp f=Elementary.representation.comp g := by
    apply Steinberg.hom_ext
    intro p A
    change Elementary.representation (b*blockMap (Steinberg.x p A)*b⁻¹)=
      Elementary.representation (blockMap (Steinberg.map (coefficientConj P) (Steinberg.x p A)))
    rw [Steinberg.map_x,blockMap_x,blockMap_x,map_mul,map_mul,map_inv,hb]
    exact big_conjugates_elementary P p A
  have hu := DFunLike.congr_fun (stable_uniqueness hn f g (fun u=>DFunLike.congr_fun he u)) u
  exact hu
end
end Kernel

end

end AllPrimeGroups
