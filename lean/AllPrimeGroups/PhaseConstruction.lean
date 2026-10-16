import OAI.GroupTheory.PeriodicGroups.Algebra.HierarchyGrowth

/-! Phases of long nonzero words, one level at a time (manuscript Lemma 19.1, abstract step).

At each level of a hierarchy, a letter predicate defines cuts, and upstream's `Cuts.parse`
splits a word into a prefix without cuts and the intervals starting at the cuts. Suppose that
every long surviving word has at least two intervals, a bounded prefix and a bounded last
interval, that every other interval t comes with an upper word `up t` with `|t| = L |up t|`, and
that the concatenation `U(w)` of these upper words survives at the next level.

Given phases at the next level modulo Q' with the prefix and suffix properties, the phase

  `σ(w) = L σ'(U(w)) - |prefix of w|`   modulo `L Q'`

again has the prefix and suffix properties. This is the inductive step of manuscript Lemma 19.1;
it uses no choice of representatives at the upper level. -/

namespace AllPrimeGroups
namespace Phases
open OAI.SourceBurnside
open Classical

noncomputable section

variable {L : Type*}

theorem parse_eq_of (cut : L → Prop) {p : List L} {ts : List (List L)}
    (hp : Cuts.NoCut cut p) (ht : ∀ t ∈ ts, Cuts.Interval cut t) :
    Cuts.parse cut (p ++ ts.flatten) = (p, ts) := by
  rw [Cuts.parse_noCut_append cut p _ hp, Cuts.parse_intervals_flatten cut ts ht]
  simp

theorem interval_append (cut : L → Prop) {l p : List L} (hl : Cuts.Interval cut l)
    (hp : Cuts.NoCut cut p) : Cuts.Interval cut (l ++ p) := by
  obtain ⟨a, t, rfl, ha, ht⟩ := hl
  refine ⟨a, t ++ p, rfl, ha, ?_⟩
  intro b hb
  rcases List.mem_append.mp hb with hb | hb
  · exact ht b hb
  · exact hp b hb

theorem noCut_append (cut : L → Prop) {x p : List L} (hx : Cuts.NoCut cut x)
    (hp : Cuts.NoCut cut p) : Cuts.NoCut cut (x ++ p) := by
  intro b hb
  rcases List.mem_append.mp hb with hb | hb
  · exact hx b hb
  · exact hp b hb

/-- Phases at one level modulo Q, with the prefix and suffix properties for long surviving
words. -/
structure LevelPhases (surv : List L → Prop) (Q : ℕ) where
  thr : ℕ
  σ : List L → ZMod Q
  suffix : ∀ x z, surv (x ++ z) → thr ≤ z.length → σ (x ++ z) + (x.length : ZMod Q) = σ z
  pref : ∀ v y, surv (v ++ y) → thr ≤ v.length → σ (v ++ y) = σ v

/-- The phases at the top of a finite hierarchy, modulo one. -/
def trivialPhases (surv : List L → Prop) : LevelPhases surv 1 where
  thr := 0
  σ _ := 0
  suffix _ _ _ _ := Subsingleton.elim _ _
  pref _ _ _ _ := rfl

/-- The data relating one level of a hierarchy to the next. -/
structure TokenData {L' : Type*} (surv : List L → Prop) (surv' : List L' → Prop) where
  cut : L → Prop
  B : ℕ
  Lb : ℕ
  Lb_pos : 0 < Lb
  thrTok : ℕ
  up : List L → List L'
  surv_left : ∀ x z, surv (x ++ z) → surv z
  surv_right : ∀ v y, surv (v ++ y) → surv v
  parse_bound : ∀ w, surv w → thrTok < w.length → (Cuts.parse cut w).1.length ≤ B ∧
    ∃ (ts : List (List L)) (s : List L), (Cuts.parse cut w).2 = ts ++ [s] ∧ ts ≠ [] ∧
      s.length ≤ B
  token_length : ∀ w, surv w → thrTok < w.length →
    ∀ t ∈ (Cuts.parse cut w).2.dropLast, t.length = Lb * (up t).length
  up_surv : ∀ w, surv w → thrTok < w.length →
    surv' (((Cuts.parse cut w).2.dropLast.map up).flatten)

namespace TokenData
variable {L' : Type*} {surv : List L → Prop} {surv' : List L' → Prop}
variable (T : TokenData surv surv')

/-- The upper word of a word: the concatenation of the upper words of its complete intervals. -/
def U (w : List L) : List L' := ((Cuts.parse T.cut w).2.dropLast.map T.up).flatten

theorem length_flatten_eq (ts : List (List L))
    (htl : ∀ t ∈ ts, t.length = T.Lb * (T.up t).length) :
    ts.flatten.length = T.Lb * (ts.map T.up).flatten.length := by
  induction ts with
  | nil => simp
  | cons t ts ih =>
    rw [List.flatten_cons, List.length_append, List.map_cons, List.flatten_cons,
      List.length_append, ih (fun s hs => htl s (List.mem_cons.mpr (Or.inr hs))),
      htl t (List.mem_cons.mpr (Or.inl rfl)), mul_add]

/-- A long surviving word has a long upper word. -/
theorem U_long (w : List L) (hw : surv w) (hl : T.thrTok < w.length) {n : ℕ}
    (hn : 2 * T.B + T.Lb * n ≤ w.length) : n ≤ (T.U w).length := by
  obtain ⟨hp, ts, s, hts, _, hs⟩ := T.parse_bound w hw hl
  have hjoin := Cuts.parse_join T.cut w
  have hlen := T.length_flatten_eq (Cuts.parse T.cut w).2.dropLast (T.token_length w hw hl)
  rw [hts, List.dropLast_concat] at hlen
  have hw' : w.length = (Cuts.parse T.cut w).1.length + ts.flatten.length + s.length := by
    conv_lhs => rw [← hjoin]
    rw [hts, List.flatten_append, List.length_append, List.length_append, List.flatten_singleton]
    omega
  have hU : (T.U w).length = (ts.map T.up).flatten.length := by
    rw [U, hts, List.dropLast_concat]
  rw [hU]
  have hpos := T.Lb_pos
  by_contra hc
  have hc' : (ts.map T.up).flatten.length < n := Nat.lt_of_not_le hc
  have : T.Lb * (ts.map T.up).flatten.length < T.Lb * n := Nat.mul_lt_mul_of_pos_left hc' hpos
  omega

end TokenData

/-- The multiplication by L from residues modulo Q to residues modulo L Q. -/
def scale (Lb Q : ℕ) : ZMod Q →+ ZMod (Lb * Q) :=
  ZMod.lift Q ⟨(Int.castAddHom (ZMod (Lb * Q))).comp (AddMonoidHom.mulLeft (Lb : ℤ)), by
    change (((Lb : ℤ) * Q : ℤ) : ZMod (Lb * Q)) = 0
    push_cast
    exact_mod_cast ZMod.natCast_self (Lb * Q)⟩

theorem scale_natCast (Lb Q n : ℕ) : scale Lb Q (n : ZMod Q) = ((Lb * n : ℕ) : ZMod (Lb * Q)) := by
  have h : ((n : ℤ) : ZMod Q) = (n : ZMod Q) := Int.cast_natCast n
  rw [← h, scale, ZMod.lift_coe]
  simp

theorem scale_add_natCast (Lb Q : ℕ) (a : ZMod Q) (n : ℕ) :
    scale Lb Q (a + n) = scale Lb Q a + ((Lb * n : ℕ) : ZMod (Lb * Q)) := by
  rw [map_add, scale_natCast]

namespace TokenData
variable {L' : Type*} {surv : List L → Prop} {surv' : List L' → Prop}
variable (T : TokenData surv surv')

/-- The phases of the lower level. -/
def phase {Q' : ℕ} (P' : LevelPhases surv' Q') (w : List L) : ZMod (T.Lb * Q') :=
  scale T.Lb Q' (P'.σ (T.U w)) - ((Cuts.parse T.cut w).1.length : ZMod (T.Lb * Q'))

/-- The threshold of the lower level. -/
def thr {Q' : ℕ} (P' : LevelPhases surv' Q') : ℕ := T.thrTok + 1 + 2 * T.B + T.Lb * P'.thr

theorem suffix {Q' : ℕ} (P' : LevelPhases surv' Q') (x z : List L) (hxz : surv (x ++ z))
    (hz : T.thr P' ≤ z.length) :
    T.phase P' (x ++ z) + (x.length : ZMod (T.Lb * Q')) = T.phase P' z := by
  have hsz := T.surv_left x z hxz
  have hzl : T.thrTok < z.length := by unfold thr at hz; omega
  have hxzl : T.thrTok < (x ++ z).length := by rw [List.length_append]; omega
  obtain ⟨_, tz, sz, hz2, _, _⟩ := T.parse_bound z hsz hzl
  have hjz := Cuts.parse_join T.cut z
  have hpz := Cuts.parse_prefix T.cut z
  have hiz := Cuts.parse_intervals T.cut z
  rw [hz2] at hjz hiz
  set pz := (Cuts.parse T.cut z).1 with hpzdef
  have hjx := Cuts.parse_join T.cut x
  have hpx := Cuts.parse_prefix T.cut x
  have hix := Cuts.parse_intervals T.cut x
  set px := (Cuts.parse T.cut x).1 with hpxdef
  have hUz : T.U z = (tz.map T.up).flatten := by rw [U, hz2, List.dropLast_concat]
  have hUlong : P'.thr ≤ (T.U z).length := T.U_long z hsz hzl (by unfold thr at hz; omega)
  rcases List.eq_nil_or_concat' (Cuts.parse T.cut x).2 with hx0 | ⟨ps, l, hx1⟩
  · -- no cut in x
    rw [hx0, List.flatten_nil, List.append_nil] at hjx
    have hxz' : x ++ z = (x ++ pz) ++ (tz ++ [sz]).flatten := by
      rw [List.append_assoc, hjz]
    have hparse : Cuts.parse T.cut (x ++ z) = (x ++ pz, tz ++ [sz]) := by
      rw [hxz']
      exact parse_eq_of T.cut (noCut_append T.cut (hjx ▸ hpx) hpz) hiz
    have hU : T.U (x ++ z) = T.U z := by rw [U, U, hparse, hz2]
    simp only [phase, hU, hparse, List.length_append, Nat.cast_add]
    ring
  · -- x has a cut
    rw [hx1] at hjx hix
    have hl : Cuts.Interval T.cut l := hix l (List.mem_append.mpr (Or.inr (List.mem_singleton_self l)))
    have hps : ∀ t ∈ ps, Cuts.Interval T.cut t := fun t ht => hix t (List.mem_append.mpr (Or.inl ht))
    have hxz' : x ++ z = px ++ (ps ++ [l ++ pz] ++ tz ++ [sz]).flatten := by
      rw [← hjx, ← hjz]
      simp only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil,
        List.append_assoc]
    have hint : ∀ t ∈ ps ++ [l ++ pz] ++ tz ++ [sz], Cuts.Interval T.cut t := by
      intro t ht
      simp only [List.mem_append, List.mem_singleton] at ht
      rcases ht with ((ht | rfl) | ht) | rfl
      · exact hps t ht
      · exact interval_append T.cut hl hpz
      · exact hiz t (List.mem_append.mpr (Or.inl ht))
      · exact hiz _ (List.mem_append.mpr (Or.inr (List.mem_singleton_self _)))
    have hparse : Cuts.parse T.cut (x ++ z) = (px, ps ++ [l ++ pz] ++ tz ++ [sz]) := by
      rw [hxz']
      exact parse_eq_of T.cut hpx hint
    have hdrop : (Cuts.parse T.cut (x ++ z)).2.dropLast = ps ++ [l ++ pz] ++ tz := by
      rw [hparse, List.dropLast_concat]
    have hU : T.U (x ++ z) = ((ps ++ [l ++ pz]).map T.up).flatten ++ T.U z := by
      show ((Cuts.parse T.cut (x ++ z)).2.dropLast.map T.up).flatten = _
      rw [hdrop, hUz, List.map_append, List.flatten_append]
    have htl := T.token_length (x ++ z) hxz hxzl
    rw [hdrop] at htl
    have hlen : (ps ++ [l ++ pz]).flatten.length =
        T.Lb * ((ps ++ [l ++ pz]).map T.up).flatten.length :=
      T.length_flatten_eq _ (fun t ht => htl t (List.mem_append.mpr (Or.inl ht)))
    have hsuf := P'.suffix (((ps ++ [l ++ pz]).map T.up).flatten) (T.U z)
      (hU ▸ T.up_surv (x ++ z) hxz hxzl) hUlong
    have hxlen : x.length + pz.length = px.length + (ps ++ [l ++ pz]).flatten.length := by
      rw [← hjx]
      simp only [List.length_append, List.flatten_append, List.flatten_cons, List.flatten_nil,
        List.append_nil]
      omega
    simp only [phase, hparse]
    rw [← hsuf, hU, scale_add_natCast]
    rw [hlen] at hxlen
    have hcast : ((x.length : ℕ) : ZMod (T.Lb * Q')) + (pz.length : ZMod (T.Lb * Q')) =
        (px.length : ZMod (T.Lb * Q')) +
          ((T.Lb * ((ps ++ [l ++ pz]).map T.up).flatten.length : ℕ) : ZMod (T.Lb * Q')) := by
      exact_mod_cast congrArg (fun n : ℕ => (n : ZMod (T.Lb * Q'))) hxlen
    linear_combination hcast

theorem pref {Q' : ℕ} (P' : LevelPhases surv' Q') (v y : List L) (hvy : surv (v ++ y))
    (hv : T.thr P' ≤ v.length) : T.phase P' (v ++ y) = T.phase P' v := by
  have hsv := T.surv_right v y hvy
  have hvl : T.thrTok < v.length := by unfold thr at hv; omega
  have hvyl : T.thrTok < (v ++ y).length := by rw [List.length_append]; omega
  obtain ⟨_, tv, sv, hv2, _, _⟩ := T.parse_bound v hsv hvl
  have hjv := Cuts.parse_join T.cut v
  have hpv := Cuts.parse_prefix T.cut v
  have hiv := Cuts.parse_intervals T.cut v
  rw [hv2] at hjv hiv
  set pv := (Cuts.parse T.cut v).1 with hpvdef
  have hjy := Cuts.parse_join T.cut y
  have hpy := Cuts.parse_prefix T.cut y
  have hiy := Cuts.parse_intervals T.cut y
  set py := (Cuts.parse T.cut y).1 with hpydef
  set qy := (Cuts.parse T.cut y).2 with hqydef
  have hsv' : Cuts.Interval T.cut sv := hiv sv (List.mem_append.mpr (Or.inr (List.mem_singleton_self sv)))
  have hvy' : v ++ y = pv ++ (tv ++ [sv ++ py] ++ qy).flatten := by
    rw [← hjv, ← hjy]
    simp only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil,
      List.append_assoc]
  have hint : ∀ t ∈ tv ++ [sv ++ py] ++ qy, Cuts.Interval T.cut t := by
    intro t ht
    simp only [List.mem_append, List.mem_singleton] at ht
    rcases ht with (ht | rfl) | ht
    · exact hiv t (List.mem_append.mpr (Or.inl ht))
    · exact interval_append T.cut hsv' hpy
    · exact hiy t ht
  have hparse : Cuts.parse T.cut (v ++ y) = (pv, tv ++ [sv ++ py] ++ qy) := by
    rw [hvy']
    exact parse_eq_of T.cut hpv hint
  have hUv : T.U v = (tv.map T.up).flatten := by rw [U, hv2, List.dropLast_concat]
  rcases List.eq_nil_or_concat' qy with hq0 | ⟨qs, q, hq1⟩
  · have hU : T.U (v ++ y) = T.U v := by
      show ((Cuts.parse T.cut (v ++ y)).2.dropLast.map T.up).flatten = _
      rw [hparse, hq0, List.append_nil, List.dropLast_concat, hUv]
    simp only [phase, hU, hparse, hpvdef]
  · have hd : (Cuts.parse T.cut (v ++ y)).2.dropLast = tv ++ ((sv ++ py) :: qs) := by
      rw [hparse, hq1]
      have h : tv ++ [sv ++ py] ++ (qs ++ [q]) = (tv ++ ((sv ++ py) :: qs)) ++ [q] := by simp
      rw [h]
      exact List.dropLast_concat
    have hU : T.U (v ++ y) = T.U v ++ ((((sv ++ py) :: qs).map T.up).flatten) := by
      show ((Cuts.parse T.cut (v ++ y)).2.dropLast.map T.up).flatten = _
      rw [hd, List.map_append, List.flatten_append, hUv]
    have hUlong : P'.thr ≤ (T.U v).length := T.U_long v hsv hvl (by unfold thr at hv; omega)
    have hpre := P'.pref (T.U v) ((((sv ++ py) :: qs).map T.up).flatten)
      (hU ▸ T.up_surv (v ++ y) hvy hvyl) hUlong
    simp only [phase, hparse]
    rw [hU, hpre, ← hpvdef]

/-- The inductive step of manuscript Lemma 19.1. -/
def step {Q' : ℕ} (P' : LevelPhases surv' Q') : LevelPhases surv (T.Lb * Q') where
  thr := T.thr P'
  σ := T.phase P'
  suffix := T.suffix P'
  pref := T.pref P'

end TokenData

end

end Phases
end AllPrimeGroups
