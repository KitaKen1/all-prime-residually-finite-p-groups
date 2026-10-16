import AllPrimeGroups.K1Stability

/-! The Steinberg group is centrally closed in rank at least five (Kervaire, Steinberg; Milnor's
*Introduction to algebraic K-theory*, Theorem 5.10), the first ingredient of manuscript
Section 12.

Let `q : V → St_n(B)` be surjective with central kernel. Commutators of lifts only depend on the
images. Lifts of roots in commuting positions commute exactly: one of them is, up to a central
element, a commutator through a spare coordinate, and the other commutes with both factors up to
central elements. The corrected lifts `[ȳ_ih(a), ȳ_hj(1)]` do not depend on the spare coordinate `h`
(by `CommutatorCalculus.three_factor`) and satisfy the Steinberg relations, so they define a
splitting. Consequently `St_n(B)` lifts to every central extension of a group it maps to, and such
lifts of a perfect group are unique. -/

namespace AllPrimeGroups
namespace Central

open CommutatorCalculus

variable {B : Type*} [Ring B] {n : ℕ}

theorem exists_avoid (S : Finset (Fin n)) (h : S.card < n) : ∃ s, s ∉ S := by
  by_contra hc
  simp only [not_exists, not_not] at hc
  rw [Finset.eq_univ_of_forall hc, Finset.card_univ, Fintype.card_fin] at h
  exact lt_irrefl _ h

theorem exists_ne_four (hn : 5 ≤ n) (a b c d : Fin n) :
    ∃ s : Fin n, s ≠ a ∧ s ≠ b ∧ s ≠ c ∧ s ≠ d := by
  have hcard : ({a, b, c, d} : Finset (Fin n)).card < n := by
    have h1 := Finset.card_insert_le a ({b, c, d} : Finset (Fin n))
    have h2 := Finset.card_insert_le b ({c, d} : Finset (Fin n))
    have h3 := Finset.card_insert_le c ({d} : Finset (Fin n))
    rw [Finset.card_singleton] at h3
    omega
  obtain ⟨s, hs⟩ := exists_avoid _ hcard
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hs
  exact ⟨s, hs.1, hs.2.1, hs.2.2.1, hs.2.2.2⟩

theorem exists_ne_three (hn : 5 ≤ n) (a b c : Fin n) : ∃ s : Fin n, s ≠ a ∧ s ≠ b ∧ s ≠ c := by
  obtain ⟨s, h1, h2, h3, -⟩ := exists_ne_four hn a b c c
  exact ⟨s, h1, h2, h3⟩

/-! ### Commutators in central extensions -/

section Bracket
variable {V : Type*} [Group V]

theorem bracket_mul_center (a b z w : V) (hz : z ∈ Subgroup.center V)
    (hw : w ∈ Subgroup.center V) : bracket (a * z) (b * w) = bracket a b := by
  have hz' : ∀ c : V, bracket z c = 1 := fun c =>
    (bracket_eq_one_iff _ _).mpr (Subgroup.mem_center_iff.mp hz c).symm
  have hw' : ∀ c : V, bracket c w = 1 := fun c =>
    (bracket_eq_one_iff _ _).mpr (Subgroup.mem_center_iff.mp hw c)
  rw [mul_right, hw' (a * z), mul_one, mul_inv_cancel_right, mul_left, hz' b, mul_one,
    mul_inv_cancel, one_mul]

end Bracket

section Lifts
variable {V : Type*} [Group V] (q : V →* Steinberg n B)
  (hq : ∀ z, q z = 1 → z ∈ Subgroup.center V)

include hq in
theorem center_of_eq {a a' : V} (h : q a = q a') : a⁻¹ * a' ∈ Subgroup.center V :=
  hq _ (by rw [map_mul, map_inv, h, inv_mul_cancel])

include hq in
/-- Commutators of lifts only depend on the images. -/
theorem bracket_congr {a a' b b' : V} (ha : q a = q a') (hb : q b = q b') :
    bracket a b = bracket a' b' := by
  have e1 : a' = a * (a⁻¹ * a') := by group
  have e2 : b' = b * (b⁻¹ * b') := by group
  rw [e1, e2, bracket_mul_center _ _ _ _ (center_of_eq q hq ha) (center_of_eq q hq hb)]

include hq in
theorem commute_bracket_of_commute {g u v : V} (hu : Commute (q g) (q u))
    (hv : Commute (q g) (q v)) : Commute g (bracket u v) := by
  have e1 : q (g * u * g⁻¹) = q u := by
    rw [map_mul, map_mul, map_inv, hu.eq, mul_inv_cancel_right]
  have e2 : q (g * v * g⁻¹) = q v := by
    rw [map_mul, map_mul, map_inv, hv.eq, mul_inv_cancel_right]
  have h : g * bracket u v * g⁻¹ = bracket (g * u * g⁻¹) (g * v * g⁻¹) := by
    simp only [bracket]
    group
  rw [bracket_congr q hq e1 e2] at h
  exact mul_inv_eq_iff_eq_mul.mp h

variable (hsurj : Function.Surjective q)

include hq hsurj in
/-- Lifts of roots in commuting positions commute exactly. -/
theorem lift_commute (hn : 5 ≤ n) {p r : Root n} (h₁ : p.col ≠ r.row) (h₂ : p.row ≠ r.col)
    {a b : B} {g w : V} (hg : q g = Steinberg.x p a) (hw : q w = Steinberg.x r b) :
    Commute g w := by
  obtain ⟨s, hs1, hs2, hs3, hs4⟩ := exists_ne_four hn p.row p.col r.row r.col
  obtain ⟨u, hu⟩ := hsurj (Steinberg.x ⟨r.row, s, Ne.symm hs3⟩ b)
  obtain ⟨v, hv⟩ := hsurj (Steinberg.x ⟨s, r.col, hs4⟩ 1)
  have hbr : q (bracket u v) = q w := by
    rw [map_bracket, hu, hv, Steinberg.x_mul _ _ _ (Ne.symm hs3) hs4 r.ne, mul_one, hw]
  have hc : Commute g (bracket u v) := commute_bracket_of_commute q hq
    (by rw [hg, hu]; exact Steinberg.x_commute p ⟨r.row, s, Ne.symm hs3⟩ h₁ (Ne.symm hs1) a b)
    (by rw [hg, hv]; exact Steinberg.x_commute p ⟨s, r.col, hs4⟩ (Ne.symm hs2) h₂ a 1)
  have hz := center_of_eq q hq hbr
  have e : w = bracket u v * ((bracket u v)⁻¹ * w) := by group
  rw [e]
  exact hc.mul_right (Subgroup.mem_center_iff.mp hz g)

/-- A lift of an element of the Steinberg group. -/
noncomputable def lift (x : Steinberg n B) : V := (hsurj x).choose

theorem q_lift (x : Steinberg n B) : q (lift q hsurj x) = x := (hsurj x).choose_spec

/-- A spare coordinate for a root. -/
noncomputable def spare (hn : 5 ≤ n) (p : Root n) : Fin n :=
  (exists_ne_three hn p.row p.col p.row).choose

theorem spare_ne_row (hn : 5 ≤ n) (p : Root n) : spare hn p ≠ p.row :=
  (exists_ne_three hn p.row p.col p.row).choose_spec.1

theorem spare_ne_col (hn : 5 ≤ n) (p : Root n) : spare hn p ≠ p.col :=
  (exists_ne_three hn p.row p.col p.row).choose_spec.2.1

/-- The corrected lift of a root. -/
noncomputable def yhat (hn : 5 ≤ n) (p : Root n) (a : B) : V :=
  bracket (lift q hsurj (Steinberg.x ⟨p.row, spare hn p, Ne.symm (spare_ne_row hn p)⟩ a))
    (lift q hsurj (Steinberg.x ⟨spare hn p, p.col, spare_ne_col hn p⟩ 1))

theorem q_yhat (hn : 5 ≤ n) (p : Root n) (a : B) : q (yhat q hsurj hn p a) = Steinberg.x p a := by
  rw [yhat, map_bracket, q_lift, q_lift, Steinberg.x_mul _ _ _ _ _ p.ne, mul_one]

include hq in
/-- The corrected lift does not depend on the spare coordinate or the lifts. -/
theorem bracket_eq_yhat (hn : 5 ≤ n) {i h j : Fin n} (hih : i ≠ h) (hhj : h ≠ j) (hij : i ≠ j)
    {a : B} {u v : V} (hu : q u = Steinberg.x ⟨i, h, hih⟩ a)
    (hv : q v = Steinberg.x ⟨h, j, hhj⟩ 1) : bracket u v = yhat q hsurj hn ⟨i, j, hij⟩ a := by
  set h' := spare hn ⟨i, j, hij⟩ with hh'
  have hh'i : h' ≠ i := spare_ne_row hn ⟨i, j, hij⟩
  have hh'j : h' ≠ j := spare_ne_col hn ⟨i, j, hij⟩
  by_cases hhh : h = h'
  · subst hhh
    exact bracket_congr q hq (hu.trans (q_lift q hsurj _).symm) (hv.trans (q_lift q hsurj _).symm)
  · set X := lift q hsurj (Steinberg.x ⟨i, h', Ne.symm hh'i⟩ a) with hX
    set Y := lift q hsurj (Steinberg.x ⟨h', h, Ne.symm hhh⟩ (1 : B)) with hY
    have qX : q X = Steinberg.x ⟨i, h', Ne.symm hh'i⟩ a := q_lift q hsurj _
    have qY : q Y = Steinberg.x ⟨h', h, Ne.symm hhh⟩ 1 := q_lift q hsurj _
    have qXY : q (bracket X Y) = Steinberg.x ⟨i, h, hih⟩ a := by
      rw [map_bracket, qX, qY, Steinberg.x_mul _ _ _ _ _ hih, mul_one]
    have qYZ : q (bracket Y v) = Steinberg.x ⟨h', j, hh'j⟩ 1 := by
      rw [map_bracket, qY, hv, Steinberg.x_mul _ _ _ _ _ hh'j, mul_one]
    have hAX : Commute (bracket X Y) X :=
      lift_commute q hq hsurj hn (p := ⟨i, h, hih⟩) (r := ⟨i, h', Ne.symm hh'i⟩) (Ne.symm hih)
        (Ne.symm hh'i).symm.symm qXY qX
    have hAY : Commute (bracket X Y) Y :=
      lift_commute q hq hsurj hn (p := ⟨i, h, hih⟩) (r := ⟨h', h, Ne.symm hhh⟩) hhh hih qXY qY
    have hBY : Commute (bracket Y v) Y :=
      lift_commute q hq hsurj hn (p := ⟨h', j, hh'j⟩) (r := ⟨h', h, Ne.symm hhh⟩) (Ne.symm hh'j)
        (Ne.symm hhh) qYZ qY
    have hBZ : Commute (bracket Y v) v :=
      lift_commute q hq hsurj hn (p := ⟨h', j, hh'j⟩) (r := ⟨h, j, hhj⟩) (Ne.symm hhj) hh'j qYZ hv
    have hAB : Commute (bracket X Y) (bracket Y v) :=
      lift_commute q hq hsurj hn (p := ⟨i, h, hih⟩) (r := ⟨h', j, hh'j⟩) hhh hij qXY qYZ
    have hXZ : Commute X v :=
      lift_commute q hq hsurj hn (p := ⟨i, h', Ne.symm hh'i⟩) (r := ⟨h, j, hhj⟩) (Ne.symm hhh) hij
        qX hv
    have h1 : bracket u v = bracket (bracket X Y) v :=
      bracket_congr q hq (hu.trans qXY.symm) rfl
    rw [h1, (three_factor X Y v hAX hAY hBY hBZ hAB hXZ).1]
    exact bracket_congr q hq rfl (qYZ.trans (q_lift q hsurj _).symm)

include hq in
theorem yhat_add (hn : 5 ≤ n) (p : Root n) (a b : B) :
    yhat q hsurj hn p (a + b) = yhat q hsurj hn p a * yhat q hsurj hn p b := by
  set h := spare hn p
  have hhi : h ≠ p.row := spare_ne_row hn p
  have hhj : h ≠ p.col := spare_ne_col hn p
  set U := lift q hsurj (Steinberg.x ⟨p.row, h, Ne.symm hhi⟩ a)
  set U' := lift q hsurj (Steinberg.x ⟨p.row, h, Ne.symm hhi⟩ b)
  set Z := lift q hsurj (Steinberg.x ⟨h, p.col, hhj⟩ (1 : B))
  have qU : q U = Steinberg.x ⟨p.row, h, Ne.symm hhi⟩ a := q_lift q hsurj _
  have qU' : q U' = Steinberg.x ⟨p.row, h, Ne.symm hhi⟩ b := q_lift q hsurj _
  have qZ : q Z = Steinberg.x ⟨h, p.col, hhj⟩ 1 := q_lift q hsurj _
  have e1 : yhat q hsurj hn p (a + b) = bracket (U * U') Z := by
    unfold yhat
    exact bracket_congr q hq (by rw [q_lift, map_mul, qU, qU', Steinberg.x_add]) rfl
  have e2 : yhat q hsurj hn p a = bracket U Z := rfl
  have e3 : yhat q hsurj hn p b = bracket U' Z := rfl
  have qW : q (bracket U' Z) = Steinberg.x p b := by
    rw [← e3, q_yhat]
  have hc : Commute U (bracket U' Z) :=
    lift_commute q hq hsurj hn (p := ⟨p.row, h, Ne.symm hhi⟩) (r := p) hhi.symm.symm.symm.symm
      p.ne qU qW
  have hW : Commute (bracket U' Z) (bracket U Z) :=
    lift_commute q hq hsurj hn (p := p) (r := p) (Ne.symm p.ne) p.ne qW (by rw [← e2, q_yhat])
  rw [e1, mul_left, conj_of_commute hc, e2, e3]
  exact hW.eq

include hq in
theorem yhat_commute (hn : 5 ≤ n) (p r : Root n) (h₁ : p.col ≠ r.row) (h₂ : p.row ≠ r.col)
    (a b : B) : Commute (yhat q hsurj hn p a) (yhat q hsurj hn r b) :=
  lift_commute q hq hsurj hn h₁ h₂ (q_yhat q hsurj hn p a) (q_yhat q hsurj hn r b)

include hq in
theorem yhat_mul (hn : 5 ≤ n) (i j k : Fin n) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a b : B) :
    bracket (yhat q hsurj hn ⟨i, j, hij⟩ a) (yhat q hsurj hn ⟨j, k, hjk⟩ b) =
      yhat q hsurj hn ⟨i, k, hik⟩ (a * b) := by
  obtain ⟨h, hhi, hhj, hhk⟩ := exists_ne_three hn i j k
  set X := yhat q hsurj hn ⟨i, j, hij⟩ a
  set Y := lift q hsurj (Steinberg.x ⟨j, h, Ne.symm hhj⟩ b)
  set Z := lift q hsurj (Steinberg.x ⟨h, k, hhk⟩ (1 : B))
  have qX : q X = Steinberg.x ⟨i, j, hij⟩ a := q_yhat q hsurj hn _ a
  have qY : q Y = Steinberg.x ⟨j, h, Ne.symm hhj⟩ b := q_lift q hsurj _
  have qZ : q Z = Steinberg.x ⟨h, k, hhk⟩ 1 := q_lift q hsurj _
  have qXY : q (bracket X Y) = Steinberg.x ⟨i, h, Ne.symm hhi⟩ (a * b) := by
    rw [map_bracket, qX, qY, Steinberg.x_mul]
  have qYZ : q (bracket Y Z) = Steinberg.x ⟨j, k, hjk⟩ b := by
    rw [map_bracket, qY, qZ, Steinberg.x_mul _ _ _ _ _ hjk, mul_one]
  have hAX : Commute (bracket X Y) X :=
    lift_commute q hq hsurj hn (p := ⟨i, h, Ne.symm hhi⟩) (r := ⟨i, j, hij⟩) hhi hij qXY qX
  have hAY : Commute (bracket X Y) Y :=
    lift_commute q hq hsurj hn (p := ⟨i, h, Ne.symm hhi⟩) (r := ⟨j, h, Ne.symm hhj⟩) hhj
      (Ne.symm hhi) qXY qY
  have hBY : Commute (bracket Y Z) Y :=
    lift_commute q hq hsurj hn (p := ⟨j, k, hjk⟩) (r := ⟨j, h, Ne.symm hhj⟩) (Ne.symm hjk)
      (Ne.symm hhj) qYZ qY
  have hBZ : Commute (bracket Y Z) Z :=
    lift_commute q hq hsurj hn (p := ⟨j, k, hjk⟩) (r := ⟨h, k, hhk⟩) (Ne.symm hhk) hjk qYZ qZ
  have hAB : Commute (bracket X Y) (bracket Y Z) :=
    lift_commute q hq hsurj hn (p := ⟨i, h, Ne.symm hhi⟩) (r := ⟨j, k, hjk⟩) hhj hik qXY qYZ
  have hXZ : Commute X Z :=
    lift_commute q hq hsurj hn (p := ⟨i, j, hij⟩) (r := ⟨h, k, hhk⟩) (Ne.symm hhj) hik qX qZ
  have h1 : bracket X (yhat q hsurj hn ⟨j, k, hjk⟩ b) = bracket X (bracket Y Z) :=
    bracket_congr q hq rfl ((q_yhat q hsurj hn _ b).trans qYZ.symm)
  rw [h1, ← (three_factor X Y Z hAX hAY hBY hBZ hAB hXZ).1]
  exact bracket_eq_yhat q hq hsurj hn (Ne.symm hhi) hhk hik qXY qZ

include hq hsurj in
/-- Manuscript Section 12 (Kervaire, Steinberg): in rank at least five the Steinberg group is
centrally closed. -/
theorem exists_splitting (hn : 5 ≤ n) :
    ∃ s : Steinberg n B →* V, q.comp s = MonoidHom.id (Steinberg n B) := by
  refine ⟨Steinberg.lift (yhat q hsurj hn) (yhat_add q hq hsurj hn)
    (fun p r h₁ h₂ a b => yhat_commute q hq hsurj hn p r h₁ h₂ a b)
    (fun i j k hij hjk hik a b => yhat_mul q hq hsurj hn i j k hij hjk hik a b), ?_⟩
  apply Steinberg.hom_ext
  intro p a
  rw [MonoidHom.comp_apply, Steinberg.lift_x, q_yhat, MonoidHom.id_apply]

end Lifts

/-! ### Universality -/

/-- The Steinberg group lifts to every central extension of a group it maps to. -/
theorem exists_lift (hn : 5 ≤ n) {H V : Type*} [Group H] [Group V] (f : Steinberg n B →* H)
    (p : V →* H) (hrange : f.range ≤ p.range) (hker : ∀ v, p v = 1 → v ∈ Subgroup.center V) :
    ∃ φ : Steinberg n B →* V, p.comp φ = f := by
  let W : Subgroup (V × Steinberg n B) :=
    { carrier := {x | p x.1 = f x.2}
      mul_mem' := fun {x y} hx hy => by
        show p (x.1 * y.1) = f (x.2 * y.2)
        rw [map_mul, map_mul, hx, hy]
      one_mem' := by
        show p 1 = f 1
        rw [map_one, map_one]
      inv_mem' := fun {x} hx => by
        show p x.1⁻¹ = f x.2⁻¹
        rw [map_inv, map_inv, hx] }
  let q : W →* Steinberg n B := (MonoidHom.snd V (Steinberg n B)).comp W.subtype
  have hsurj : Function.Surjective q := by
    intro z
    obtain ⟨v, hv⟩ := hrange ⟨z, rfl⟩
    exact ⟨⟨(v, z), hv⟩, rfl⟩
  have hq : ∀ w, q w = 1 → w ∈ Subgroup.center W := by
    rintro ⟨⟨v, z⟩, hw⟩ hz
    change z = 1 at hz
    subst hz
    have hv : p v = 1 := by
      have : p v = f 1 := hw
      rw [this, map_one]
    rw [Subgroup.mem_center_iff]
    rintro ⟨⟨v', z'⟩, hw'⟩
    apply Subtype.ext
    show (v' * v, z' * 1) = (v * v', 1 * z')
    rw [(Subgroup.mem_center_iff.mp (hker v hv) v'), mul_one, one_mul]
  obtain ⟨s, hs⟩ := exists_splitting q hq hsurj hn
  refine ⟨(MonoidHom.fst V (Steinberg n B)).comp (W.subtype.comp s), ?_⟩
  apply Steinberg.hom_ext
  intro r a
  have h1 : ((s (Steinberg.x r a) : W) : V × Steinberg n B).2 = Steinberg.x r a :=
    DFunLike.congr_fun hs (Steinberg.x r a)
  have h2 := (s (Steinberg.x r a)).2
  simp only [MonoidHom.comp_apply, MonoidHom.coe_fst, Subgroup.coe_subtype]
  rw [show p ((s (Steinberg.x r a) : W) : V × Steinberg n B).1 =
    f ((s (Steinberg.x r a) : W) : V × Steinberg n B).2 from h2, h1]

/-- Lifts of a perfect group to a central extension are unique. -/
theorem lift_unique {G H V : Type*} [Group G] [Group H] [Group V] [Group.IsPerfect G]
    (p : V →* H) (hker : ∀ v, p v = 1 → v ∈ Subgroup.center V) {φ ψ : G →* V}
    (h : p.comp φ = p.comp ψ) : φ = ψ := by
  have hc : ∀ g, ψ g * (φ g)⁻¹ ∈ Subgroup.center V := fun g =>
    hker _ (by rw [map_mul, map_inv, ← MonoidHom.comp_apply, ← h, MonoidHom.comp_apply,
      mul_inv_cancel])
  let χ : G →* Subgroup.center V :=
    { toFun := fun g => ⟨ψ g * (φ g)⁻¹, hc g⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun g g' => by
        apply Subtype.ext
        show ψ (g * g') * (φ (g * g'))⁻¹ = ψ g * (φ g)⁻¹ * (ψ g' * (φ g')⁻¹)
        have hz := Subgroup.mem_center_iff.mp (hc g') (φ g)⁻¹
        rw [map_mul, map_mul, mul_inv_rev]
        calc ψ g * ψ g' * ((φ g')⁻¹ * (φ g)⁻¹) = ψ g * (ψ g' * (φ g')⁻¹ * (φ g)⁻¹) := by group
          _ = ψ g * ((φ g)⁻¹ * (ψ g' * (φ g')⁻¹)) := by rw [← hz]
          _ = ψ g * (φ g)⁻¹ * (ψ g' * (φ g')⁻¹) := by group }
  have hχ : χ = 1 := by
    have hker : commutator G ≤ χ.ker := by
      rw [commutator_def, Subgroup.commutator_le]
      intro g₁ _ g₂ _
      rw [MonoidHom.mem_ker, map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr
        (Subtype.ext (Subgroup.mem_center_iff.mp (χ g₂).2 (χ g₁)))
    ext g
    have hg : g ∈ χ.ker := hker (by rw [Group.IsPerfect.commutator_eq_top]; trivial)
    rw [MonoidHom.mem_ker] at hg
    rw [hg]
    rfl
  ext g
  have h1 := congrArg Subtype.val (DFunLike.congr_fun hχ g)
  change ψ g * (φ g)⁻¹ = 1 at h1
  exact (mul_inv_eq_one.mp h1).symm

end Central
end AllPrimeGroups
