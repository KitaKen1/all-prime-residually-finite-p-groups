import Mathlib.Algebra.Colimit.DirectLimit

/-! Natural-number chains of groups, with explicit finite-stage equality criteria. -/
namespace AllPrimeGroups.Chain

variable {C : ℕ → Type*} [∀ n, Group (C n)]

/-- Compose the successive structure homomorphisms from stage n through stage m. -/
def connect (step : ∀ n, C n →* C (n + 1)) (n m : ℕ) (h : n ≤ m) : C n →* C m :=
  Nat.leRecOn h (@fun k f => (step k).comp f) (MonoidHom.id _)

@[simp] theorem connect_apply (step : ∀ n, C n →* C (n + 1)) (n m : ℕ) (h : n ≤ m) :
    (connect step n m h : C n → C m) = Nat.leRecOn h (@fun k => step k) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  funext x
  induction k with
  | zero => simp [connect, Nat.leRecOn_self]
  | succ k ih =>
    rw [Nat.leRecOn_succ (Nat.le_add_right n k), connect, Nat.leRecOn_succ (Nat.le_add_right n k),
      ← connect, MonoidHom.comp_apply, ih]

instance directedSystem (step : ∀ n, C n →* C (n + 1)) :
    DirectedSystem C (fun i j h => connect step i j h) :=
  ⟨fun _ _ => congr (congr rfl (Nat.leRecOn_self _)) rfl,
    fun _ _ _ hij hjk => by simp [Nat.leRecOn_trans hij hjk]⟩

abbrev Limit (step : ∀ n, C n →* C (n + 1)) := DirectLimit C (connect step)

/-- The canonical group homomorphism from a finite stage to the direct limit. -/
def of (step : ∀ n, C n →* C (n + 1)) (n : ℕ) : C n →* Limit step where
  toFun g := Quotient.mk _ ⟨n, g⟩
  map_one' := (DirectLimit.one_def (f := connect step) n).symm
  map_mul' g h := (DirectLimit.mul_def (f := connect step) n g h).symm

@[simp] theorem of_connect (step : ∀ n, C n →* C (n + 1))
    (n m : ℕ) (h : n ≤ m) (g : C n) : of step m (connect step n m h g) = of step n g :=
  DirectLimit.mk_apply (F := C) (f := connect step) n m g h

/-- This criterion does not assume the transition homomorphisms are injective. -/
theorem of_eq_one_iff (step : ∀ n, C n →* C (n + 1)) (n : ℕ) (g : C n) :
    of step n g = 1 ↔ ∃ m, ∃ h : n ≤ m, connect step n m h g = 1 :=
  DirectLimit.exists_eq_one (f := connect step) ⟨n, g⟩

theorem of_eq_iff (step : ∀ n, C n →* C (n + 1))
    (n m : ℕ) (g : C n) (h : C m) :
    of step n g = of step m h ↔
      ∃ k, ∃ hn : n ≤ k, ∃ hm : m ≤ k, connect step n k hn g = connect step m k hm h :=
  Quotient.eq


theorem connect_succ (step : ∀ n, C n →* C (n + 1))
    (n m : ℕ) (h : n ≤ m) (h' : n ≤ m + 1) :
    connect step n (m + 1) h' = (step m).comp (connect step n m h) := by
  unfold connect
  exact Nat.leRecOn_succ (C := fun j => C n →* C j) h (MonoidHom.id _)

@[simp] theorem connect_successor (step : ∀ n, C n →* C (n + 1))
    (n : ℕ) (h : n ≤ n + 1) : connect step n (n + 1) h = step n := by
  ext g
  simp [connect_apply, Nat.leRecOn_succ']

@[simp] theorem of_step (step : ∀ n, C n →* C (n + 1)) (n : ℕ) (g : C n) :
    of step (n + 1) (step n g) = of step n g := by
  simpa only [connect_successor] using of_connect step n (n + 1) (Nat.le_succ n) g

theorem exists_stage (step : ∀ n, C n →* C (n + 1)) (g : Limit step) :
    ∃ n, ∃ x : C n, g = of step n x :=
  DirectLimit.exists_eq_mk (connect step) g

theorem connect_injective (step : ∀ n, C n →* C (n + 1))
    (hinj : ∀ n, Function.Injective (step n)) (n m : ℕ) (h : n ≤ m) :
    Function.Injective (connect step n m h) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  induction k with
  | zero => simpa [connect, Nat.leRecOn_self] using (Function.injective_id : Function.Injective (id : C n → C n))
  | succ k ih =>
    simp only [Nat.add_succ] at h ⊢
    rw [connect_succ step n (n + k) (Nat.le_add_right n k)]
    exact (hinj (n + k)).comp (ih (Nat.le_add_right n k))

/-- Used for the matrix chain. No injectivity is assumed for the Steinberg chain. -/
theorem of_injective (step : ∀ n, C n →* C (n + 1))
    (hinj : ∀ n, Function.Injective (step n)) (n : ℕ) : Function.Injective (of step n) :=
  DirectLimit.mk_injective (connect step) (connect_injective step hinj) n

variable {G : Type*} [Group G]

theorem compatible (step : ∀ n, C n →* C (n + 1)) (q : ∀ n, C n →* G)
    (hq : ∀ n, (q (n + 1)).comp (step n) = q n)
    (n m : ℕ) (h : n ≤ m) (g : C n) : q n g = q m (connect step n m h g) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  induction k with
  | zero => simp [connect, Nat.leRecOn_self]
  | succ k ih =>
    simp only [Nat.add_succ] at h ⊢
    rw [connect_succ step n (n + k) (Nat.le_add_right n k), MonoidHom.comp_apply]
    rw [show q (n + k + 1) (step (n + k) (connect step n (n + k) _ g)) =
      q (n + k) (connect step n (n + k) _ g) from DFunLike.congr_fun (hq (n + k)) _]
    exact ih (Nat.le_add_right n k)

/-- The universal group homomorphism, constructed from compatible stage homomorphisms. -/
def lift (step : ∀ n, C n →* C (n + 1)) (q : ∀ n, C n →* G)
    (hq : ∀ n, (q (n + 1)).comp (step n) = q n) : Limit step →* G where
  toFun := DirectLimit.lift (F := C) (f := connect step) (fun n => q n) (compatible step q hq)
  map_one' := DirectLimit.lift_one (f := connect step) q (compatible step q hq)
  map_mul' g h := DirectLimit.lift_mul (f := connect step) q (compatible step q hq) g h

@[simp] theorem lift_of (step : ∀ n, C n →* C (n + 1)) (q : ∀ n, C n →* G)
    (hq : ∀ n, (q (n + 1)).comp (step n) = q n) (n : ℕ) (g : C n) :
    lift step q hq (of step n g) = q n g := rfl

end AllPrimeGroups.Chain
