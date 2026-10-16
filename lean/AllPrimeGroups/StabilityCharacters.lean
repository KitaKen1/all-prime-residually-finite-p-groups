import AllPrimeGroups.RowStabilizer
import Mathlib.Algebra.Module.CharacterModule

/-! Character detection for the remaining stability argument.

The coefficient group is the rational circle `ℚ/ℤ`, rather than rational characters, so it
detects torsion. Mathlib supplies separation by characters and the centrally closed Steinberg
group supplies the lift. The only hypothesis left in this reduction is the extension of the
central characters; constructing those extensions is the frame/cochain argument, not claimed
here.

The character-separation proof follows the evaluation argument in
TauCeti/Algebra/Module/CharacterModule.lean (Apache-2.0), using the pinned Mathlib API. -/

universe u

open scoped IsMulCommutative

namespace AllPrimeGroups
namespace Central

variable {B : Type u} [Ring B] {n : ℕ}

/-- Every map from a perfect group into a Steinberg group has the same lift as a compatible
map into a central extension. In particular, the latter map kills its kernel. -/
theorem compatible_lift_kills_kernel {G H V : Type*} [Group G] [Group H] [Group V]
    [Group.IsPerfect G] (hn : 5 ≤ n) (f : G →* Steinberg n B) (q : Steinberg n B →* H)
    (p : V →* H) (hrange : q.range ≤ p.range)
    (hker : ∀ v, p v = 1 → v ∈ Subgroup.center V) (ψ : G →* V)
    (hψ : p.comp ψ = q.comp f) {x : G} (hx : f x = 1) : ψ x = 1 := by
  obtain ⟨φ, hφ⟩ := exists_lift hn q p hrange hker
  have h : p.comp (φ.comp f) = p.comp ψ := by
    apply MonoidHom.ext
    intro g
    exact (DFunLike.congr_fun hφ (f g)).trans (DFunLike.congr_fun hψ g).symm
  have heq : φ.comp f = ψ := lift_unique p hker h
  rw [← heq, MonoidHom.comp_apply, hx, map_one]

/-- The extension property needed from the frame argument. Each rational-circle character
of the centre is realized on the base kernel by a map to a central extension of the ambient
matrix group. This is an explicit proof obligation, not an instance. -/
def CharacterExtensions {G H : Type u} [Group G] [Group H]
    (f : G →* Steinberg n B) (q : Steinberg n B →* H) : Prop :=
  ∀ χ : CharacterModule (Additive (Subgroup.center G)),
    ∃ (V : Type u) (_ : Group V) (p : V →* H)
      (i : Multiplicative (AddCircle (1 : ℚ)) →* V) (ψ : G →* V),
      Function.Injective i ∧ q.range ≤ p.range ∧
      (∀ v, p v = 1 → v ∈ Subgroup.center V) ∧ p.comp ψ = q.comp f ∧
      ∀ z : Subgroup.center G, q (f z) = 1 → ψ z = i (Multiplicative.ofAdd (χ (Additive.ofMul z)))

/-- Rational-circle characters and uniqueness of perfect lifts detect every element killed
by the rank-changing map. -/
theorem injective_of_character_extensions {G H : Type u} [Group G] [Group H]
    [Group.IsPerfect G] (hn : 5 ≤ n) (f : G →* Steinberg n B) (q : Steinberg n B →* H)
    (hcentral : ∀ x, f x = 1 → x ∈ Subgroup.center G)
    (hext : CharacterExtensions f q) : Function.Injective f := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  let z : Subgroup.center G := ⟨x, hcentral x hx⟩
  have hz : (Additive.ofMul z : Additive (Subgroup.center G)) = 0 := by
    apply CharacterModule.eq_zero_of_character_apply
    intro χ
    obtain ⟨V, hV, p, i, ψ, hi, hrange, hker, hψ, hχ⟩ := hext χ
    have hxψ : ψ x = 1 := compatible_lift_kills_kernel hn f q p hrange hker ψ hψ hx
    have hzq : q (f z) = 1 := by change q (f x) = 1; rw [hx, map_one]
    have hv : i (Multiplicative.ofAdd (χ (Additive.ofMul z))) = i 1 := by
      rw [← hχ z hzq, map_one]
      exact hxψ
    exact congrArg Multiplicative.toAdd (hi hv)
  have hz' : z = 1 := congrArg Additive.toMul hz
  have hx' : x = 1 := congrArg Subtype.val hz'
  rw [hx']
  exact Subgroup.one_mem _

end Central

namespace FrameStabilizer

variable {B : Type u} [Ring B] {m : ℕ}
variable {K : Type*} [Field K] (ε : B →+* K) (hunit : ∀ b : B, ε b ≠ 0 → IsUnit b)

include hunit in
/-- A precise reduction of one-column cover injectivity to the character-extension step. -/
theorem toSteinberg_injective_of_characters (hm : 6 ≤ m)
    (hext : Central.CharacterExtensions (toSteinberg (m := m) (B := B)) Elementary.representation) :
    Function.Injective (toSteinberg (m := m) (B := B)) := by
  have := isPerfect (B := B) (show 3 ≤ m by omega)
  apply Central.injective_of_character_extensions (by omega) toSteinberg Elementary.representation
    _ hext
  intro x hx
  apply kernel_central ε hunit hm
  have h := congrArg Elementary.representation hx
  rw [map_one, ← MonoidHom.comp_apply, representation_toSteinberg] at h
  exact h

include hunit in
theorem pad_injective_of_characters (hm : 6 ≤ m)
    (hext : Central.CharacterExtensions (toSteinberg (m := m) (B := B)) Elementary.representation) :
    Function.Injective (Kernel.padSteinberg (n := m) (R := B)) := by
  intro x y hxy
  apply SemidirectProduct.inr_injective (φ := stRowAct)
  apply toSteinberg_injective_of_characters ε hunit hm hext
  simpa only [toSteinberg_inr] using hxy

end FrameStabilizer
end AllPrimeGroups
