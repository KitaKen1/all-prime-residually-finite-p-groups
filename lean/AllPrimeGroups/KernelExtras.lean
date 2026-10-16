/-
Naturality of the elementary representation and of coefficient maps, adapted from OpenAI
PeriodicGroups/Steinberg/KernelRelations.lean (commit pinned in upstream/provenance.json;
Apache-2.0, see upstream/OpenAI-LICENSE). These statements hold over every unital ring.
-/
import AllPrimeGroups.Stabilization

namespace AllPrimeGroups

namespace Kernel
noncomputable section
variable {n : ℕ} {R : Type*} [Ring R]

lemma padUnitsHom_injective : Function.Injective (padUnitsHom (n:=n) (R:=R)) := by
  intro u v huv
  apply Units.ext
  have he := congrArg Units.val huv
  change (Matrix.reindexRingEquiv R (coordinateEquiv n)) (Matrix.fromBlocks u.val 0 0 1)=
    (Matrix.reindexRingEquiv R (coordinateEquiv n)) (Matrix.fromBlocks v.val 0 0 1) at he
  have hb := (Matrix.reindexRingEquiv R (coordinateEquiv n)).injective he
  apply Matrix.ext
  intro i j
  exact congrArg (fun M : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) R=>M (Sum.inl i) (Sum.inl j)) hb

lemma pad_kernel_iff (g : Steinberg n R) :
    Elementary.representation (padSteinberg g)=1 ↔ Elementary.representation g=1 := by
  have he := DFunLike.congr_fun (pad_representation (n:=n) (R:=R)) g
  change Elementary.representation (padSteinberg g)=padUnitsHom (Elementary.representation g) at he
  rw [he]
  exact (map_eq_one_iff _ padUnitsHom_injective)

end
end Kernel

namespace Elementary
variable {n : ℕ} {R S : Type*} [Ring R] [Ring S]

lemma map_e (f : R →+* S) (p : Root n) (a : R) :
    Units.map f.mapMatrix.toMonoidHom (e p a)=e p (f a) := by
  apply Units.ext
  change f.mapMatrix (1+Matrix.single p.row p.col a)=1+Matrix.single p.row p.col (f a)
  rw [map_add,map_one]
  congr 1
  exact Matrix.map_single p.row p.col a f

lemma representation_map (f : R →+* S) :
    representation.comp (Steinberg.map (n:=n) f)=
      (Units.map f.mapMatrix.toMonoidHom).comp representation := by
  apply Steinberg.hom_ext
  intro p a
  simp only [MonoidHom.comp_apply,Steinberg.map_x,representation_x,map_e]

lemma map_kernel (f : R →+* S) (g : Steinberg n R) (hg : representation g=1) :
    representation (Steinberg.map f g)=1 := by
  have he := DFunLike.congr_fun (representation_map (n:=n) f) g
  simpa only [MonoidHom.comp_apply,hg,map_one] using he

end Elementary

namespace Steinberg
variable {n : ℕ} {R S T : Type*} [Ring R] [Ring S] [Ring T]

lemma map_comp (g : S →+* T) (f : R →+* S) :
    (map (n:=n) g).comp (map f)=map (g.comp f) := by
  apply hom_ext
  intro p a
  simp [map_x]

lemma map_map (g : S →+* T) (f : R →+* S) (x : Steinberg n R) :
    map g (map f x)=map (g.comp f) x := DFunLike.congr_fun (map_comp g f) x

lemma map_identity : map (n:=n) (RingHom.id R)=MonoidHom.id _ := by
  apply hom_ext
  intro p a
  simp [map_x]

end Steinberg
end AllPrimeGroups
