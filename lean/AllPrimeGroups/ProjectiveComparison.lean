/-
Adapted from TauCetiProject/TauCeti at 4f1a681d10b8371c56bc49158b0481d18bd949f5.
Source: TauCeti/Algebra/Homology/Ext/ProjectiveResolution.lean; SHA-256: 65e4e7d08b0183508f80fc72285b7f7ba0106f7fc91a778490204f076c0006ba.
Retrieved 2026-10-15. Imports, visibility and namespace adapted to pinned Mathlib;
only the comparison and explicit Shapiro results needed here are retained.
-/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
import Mathlib.CategoryTheory.Abelian.Ext
import Mathlib.CategoryTheory.Abelian.Projective.Ext
import AllPrimeGroups.HomologyUnop

/-! Compatibility of the projective-resolution computation of Ext with a comparison map. -/

namespace CategoryTheory.ProjectiveResolution

open CategoryTheory.Abelian

section Comparison

variable {R : Type*} [Ring R] {D : Type*} [Category* D] [Abelian D] [Linear R D]
  [EnoughProjectives D]

/-- **`Ext` computed from two resolutions related by a chain map.** If `φ : P ⟶ Q` is a chain map
between projective resolutions of `X` lying over the identity of `X`, then computing `Extⁿ(X, Y)`
from `Q` and precomposing with `φ` gives the computation from `P`. -/
theorem isoExt_hom_comp_homologyMap {X : D} (P Q : ProjectiveResolution X)
    (φ : P.complex ⟶ Q.complex) (comm : φ.f 0 ≫ Q.π.f 0 = P.π.f 0) (n : ℕ) (Y : D) :
    (Q.isoExt n Y).hom ≫ HomologicalComplex.homologyMap
      ((HomologicalComplex.unopFunctor _ _).map
        ((((linearYoneda R D).obj Y).rightOp.mapHomologicalComplex _).map φ).op) n =
      (P.isoExt n Y).hom := by
  have h := isoLeftDerivedObj_hom_naturality (𝟙 X) P Q φ
    (comm.trans (Category.comp_id _).symm) ((linearYoneda R D).obj Y).rightOp n
  rw [CategoryTheory.Functor.map_id, Category.id_comp] at h
  have hP := congrArg Quiver.Hom.unop ((Iso.comp_inv_eq _).2 ((Iso.eq_inv_comp _).2 h.symm))
  have hn := AllPrimeGroups.HomologicalComplex.homologyUnop_inv_naturality
    ((((linearYoneda R D).obj Y).rightOp.mapHomologicalComplex _).map φ) n
  -- `isoExt` is by definition the inverse of `isoLeftDerivedObj`, unopposed, followed by the
  -- inverse of `homologyUnop`; its two constituents are what the two naturality squares govern.
  have e : (Q.isoExt n Y).hom =
      (Q.isoLeftDerivedObj ((linearYoneda R D).obj Y).rightOp n).inv.unop ≫
        (HomologicalComplex.homologyUnop _ n).inv := rfl
  rw [e]
  exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hn.symm).trans
    ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) hP)))

end Comparison

end CategoryTheory.ProjectiveResolution
