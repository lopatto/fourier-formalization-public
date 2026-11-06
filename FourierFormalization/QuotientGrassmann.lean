/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import FourierFormalization.BinaryLinear
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Dimension.Free

/-! Dimension and exact cardinality transport for binary quotient subspaces.
These helpers include zero-dimensional quotients and impose no bound on the
dimension of the quotient Grassmannian being counted. -/

@[expose] public section

noncomputable section

namespace Paper

theorem quotient_image_finrank_add {n : ℕ}
    (S A : Submodule (ZMod 2) (BinarySpace n)) (hSA : S ≤ A) :
    Module.finrank (ZMod 2) (A.map S.mkQ) + Module.finrank (ZMod 2) S =
      Module.finrank (ZMod 2) A := by
  have hker : LinearMap.ker (S.mkQ.domRestrict A) = S.comap A.subtype := by
    ext x
    simp
  have h := LinearMap.finrank_range_add_finrank_ker (S.mkQ.domRestrict A)
  rw [LinearMap.range_domRestrict, hker,
    (Submodule.comapSubtypeEquivOfLe hSA).finrank_eq] at h
  exact h

theorem quotient_image_finrank {n : ℕ}
    (S A : Submodule (ZMod 2) (BinarySpace n)) (hSA : S ≤ A) :
    Module.finrank (ZMod 2) (A.map S.mkQ) =
      Module.finrank (ZMod 2) A - Module.finrank (ZMod 2) S := by
  exact Nat.eq_sub_of_add_eq (quotient_image_finrank_add S A hSA)

theorem quotient_finrank {n : ℕ} (S : Submodule (ZMod 2) (BinarySpace n)) :
    Module.finrank (ZMod 2) (BinarySpace n ⧸ S) = n - Module.finrank (ZMod 2) S := by
  rw [Submodule.finrank_quotient]
  simp only [BinarySpace, Module.finrank_fin_fun]

def quotientCoordinateEquiv {n d : ℕ} (S : Grass n d) :
    (BinarySpace n ⧸ S.val) ≃ₗ[ZMod 2] BinarySpace (n - d) :=
  LinearEquiv.ofFinrankEq _ _ (by
    rw [quotient_finrank, S.property]
    simp only [BinarySpace, Module.finrank_fin_fun])

theorem quotientGrass_card {n d : ℕ} (S : Grass n d) (r : ℕ) :
    Nat.card {W : Submodule (ZMod 2) (BinarySpace n ⧸ S.val) //
      Module.finrank (ZMod 2) W = r} = Nat.card (Grass (n - d) r) := by
  let e := quotientCoordinateEquiv S
  let E := Submodule.orderIsoMapComap e
  apply Nat.card_congr
  refine E.toEquiv.subtypeEquiv ?_
  intro W
  change Module.finrank (ZMod 2) W = r ↔
    Module.finrank (ZMod 2) (W.map e.toLinearMap) = r
  rw [e.finrank_map_eq]

end Paper
