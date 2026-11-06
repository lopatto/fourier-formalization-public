/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import FourierFormalization.DefinitionLemmas

/-! Binary linear-algebra facts for the reviewed coordinate pairing. -/

@[expose] public section

noncomputable section

namespace Paper

theorem dotProduct_nondegenerate (n : ℕ) : (dotProduct n).Nondegenerate := by
  apply LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero.mpr
  simp

theorem dotProduct_isRefl (n : ℕ) : (dotProduct n).IsRefl := by
  apply LinearMap.BilinForm.IsSymm.isRefl
  exact Matrix.isSymm_toBilin'_iff_isSymm.mpr Matrix.isSymm_one

theorem annihilator_finrank {n : ℕ} (V : Submodule (ZMod 2) (BinarySpace n)) :
    Module.finrank (ZMod 2) (annihilator V) = n - Module.finrank (ZMod 2) V := by
  rw [annihilator, LinearMap.BilinForm.finrank_orthogonal (dotProduct_nondegenerate n)]
  simp only [BinarySpace, Module.finrank_fin_fun]

theorem annihilator_annihilator {n : ℕ} (V : Submodule (ZMod 2) (BinarySpace n)) :
    annihilator (annihilator V) = V := by
  exact LinearMap.BilinForm.orthogonal_orthogonal
    (dotProduct_nondegenerate n) (dotProduct_isRefl n) V

theorem subspace_card {n : ℕ} (V : Submodule (ZMod 2) (BinarySpace n)) :
    Nat.card V = 2 ^ Module.finrank (ZMod 2) V := by
  let : Fintype V := Fintype.ofFinite V
  rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]

theorem binarySpace_card (n : ℕ) : Fintype.card (BinarySpace n) = 2 ^ n := by
  simp [BinarySpace]

theorem subspace_card_pos {n : ℕ} (V : Submodule (ZMod 2) (BinarySpace n)) :
    0 < Nat.card V := by
  rw [subspace_card]
  exact Nat.pow_pos (by decide)

theorem subspace_finrank_le {n : ℕ} (V : Submodule (ZMod 2) (BinarySpace n)) :
    Module.finrank (ZMod 2) V ≤ n := by
  simpa only [BinarySpace, Module.finrank_fin_fun] using Submodule.finrank_le V

theorem subspace_card_mul_annihilator_card {n : ℕ}
    (V : Submodule (ZMod 2) (BinarySpace n)) :
    Nat.card V * Nat.card (annihilator V) = 2 ^ n := by
  rw [subspace_card, subspace_card, annihilator_finrank, ← pow_add,
    Nat.add_sub_of_le (subspace_finrank_le V)]

theorem annihilator_card {n : ℕ} (V : Submodule (ZMod 2) (BinarySpace n)) :
    Nat.card (annihilator V) = 2 ^ (n - Module.finrank (ZMod 2) V) := by
  rw [subspace_card, annihilator_finrank]

theorem subspace_card_real_pos {n : ℕ} (V : Submodule (ZMod 2) (BinarySpace n)) :
    (0 : ℝ) < Nat.card V := by
  exact_mod_cast subspace_card_pos V

theorem subspace_card_real_mul_annihilator_card {n : ℕ}
    (V : Submodule (ZMod 2) (BinarySpace n)) :
    (Nat.card V : ℝ) * (Nat.card (annihilator V) : ℝ) = (2 ^ n : ℝ) := by
  exact_mod_cast subspace_card_mul_annihilator_card V

end Paper
