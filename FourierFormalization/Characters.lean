/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import FourierFormalization.BinaryLinear
public import FourierFormalization.WalshApplication
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Tactic.FinCases

/-! Real binary characters and exact finite character cancellation. -/

@[expose] public section

noncomputable section

open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Paper

private theorem binarySign_add (u v : ZMod 2) :
    (if u + v = 0 then (1 : ℝ) else -1) =
      (if u = 0 then (1 : ℝ) else -1) * (if v = 0 then (1 : ℝ) else -1) := by
  fin_cases u <;> fin_cases v <;> simp [ZMod]

def realCharacter {n : ℕ} (a : BinarySpace n) : AddChar (BinarySpace n) ℝ where
  toFun := character a
  map_zero_eq_one' := by simp [character]
  map_add_eq_mul' x y := by
    simpa only [character, map_add] using binarySign_add (dotProduct n a x) (dotProduct n a y)

@[simp] theorem realCharacter_apply {n : ℕ} (a x : BinarySpace n) :
    realCharacter a x = character a x := rfl

theorem character_add {n : ℕ} (a x y : BinarySpace n) :
    character a (x + y) = character a x * character a y :=
  (realCharacter a).map_add_eq_mul x y

theorem character_product {n : ℕ} (a b x : BinarySpace n) :
    character a x * character b x = character (a - b) x := by
  rw [character_symm a x, character_symm b x, character_symm (a - b) x]
  have hneg : -b = b := by
    funext i
    exact CharTwo.neg_eq (b i)
  rw [sub_eq_add_neg, hneg, character_add]

theorem character_eq_one_iff {n : ℕ} (a x : BinarySpace n) :
    character a x = 1 ↔ dotProduct n a x = 0 := by
  unfold character
  split_ifs <;> norm_num [*]

theorem realCharacter_eq_zero_iff {n : ℕ} (a : BinarySpace n) :
    realCharacter a = 0 ↔ a = 0 := by
  rw [AddChar.eq_zero_iff]
  simp only [realCharacter_apply, character_eq_one_iff]
  constructor
  · exact (dotProduct_nondegenerate n).1 a
  · rintro rfl x
    simp

theorem character_sum (n : ℕ) (a : BinarySpace n) :
    (∑ x : BinarySpace n, character a x) = if a = 0 then (2 ^ n : ℝ) else 0 := by
  simpa only [realCharacter_apply, realCharacter_eq_zero_iff, binarySpace_card,
    Nat.cast_pow, Nat.cast_ofNat] using
    (realCharacter a).sum_eq_ite

theorem characterObligations (n : ℕ) : CharacterObligations n :=
  ⟨character_sum n, character_product⟩

def subspaceRealCharacter {n : ℕ} (V : Submodule (ZMod 2) (BinarySpace n))
    (a : BinarySpace n) : AddChar V ℝ :=
  (realCharacter a).compAddMonoidHom V.subtype.toAddMonoidHom

@[simp] theorem subspaceRealCharacter_apply {n : ℕ}
    (V : Submodule (ZMod 2) (BinarySpace n)) (a : BinarySpace n) (x : V) :
    subspaceRealCharacter V a x = character a x := rfl

theorem subspaceRealCharacter_eq_zero_iff {n : ℕ}
    (V : Submodule (ZMod 2) (BinarySpace n)) (a : BinarySpace n) :
    subspaceRealCharacter V a = 0 ↔ a ∈ annihilator V := by
  rw [AddChar.eq_zero_iff, mem_annihilator_iff]
  simp only [subspaceRealCharacter_apply, character_eq_one_iff]
  constructor
  · intro h v hv
    exact h ⟨v, hv⟩
  · intro h v
    exact h v.val v.property

theorem character_sum_subspace {n : ℕ}
    (V : Submodule (ZMod 2) (BinarySpace n)) (a : BinarySpace n) :
    (∑ x : V, character a x) = if a ∈ annihilator V then (Nat.card V : ℝ) else 0 := by
  simpa only [subspaceRealCharacter_apply, subspaceRealCharacter_eq_zero_iff,
    Nat.card_eq_fintype_card] using (subspaceRealCharacter V a).sum_eq_ite

end Paper
