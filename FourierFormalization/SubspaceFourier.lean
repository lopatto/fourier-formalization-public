/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import FourierFormalization.Characters

/-! Exact Euclidean support/energy and Walsh identities for normalized binary
subspace indicators. All identities are pointwise on the finite ambient space. -/

@[expose] public section

noncomputable section

open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Paper

theorem walsh_column_orthogonality (n : ℕ) (a b : BinarySpace n) :
    (∑ x : BinarySpace n,
      ((Real.sqrt (2 ^ n : ℝ))⁻¹ * character x a) *
        ((Real.sqrt (2 ^ n : ℝ))⁻¹ * character x b)) = if a = b then 1 else 0 :=
  walsh_column_orthogonality_of_obligations n (characterObligations n) a b

theorem walsh_row_orthogonality (n : ℕ) (a b : BinarySpace n) :
    (∑ x : BinarySpace n,
      ((Real.sqrt (2 ^ n : ℝ))⁻¹ * character a x) *
        ((Real.sqrt (2 ^ n : ℝ))⁻¹ * character b x)) = if a = b then 1 else 0 := by
  simpa only [character_symm a, character_symm b] using walsh_column_orthogonality n a b

theorem walsh_involution {n : ℕ} (f : Signal n) : walsh (walsh f) = f := by
  have hwalsh (g : Signal n) (a : BinarySpace n) :
      walsh g a = ∑ x, ((Real.sqrt (2 ^ n : ℝ))⁻¹ * character a x) * g x := by
    rw [walsh, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  have horth (a y : BinarySpace n) :
      (∑ x, ((Real.sqrt (2 ^ n : ℝ))⁻¹ * character a x) *
        ((Real.sqrt (2 ^ n : ℝ))⁻¹ * character x y)) = if a = y then 1 else 0 := by
    simpa only [character_symm a] using walsh_column_orthogonality n a y
  have hinner (a y : BinarySpace n) :
      (∑ x, ((Real.sqrt (2 ^ n : ℝ))⁻¹ * character a x) *
        (((Real.sqrt (2 ^ n : ℝ))⁻¹ * character x y) * f y)) =
        (if a = y then 1 else 0) * f y := by
    calc
      _ = (∑ x, ((Real.sqrt (2 ^ n : ℝ))⁻¹ * character a x) *
          ((Real.sqrt (2 ^ n : ℝ))⁻¹ * character x y)) * f y := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl (fun _ _ => (mul_assoc _ _ _).symm)
      _ = _ := by rw [horth]
  funext a
  simp_rw [hwalsh, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [hinner]
  simp

theorem normalizedIndicator_ne_zero_value_iff {n : ℕ}
    (V : Submodule (ZMod 2) (BinarySpace n)) (x : BinarySpace n) :
    normalizedIndicator V x ≠ 0 ↔ x ∈ V := by
  have hsqrt : Real.sqrt (Nat.card V : ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (subspace_card_real_pos V))
  constructor
  · intro h
    by_contra hx
    exact h (by simp [normalizedIndicator, hx])
  · intro hx
    rw [normalizedIndicator, ite_eq_left hx]
    exact inv_ne_zero hsqrt

theorem normalizedIndicator_eq_zero_iff {n : ℕ}
    (V : Submodule (ZMod 2) (BinarySpace n)) (x : BinarySpace n) :
    normalizedIndicator V x = 0 ↔ x ∉ V := by
  simpa only [not_not] using not_congr (normalizedIndicator_ne_zero_value_iff V x)

theorem normalizedIndicator_nonzero {n : ℕ}
    (V : Submodule (ZMod 2) (BinarySpace n)) : normalizedIndicator V ≠ 0 := by
  intro h
  exact ((normalizedIndicator_ne_zero_value_iff V 0).mpr V.zero_mem) (congrFun h 0)

theorem mem_support_normalizedIndicator {n : ℕ}
    (V : Submodule (ZMod 2) (BinarySpace n)) (x : BinarySpace n) :
    x ∈ signalSupport (normalizedIndicator V) ↔ x ∈ V := by
  rw [mem_signalSupport_iff, normalizedIndicator_ne_zero_value_iff]

theorem normalizedIndicator_support_card {n : ℕ}
    (V : Submodule (ZMod 2) (BinarySpace n)) :
    (signalSupport (normalizedIndicator V)).card = Nat.card V := by
  rw [Nat.card_eq_fintype_card]
  exact (Fintype.card_of_subtype (signalSupport (normalizedIndicator V))
    (mem_support_normalizedIndicator V)).symm

theorem normalizedIndicator_support_card_eq_pow {n : ℕ}
    (V : Submodule (ZMod 2) (BinarySpace n)) :
    (signalSupport (normalizedIndicator V)).card = 2 ^ Module.finrank (ZMod 2) V := by
  rw [normalizedIndicator_support_card, subspace_card]

theorem normalizedIndicator_sparse {n k : ℕ} (V : Grass n k) :
    Sparse (2 ^ k) (normalizedIndicator V.val) := by
  rw [Sparse, normalizedIndicator_support_card_eq_pow, V.property]

theorem normalizedIndicator_energy {n : ℕ}
    (V : Submodule (ZMod 2) (BinarySpace n)) : squaredEnergy (normalizedIndicator V) = 1 := by
  have hcard : (Finset.univ.filter (fun x : BinarySpace n => x ∈ V)).card = Nat.card V := by
    rw [Nat.card_eq_fintype_card]
    exact (Fintype.card_of_subtype _ (by simp)).symm
  simp only [squaredEnergy, normalizedIndicator, ite_pow, zero_pow (by decide : 2 ≠ 0)]
  rw [← Finset.sum_filter, Finset.sum_const, hcard, nsmul_eq_mul, inv_pow,
    Real.sq_sqrt (subspace_card_real_pos V).le]
  exact mul_inv_cancel₀ (ne_of_gt (subspace_card_real_pos V))

private theorem normalizedIndicator_coefficient {n : ℕ}
    (V : Submodule (ZMod 2) (BinarySpace n)) :
    (Real.sqrt (2 ^ n : ℝ))⁻¹ * ((Real.sqrt (Nat.card V : ℝ))⁻¹ * (Nat.card V : ℝ)) =
      (Real.sqrt (Nat.card (annihilator V) : ℝ))⁻¹ := by
  rw [← subspace_card_real_mul_annihilator_card V,
    Real.sqrt_mul (subspace_card_real_pos V).le]
  rw [mul_inv_rev]
  calc
    _ = (Real.sqrt (Nat.card (annihilator V) : ℝ))⁻¹ *
        (((Real.sqrt (Nat.card V : ℝ)) ^ 2)⁻¹ * (Nat.card V : ℝ)) := by ring
    _ = _ := by
      rw [Real.sq_sqrt (subspace_card_real_pos V).le,
        inv_mul_cancel₀ (ne_of_gt (subspace_card_real_pos V)), mul_one]

theorem normalizedIndicator_walsh_apply {n : ℕ}
    (V : Submodule (ZMod 2) (BinarySpace n)) (a : BinarySpace n) :
    walsh (normalizedIndicator V) a = normalizedIndicator (annihilator V) a := by
  have hsum : (∑ x : BinarySpace n, normalizedIndicator V x * character a x) =
      (Real.sqrt (Nat.card V : ℝ))⁻¹ * ∑ x : V, character a x := by
    simp only [normalizedIndicator, ite_mul, zero_mul]
    rw [← Finset.sum_filter, ← Finset.mul_sum]
    congr 1
    exact Finset.sum_subtype _ (by simp) (character a)
  rw [walsh, hsum, character_sum_subspace]
  by_cases ha : a ∈ annihilator V
  · simp only [ha, ↓reduceIte, normalizedIndicator]
    exact normalizedIndicator_coefficient V
  · simp [normalizedIndicator, ha]

theorem normalizedIndicator_walsh {n : ℕ}
    (V : Submodule (ZMod 2) (BinarySpace n)) :
    walsh (normalizedIndicator V) = normalizedIndicator (annihilator V) := by
  funext a
  exact normalizedIndicator_walsh_apply V a

theorem normalizedIndicator_kernel_iff {n : ℕ}
    (V : Submodule (ZMod 2) (BinarySpace n)) (Q : RowSet n) :
    KernelOn Q (normalizedIndicator V) ↔ Misses Q V := by
  simp only [KernelOn, Misses, normalizedIndicator_walsh, normalizedIndicator_eq_zero_iff]

theorem normalizedIndicator_kernel_of_misses {n : ℕ}
    (V : Submodule (ZMod 2) (BinarySpace n)) (Q : RowSet n) (h : Misses Q V) :
    KernelOn Q (normalizedIndicator V) := (normalizedIndicator_kernel_iff V Q).mpr h

theorem missedSubspace_implies_sparseKernel {n k : ℕ} (Q : RowSet n) :
    MissedSubspace n k Q → SparseKernel (2 ^ k) Q := by
  rintro ⟨V, hV⟩
  exact ⟨normalizedIndicator V.val, normalizedIndicator_nonzero V.val,
    normalizedIndicator_sparse V, normalizedIndicator_kernel_of_misses V.val Q hV⟩

end Paper
