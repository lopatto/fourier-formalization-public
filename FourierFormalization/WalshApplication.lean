/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import FourierFormalization.DefinitionLemmas
public import FourierFormalization.Reduction

/-!
The normalized Walsh matrix as a bounded orthonormal example, derived from
character identities and the necessary-sampling reduction.
-/

@[expose] public section

noncomputable section

open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Paper

theorem c₀_positive : 0 < c₀ := by
  exact div_pos (Real.log_pos (by norm_num : (1 : ℝ) < 2)) (by norm_num)
/-- Ambient binary-character cancellation and multiplication identities. -/
structure CharacterObligations (n : ℕ) : Prop where
  cancellation : ∀ a : BinarySpace n,
    (∑ x : BinarySpace n, character a x) = if a = 0 then (2 ^ n : ℝ) else 0
  product : ∀ a b x : BinarySpace n,
    character a x * character b x = character (a - b) x

theorem character_symm {n : ℕ} (a x : BinarySpace n) : character a x = character x a := by
  unfold character
  rw [dotProduct_symm n a x]

theorem walsh_entry_abs_bound (n : ℕ) (x a : BinarySpace n) :
    |(Real.sqrt (2 ^ n : ℝ))⁻¹ * character x a| ≤ (Real.sqrt (2 ^ n : ℝ))⁻¹ := by
  unfold character
  split <;> simp [abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]

theorem walsh_column_orthogonality_of_obligations (n : ℕ) (h : CharacterObligations n)
    (a b : BinarySpace n) :
    (∑ x : BinarySpace n,
      ((Real.sqrt (2 ^ n : ℝ))⁻¹ * character x a) *
        ((Real.sqrt (2 ^ n : ℝ))⁻¹ * character x b)) = if a = b then 1 else 0 := by
  have hterm : ∀ x : BinarySpace n,
      ((Real.sqrt (2 ^ n : ℝ))⁻¹ * character x a) *
          ((Real.sqrt (2 ^ n : ℝ))⁻¹ * character x b) =
        (Real.sqrt (2 ^ n : ℝ))⁻¹ ^ 2 * character (a - b) x := by
    intro x
    rw [character_symm x a, character_symm x b, ← h.product a b x]
    ring
  simp_rw [hterm]
  rw [← Finset.mul_sum, h.cancellation]
  by_cases hab : a = b
  · subst b
    simp only [sub_self, ↓reduceIte]
    rw [inv_pow, Real.sq_sqrt (by positivity : 0 ≤ (2 ^ n : ℝ))]
    exact inv_mul_cancel₀ (by positivity : (2 ^ n : ℝ) ≠ 0)
  · have hsub : a - b ≠ 0 := sub_ne_zero.mpr hab
    simp [hab, hsub]

/-- Column orthogonality and necessary sampling for the Walsh family from
character identities and finite kernel estimates. -/
theorem bounded_orthonormal_example_of_obligations
    (hc : ∀ n : ℕ, CharacterObligations n) (hk : KernelObligationFamily)
    (hi : SamplingIdentities) :
    (∀ (n : ℕ) (a b : BinarySpace n),
      (∑ x : BinarySpace n,
        ((Real.sqrt (2 ^ n : ℝ))⁻¹ * character x a) *
          ((Real.sqrt (2 ^ n : ℝ))⁻¹ * character x b)) = if a = b then 1 else 0) ∧
    (∀ (n : ℕ) (x a : BinarySpace n),
      |(Real.sqrt (2 ^ n : ℝ))⁻¹ * character x a| ≤ (Real.sqrt (2 ^ n : ℝ))⁻¹) ∧
    (∀ (n k : ℕ → ℕ) (ρ : ℕ → ℝ) (δ : ℝ), 0 < δ → δ < 1 →
      (∀ N : ℕ, ∃ J : ℕ, ∀ j ≥ J, N ≤ n j) →
      (∃ J : ℕ, ∀ j ≥ J,
        dimensionsAdmissible (n j) (k j) ∧ 0 ≤ ρ j ∧ ρ j ≤ 1) →
      (∃ η : ℝ, 0 < η ∧
        ((∃ J : ℕ, ∀ j ≥ J, η ≤ probability (ρ j) (Recovery (n := n j) (2 ^ k j))) ∨
         (∃ J : ℕ, ∀ j ≥ J, η ≤ probability (ρ j) (RIP (n := n j) (2 ^ k j) δ)))) →
      ∃ J : ℕ, ∀ j ≥ J, recoveryThreshold (n j) (k j) < expectedRows (n j) (ρ j)) := by
  exact ⟨fun n => walsh_column_orthogonality_of_obligations n (hc n),
    walsh_entry_abs_bound, necessary_sampling_of_obligations hk hi⟩

end Paper
