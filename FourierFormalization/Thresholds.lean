/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import FourierFormalization.Reduction

/-! Exact base-two logarithmic conversions for the paper's sampling thresholds. -/

@[expose] public section

noncomputable section

namespace Paper

theorem log₂_two_pow (k : ℕ) : log₂ (2 ^ k : ℝ) = (k : ℝ) := by
  have hlog : Real.log (2 : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  unfold log₂
  rw [Real.log_pow, mul_div_cancel_right₀ _ hlog]

theorem log₂_two_pow_div (n k : ℕ) (hk : k ≤ n) :
    log₂ ((2 ^ n : ℝ) / (2 ^ k : ℝ)) = ((n - k : ℕ) : ℝ) := by
  have hlog : Real.log (2 : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  unfold log₂
  rw [Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_pow,
    sub_div, mul_div_cancel_right₀ _ hlog, mul_div_cancel_right₀ _ hlog]
  exact (Nat.cast_sub hk).symm

theorem logarithmic_threshold (n k : ℕ) (hk : k ≤ n) :
    c₀ * (2 ^ k : ℝ) / (2 ^ n : ℝ) * log₂ (2 ^ k : ℝ) *
      log₂ ((2 ^ n : ℝ) / (2 ^ k : ℝ)) = samplingThreshold n k := by
  rw [log₂_two_pow, log₂_two_pow_div n k hk]
  rfl

theorem recovery_threshold (n k : ℕ) (hk : k ≤ n) :
    recoveryThreshold n k = (2 ^ n : ℝ) * samplingThreshold n k := by
  unfold recoveryThreshold samplingThreshold
  rw [log₂_two_pow, log₂_two_pow_div n k hk]
  field_simp

end Paper
