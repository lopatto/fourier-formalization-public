/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import FourierFormalization.Thresholds

/-! Explicit elementary consequences of the reviewed finite parameter range. -/

@[expose] public section
noncomputable section

namespace Paper

theorem log_two_positive : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)

theorem log_two_lt_one : Real.log (2 : ℝ) < 1 := by
  linarith [Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    (by norm_num : (2 : ℝ) ≠ 1)]

theorem log₂_mono {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) : log₂ x ≤ log₂ y := by
  exact div_le_div_of_nonneg_right (Real.log_le_log hx hxy) log_two_positive.le

theorem log₂_mul_log_two (x : ℝ) : log₂ x * Real.log 2 = Real.log x := by
  unfold log₂
  exact div_mul_cancel₀ _ log_two_positive.ne'

theorem admissible_log_lower {n k : ℕ} (h : dimensionsAdmissible n k) :
    8 ≤ log₂ (n : ℝ) := by
  have hn : (256 : ℝ) ≤ n := by exact_mod_cast h.1
  have hmono := log₂_mono (by norm_num : (0 : ℝ) < 256) hn
  have hbase : log₂ (256 : ℝ) = 8 := by
    convert log₂_two_pow 8 using 1; norm_num
  linarith

theorem admissible_k_lower {n k : ℕ} (h : dimensionsAdmissible n k) :
    12 * log₂ (n : ℝ) ≤ (k : ℝ) :=
  le_trans h.2.2 (min_le_left _ _)

theorem admissible_codim_lower {n k : ℕ} (h : dimensionsAdmissible n k) :
    12 * log₂ (n : ℝ) ≤ ((n - k : ℕ) : ℝ) := by
  have hm := le_trans h.2.2 (min_le_right _ _)
  simpa only [Nat.cast_sub h.2.1] using hm

theorem admissible_product_log_bound {n k : ℕ} (h : dimensionsAdmissible n k) :
    16 * log₂ (n : ℝ) ≤ (k : ℝ) * ((n - k : ℕ) : ℝ) := by
  have hl := admissible_log_lower h
  have hk := admissible_k_lower h
  have hm := admissible_codim_lower h
  have hp := mul_le_mul hk hm (by linarith : 0 ≤ 12 * log₂ (n : ℝ))
    (by positivity : (0 : ℝ) ≤ (k : ℝ))
  nlinarith

theorem admissible_log_coefficient_le {n k : ℕ} (h : dimensionsAdmissible n k) :
    3 * log₂ (n : ℝ) + 1 ≤ (n : ℝ) := by
  have hk := admissible_k_lower h
  have hkn : (k : ℝ) ≤ n := by exact_mod_cast h.2.1
  have hn : (256 : ℝ) ≤ n := by exact_mod_cast h.1
  linarith

theorem samplingThreshold_eq_codim {n k : ℕ} (hk : k ≤ n) :
    samplingThreshold n k = c₀ * (k : ℝ) * ((n - k : ℕ) : ℝ) /
      (2 ^ (n - k) : ℝ) := by
  have hpow : (2 ^ n : ℝ) = 2 ^ k * 2 ^ (n - k) := by
    rw [← pow_add, Nat.add_sub_of_le hk]
  unfold samplingThreshold
  rw [hpow]
  field_simp


theorem exp_nat_mul_log (x : ℝ) (m : ℕ) (hx : 0 < x) :
    Real.exp ((m : ℝ) * Real.log x) = x ^ m := by
  rw [Real.exp_nat_mul, Real.exp_log hx]

theorem admissible_codim_power_sq {n k : ℕ} (h : dimensionsAdmissible n k) :
    (n : ℝ) ^ 2 ≤ (2 ^ (n - k) : ℝ) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 256) h.1)
  have hl := admissible_log_lower h
  have hm := admissible_codim_lower h
  have ht : 2 * log₂ (n : ℝ) ≤ ((n - k : ℕ) : ℝ) := by linarith
  calc
    (n : ℝ) ^ 2 = Real.exp (2 * Real.log (n : ℝ)) := (exp_nat_mul_log _ 2 hn).symm
    _ ≤ Real.exp (((n - k : ℕ) : ℝ) * Real.log 2) := by
      apply Real.exp_le_exp.mpr
      have hp := mul_le_mul_of_nonneg_right ht log_two_positive.le
      rw [mul_assoc, log₂_mul_log_two] at hp
      exact hp
    _ = (2 ^ (n - k) : ℝ) := exp_nat_mul_log _ _ (by norm_num)

theorem admissible_product_le_sq {n k : ℕ} (h : dimensionsAdmissible n k) :
    (k : ℝ) * ((n - k : ℕ) : ℝ) ≤ (n : ℝ) ^ 2 := by
  have hk : (k : ℝ) ≤ n := by exact_mod_cast h.2.1
  have hm : ((n - k : ℕ) : ℝ) ≤ n := by exact_mod_cast (Nat.sub_le n k)
  have hp := mul_le_mul hk hm (by positivity : (0 : ℝ) ≤ ((n - k : ℕ) : ℝ))
    (by positivity : (0 : ℝ) ≤ (n : ℝ))
  simpa only [pow_two] using hp

theorem samplingThreshold_le_c₀ {n k : ℕ} (h : dimensionsAdmissible n k) :
    samplingThreshold n k ≤ c₀ := by
  rw [samplingThreshold_eq_codim h.2.1]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ (n - k))).mpr
  have hc : 0 ≤ c₀ := by unfold c₀; exact div_nonneg log_two_positive.le (by norm_num)
  calc
    c₀ * (k : ℝ) * ((n - k : ℕ) : ℝ) =
      c₀ * ((k : ℝ) * ((n - k : ℕ) : ℝ)) := by ring
    _ ≤ c₀ * (n : ℝ) ^ 2 := mul_le_mul_of_nonneg_left (admissible_product_le_sq h) hc
    _ ≤ c₀ * (2 ^ (n - k) : ℝ) := mul_le_mul_of_nonneg_left (admissible_codim_power_sq h) hc

theorem sampling_lt_half {n k : ℕ} {ρ : ℝ} (h : dimensionsAdmissible n k)
    (hρ : ρ ≤ samplingThreshold n k) : ρ < 1 / 2 := by
  have hc : c₀ < 1 / 8 := by unfold c₀; linarith [log_two_lt_one]
  linarith [samplingThreshold_le_c₀ h]

theorem logarithmicRate_nonneg {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ₁ : ρ ≤ 1) :
    0 ≤ logarithmicRate ρ := by
  unfold logarithmicRate
  have hlog := Real.log_nonpos (by linarith : 0 ≤ 1 - ρ) (by linarith : 1 - ρ ≤ 1)
  linarith

theorem logarithmicRate_le_two_mul {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ₁ : ρ ≤ 1 / 2) :
    logarithmicRate ρ ≤ 2 * ρ := by
  have hpos : 0 < 1 - ρ := by linarith
  have hi := Real.one_sub_inv_le_log_of_pos hpos
  have hp : logarithmicRate ρ ≤ ρ / (1 - ρ) := by
    unfold logarithmicRate
    apply (le_div_iff₀ hpos).mpr
    have hmul := mul_le_mul_of_nonneg_right hi hpos.le
    rw [sub_mul, one_mul, inv_mul_cancel₀ hpos.ne'] at hmul
    linarith
  have hb : ρ / (1 - ρ) ≤ 2 * ρ := by
    apply (div_le_iff₀ hpos).mpr
    nlinarith
  exact hp.trans hb

theorem logarithmicRate_power_bound {n k : ℕ} {ρ : ℝ}
    (h : dimensionsAdmissible n k) (hρ : 0 ≤ ρ) (hsmall : ρ ≤ samplingThreshold n k) :
    logarithmicRate ρ * (2 ^ (n - k) : ℝ) ≤
      2 * c₀ * (k : ℝ) * ((n - k : ℕ) : ℝ) := by
  have hhalf := (sampling_lt_half h hsmall).le
  have hp := mul_le_mul_of_nonneg_right (logarithmicRate_le_two_mul hρ hhalf)
    (by positivity : (0 : ℝ) ≤ 2 ^ (n - k))
  have hs := hsmall
  rw [samplingThreshold_eq_codim h.2.1] at hs
  have hs' := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ (n - k))).mp hs
  nlinarith


theorem sampleMass_nonneg_of_sampling {n k : ℕ} {ρ : ℝ}
    (h : dimensionsAdmissible n k) (hρ : 0 ≤ ρ) (hsmall : ρ ≤ samplingThreshold n k)
    (Q : RowSet n) : 0 ≤ sampleMass ρ Q := by
  apply sampleMass_nonneg ρ hρ
  linarith [sampling_lt_half h hsmall]


theorem self_le_logarithmicRate {ρ : ℝ} (hρ : ρ < 1) : ρ ≤ logarithmicRate ρ := by
  have hlog := Real.log_le_sub_one_of_pos (by linarith : 0 < 1 - ρ)
  unfold logarithmicRate
  linarith

end Paper
