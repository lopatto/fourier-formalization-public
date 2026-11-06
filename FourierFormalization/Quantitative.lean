/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import FourierFormalization.Parameters
public import Mathlib.Order.Interval.Finset.Nat

/-! Explicit scalar and finite-range estimates for the quantitative reduction. -/

@[expose] public section
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Paper

theorem lowError_nonneg (n : ℕ) : 0 ≤ lowError n := by
  unfold lowError c₀
  exact div_nonneg (mul_nonneg (by norm_num) (div_nonneg log_two_positive.le (by norm_num)))
    (Nat.cast_nonneg n)

theorem covarianceKernel_le_highKernelCap {n k : ℕ} {ρ : ℝ}
    (h : dimensionsAdmissible n k) (hρ : 0 ≤ ρ) (hsmall : ρ ≤ samplingThreshold n k)
    (d : ℕ) (hd : d ∈ pairRange n k) :
    covarianceKernel ρ d ≤ highKernelCap n k ρ := by
  have hρ₁ : ρ ≤ 1 := by linarith [sampling_lt_half h hsmall]
  have hp := logarithmicRate_nonneg hρ hρ₁
  have hdm : d ≤ n - k := Nat.le_of_lt_succ (Finset.mem_range.mp hd)
  have hpow : (2 ^ d : ℝ) ≤ (2 ^ (n - k) : ℝ) := pow_le_pow_right₀ (by norm_num) hdm
  unfold covarianceKernel highKernelCap
  have hexp := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hpow hp)
  linarith

theorem high_range_card_bound {n k : ℕ} (h : dimensionsAdmissible n k) :
    (((pairRange n k).filter fun d => varianceCutoff n k < d).card : ℝ) ≤
      3 * log₂ (n : ℝ) + 1 := by
  have hl := admissible_log_lower h
  have hm := admissible_codim_lower h
  have hD : varianceCutoff n k ≤ n - k := by
    unfold varianceCutoff
    apply Nat.floor_le_of_le
    linarith
  have hset : (pairRange n k).filter (fun d => varianceCutoff n k < d) =
      Finset.Ioc (varianceCutoff n k) (n - k) := by
    ext d
    simp only [Finset.mem_filter, pairRange, Finset.mem_range, Finset.mem_Ioc]
    omega
  rw [hset, Nat.card_Ioc, Nat.cast_sub hD]
  have hfloor := Nat.sub_one_lt_floor (((n - k : ℕ) : ℝ) - 3 * log₂ (n : ℝ))
  change ((n - k : ℕ) : ℝ) - (varianceCutoff n k : ℝ) ≤ _
  unfold varianceCutoff
  linarith

theorem high_arithmetic_bound {n k : ℕ} {ρ : ℝ}
    (h : dimensionsAdmissible n k) (hρ : 0 ≤ ρ) (hsmall : ρ ≤ samplingThreshold n k) :
    (3 * log₂ (n : ℝ) + 1) * (highPairWeight n k * highKernelCap n k ρ) ≤
      highError n k := by
  have hl := admissible_log_lower h
  have hp := logarithmicRate_power_bound h hρ hsmall
  unfold highPairWeight highKernelCap highError
  apply mul_le_mul_of_nonneg_left _ (by linarith : 0 ≤ 3 * log₂ (n : ℝ) + 1)
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  unfold c₀ at hp
  nlinarith only [hp]

theorem quantitativeBound_le_inv {n k : ℕ} (h : dimensionsAdmissible n k) :
    quantitativeBound n k ≤ 1 / (n : ℝ) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 256) h.1)
  have hnlarge : (256 : ℝ) ≤ n := by exact_mod_cast h.1
  have hprod := admissible_product_log_bound h
  have hlog := log₂_mul_log_two (n : ℝ)
  have hscaled := mul_le_mul_of_nonneg_left hprod log_two_positive.le
  have hexp : Real.exp (-Real.log 2 * (k : ℝ) * ((n - k : ℕ) : ℝ) / 4) ≤
      1 / (n : ℝ) ^ 4 := by
    calc
      Real.exp (-Real.log 2 * (k : ℝ) * ((n - k : ℕ) : ℝ) / 4) ≤
          Real.exp (-(4 : ℝ) * Real.log (n : ℝ)) := by
        apply Real.exp_le_exp.mpr
        nlinarith only [hscaled, hlog]
      _ = 1 / (n : ℝ) ^ 4 := by
        rw [show -(4 : ℝ) * Real.log (n : ℝ) = -((4 : ℝ) * Real.log (n : ℝ)) by ring,
          Real.exp_neg]
        have he := exp_nat_mul_log (n : ℝ) 4 hn
        norm_num at he
        rw [he, one_div]
  have hcoef := admissible_log_coefficient_le h
  have hcoef0 : 0 ≤ 3 * log₂ (n : ℝ) + 1 := by linarith [admissible_log_lower h]
  have htail : (3 * log₂ (n : ℝ) + 1) *
      Real.exp (-Real.log 2 * (k : ℝ) * ((n - k : ℕ) : ℝ) / 4) ≤ 1 / (2 * (n : ℝ)) := by
    calc
      _ ≤ (3 * log₂ (n : ℝ) + 1) * (1 / (n : ℝ) ^ 4) :=
        mul_le_mul_of_nonneg_left hexp hcoef0
      _ ≤ (n : ℝ) * (1 / (n : ℝ) ^ 4) :=
        mul_le_mul_of_nonneg_right hcoef (by positivity)
      _ ≤ 1 / (2 * (n : ℝ)) := by
        apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * n)).mpr
        rw [mul_one_div, div_mul_eq_mul_div]
        apply (div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) ^ 4)).mpr
        nlinarith [sq_nonneg ((n : ℝ) ^ 2 - 2)]
  have hlow : 4 * c₀ / (n : ℝ) ≤ 1 / (2 * (n : ℝ)) := by
    unfold c₀
    apply (div_le_div_iff₀ hn (by positivity : (0 : ℝ) < 2 * n)).mpr
    nlinarith [log_two_lt_one]
  unfold quantitativeBound
  calc
    _ ≤ 1 / (2 * (n : ℝ)) + 1 / (2 * (n : ℝ)) := add_le_add hlow htail
    _ = 1 / (n : ℝ) := by ring


theorem low_kernel_bound {n k : ℕ} {ρ : ℝ}
    (h : dimensionsAdmissible n k) (hρ : 0 ≤ ρ) (hsmall : ρ ≤ samplingThreshold n k)
    (d : ℕ) (hd : d ≤ varianceCutoff n k) :
    covarianceKernel ρ d ≤ lowError n := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 256) h.1)
  have hnlarge : (256 : ℝ) ≤ n := by exact_mod_cast h.1
  have hl := admissible_log_lower h
  have hm := admissible_codim_lower h
  have hρ₁ : ρ ≤ 1 := by linarith [sampling_lt_half h hsmall]
  have hp0 := logarithmicRate_nonneg hρ hρ₁
  have hfloor : (varianceCutoff n k : ℝ) ≤
      ((n - k : ℕ) : ℝ) - 3 * log₂ (n : ℝ) := by
    unfold varianceCutoff
    apply Nat.floor_le
    linarith
  have hdc : (d : ℝ) ≤ varianceCutoff n k := by exact_mod_cast hd
  have hlogbound : (d : ℝ) * Real.log 2 + 3 * Real.log (n : ℝ) ≤
      ((n - k : ℕ) : ℝ) * Real.log 2 := by
    have hs := mul_le_mul_of_nonneg_right (hdc.trans hfloor) log_two_positive.le
    nlinarith only [hs, log₂_mul_log_two (n : ℝ)]
  have hpowers : (2 ^ d : ℝ) * (n : ℝ) ^ 3 ≤ (2 ^ (n - k) : ℝ) := by
    have he := Real.exp_le_exp.mpr hlogbound
    have hn3 := exp_nat_mul_log (n : ℝ) 3 hn
    norm_num at hn3
    rw [Real.exp_add, exp_nat_mul_log (2 : ℝ) d (by norm_num), hn3,
      exp_nat_mul_log (2 : ℝ) (n - k) (by norm_num)] at he
    exact he
  have hc : 0 ≤ c₀ := by unfold c₀; exact div_nonneg log_two_positive.le (by norm_num)
  have hcsmall : c₀ < 1 / 8 := by unfold c₀; linarith [log_two_lt_one]
  have hu0 : 0 ≤ logarithmicRate ρ * (2 ^ d : ℝ) := mul_nonneg hp0 (by positivity)
  have hmass : (logarithmicRate ρ * (2 ^ d : ℝ)) * (n : ℝ) ^ 3 ≤
      (2 * c₀) * (n : ℝ) ^ 2 := by
    calc
      _ = logarithmicRate ρ * ((2 ^ d : ℝ) * (n : ℝ) ^ 3) := by ring
      _ ≤ logarithmicRate ρ * (2 ^ (n - k) : ℝ) := mul_le_mul_of_nonneg_left hpowers hp0
      _ ≤ 2 * c₀ * (k : ℝ) * ((n - k : ℕ) : ℝ) := logarithmicRate_power_bound h hρ hsmall
      _ ≤ (2 * c₀) * (n : ℝ) ^ 2 := by
        have hs := mul_le_mul_of_nonneg_left (admissible_product_le_sq h)
          (by positivity : 0 ≤ 2 * c₀)
        nlinarith only [hs]
  have hcancel : (logarithmicRate ρ * (2 ^ d : ℝ)) * (n : ℝ) ≤ 2 * c₀ := by
    apply (mul_le_mul_iff_right₀ (by positivity : (0 : ℝ) < (n : ℝ) ^ 2)).mp
    nlinarith only [hmass]
  have hu : logarithmicRate ρ * (2 ^ d : ℝ) ≤ (2 * c₀) / (n : ℝ) :=
    (le_div_iff₀ hn).mpr hcancel
  have hu1 : logarithmicRate ρ * (2 ^ d : ℝ) ≤ 1 := by
    have hcnum : 2 * c₀ ≤ (n : ℝ) := by linarith
    exact hu.trans ((div_le_one hn).mpr hcnum)
  have habs : |logarithmicRate ρ * (2 ^ d : ℝ)| ≤ 1 := by
    rw [abs_of_nonneg hu0]
    exact hu1
  have hexp := Real.abs_exp_sub_one_le habs
  rw [abs_of_nonneg hu0] at hexp
  unfold covarianceKernel lowError
  calc
    _ ≤ |Real.exp (logarithmicRate ρ * (2 ^ d : ℝ)) - 1| := le_abs_self _
    _ ≤ 2 * (logarithmicRate ρ * (2 ^ d : ℝ)) := hexp
    _ ≤ 4 * c₀ / (n : ℝ) := by
      calc
        _ ≤ 2 * ((2 * c₀) / (n : ℝ)) := mul_le_mul_of_nonneg_left hu (by norm_num)
        _ = 4 * c₀ / (n : ℝ) := by ring

end Paper
