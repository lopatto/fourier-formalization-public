/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import FourierFormalization.Reduction
public import FourierFormalization.Parameters

/-! Scalar estimates used after the quotient encoding of an ordered pair of
subspaces. The counting hypotheses are explicit upstream intermediate bounds. -/

@[expose] public section

noncomputable section

namespace Paper

theorem tail_exponent_scalar (k m L t : ℝ) (hL : 24 ≤ L)
    (hk : 4 * L ≤ k) (hm : 4 * L ≤ m) (_ht : 0 ≤ t) (htL : t ≤ L) :
    (m - t) * (k + t + 1) + 2 * t * (k + 1) ≤ 3 * k * m / 2 := by
  have hstep : 0 ≤ (L - t) * (k + m + 1 - L - t) :=
    mul_nonneg (sub_nonneg.mpr htL) (by linarith)
  have hreplace : (m - t) * (k + t + 1) + 2 * t * (k + 1) ≤
      (m - L) * (k + L + 1) + 2 * L * (k + 1) := by
    nlinarith only [hstep]
  have h₀ : 0 ≤ L * (L - 5) := mul_nonneg (by linarith) (by linarith)
  have h₁ : 0 ≤ L * (k - 4 * L) := mul_nonneg (by linarith) (by linarith)
  have h₂ : 0 ≤ (L - 1) * (m - 4 * L) := mul_nonneg (by linarith) (by linarith)
  have h₃ : 0 ≤ (k - 4 * L) * (m - 4 * L) :=
    mul_nonneg (by linarith) (by linarith)
  have hfinal : (m - L) * (k + L + 1) + 2 * L * (k + 1) ≤ 3 * k * m / 2 := by
    nlinarith only [h₀, h₁, h₂, h₃]
  exact hreplace.trans hfinal

theorem exponential_ratio_bound (T M c : ℝ)
    (hT : T ≤ Real.exp (3 * c / 2)) (hM : Real.exp c ≤ M) :
    T / M ^ 2 ≤ Real.exp (-c / 2) := by
  have hMpos : 0 < M := (Real.exp_pos c).trans_le hM
  have hM2 : (Real.exp c) ^ 2 ≤ M ^ 2 := by
    simpa only [pow_two] using mul_le_mul hM hM (Real.exp_nonneg c) hMpos.le
  apply (div_le_iff₀ (sq_pos_of_pos hMpos)).mpr
  calc
    T ≤ Real.exp (3 * c / 2) := hT
    _ = Real.exp (-c / 2) * (Real.exp c) ^ 2 := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (-c / 2) * M ^ 2 :=
      mul_le_mul_of_nonneg_left hM2 (Real.exp_nonneg _)

theorem tail_count_exponent_bound {n k d : ℕ} (ha : dimensionsAdmissible n k)
    (hd : d ≤ n - k) (hcut : varianceCutoff n k < d) :
    ((d * (n - d + 1) + 2 * (n - k - d) * (k + 1) : ℕ) : ℝ) ≤
      3 * (k : ℝ) * ((n - k : ℕ) : ℝ) / 2 := by
  have hL : 24 ≤ 3 * log₂ (n : ℝ) := by linarith [admissible_log_lower ha]
  have hk : 4 * (3 * log₂ (n : ℝ)) ≤ (k : ℝ) := by linarith [admissible_k_lower ha]
  have hm : 4 * (3 * log₂ (n : ℝ)) ≤ ((n - k : ℕ) : ℝ) := by
    linarith [admissible_codim_lower ha]
  have ht : 0 ≤ ((n - k : ℕ) : ℝ) - (d : ℝ) := by
    exact sub_nonneg.mpr (by exact_mod_cast hd)
  have hfloor : ((n - k : ℕ) : ℝ) - 3 * log₂ (n : ℝ) < (d : ℝ) :=
    Nat.lt_of_floor_lt hcut
  have htL : ((n - k : ℕ) : ℝ) - (d : ℝ) ≤ 3 * log₂ (n : ℝ) := by linarith
  have hpoly := tail_exponent_scalar (k : ℝ) ((n - k : ℕ) : ℝ)
    (3 * log₂ (n : ℝ)) (((n - k : ℕ) : ℝ) - (d : ℝ)) hL hk hm ht htL
  have hnd : d ≤ n := hd.trans (Nat.sub_le n k)
  have hnm : (n : ℝ) = (k : ℝ) + ((n - k : ℕ) : ℝ) := by
    exact_mod_cast (Nat.add_sub_of_le ha.2.1).symm
  have heq : ((d * (n - d + 1) + 2 * (n - k - d) * (k + 1) : ℕ) : ℝ) =
      (((n - k : ℕ) : ℝ) - (((n - k : ℕ) : ℝ) - (d : ℝ))) *
          ((k : ℝ) + (((n - k : ℕ) : ℝ) - (d : ℝ)) + 1) +
        2 * (((n - k : ℕ) : ℝ) - (d : ℝ)) * ((k : ℝ) + 1) := by
    push_cast [Nat.cast_sub hnd, Nat.cast_sub hd]
    rw [hnm]
    ring
  rw [heq]
  exact hpoly

/-- Convert the quotient-counting estimate and Grassmann lower bound into
the high-stratum estimate used in Claim 3.3. Both inputs are raw counting
inequalities, not a probability or principal conclusion. -/
theorem high_pairWeight_of_count_bound {n k d : ℕ} (ha : dimensionsAdmissible n k)
    (hd : d ≤ n - k) (hcut : varianceCutoff n k < d)
    (hgrass : (2 : ℝ) ^ (k * (n - k)) ≤ (Nat.card (Grass n k) : ℝ))
    (hcount : (pairCount n k d : ℝ) ≤
      (2 : ℝ) ^ (d * (n - d + 1) + 2 * (n - k - d) * (k + 1))) :
    pairWeight n k d ≤ highPairWeight n k := by
  have hc : Real.exp (Real.log 2 * (k : ℝ) * ((n - k : ℕ) : ℝ)) =
      (2 : ℝ) ^ (k * (n - k)) := by
    calc
      _ = Real.exp (((k * (n - k) : ℕ) : ℝ) * Real.log 2) := by
        congr 1
        push_cast
        ring
      _ = _ := exp_nat_mul_log 2 (k * (n - k)) (by norm_num)
  have hT : (pairCount n k d : ℝ) ≤
      Real.exp (3 * (Real.log 2 * (k : ℝ) * ((n - k : ℕ) : ℝ)) / 2) := by
    apply hcount.trans
    rw [← exp_nat_mul_log 2 (d * (n - d + 1) + 2 * (n - k - d) * (k + 1)) (by norm_num)]
    apply Real.exp_le_exp.mpr
    have he := mul_le_mul_of_nonneg_left (tail_count_exponent_bound ha hd hcut)
      log_two_positive.le
    nlinarith only [he]
  have hr := exponential_ratio_bound (pairCount n k d : ℝ) (Nat.card (Grass n k) : ℝ)
    (Real.log 2 * (k : ℝ) * ((n - k : ℕ) : ℝ)) hT (hc.trans_le hgrass)
  unfold pairWeight highPairWeight
  calc
    _ ≤ Real.exp (-(Real.log 2 * (k : ℝ) * ((n - k : ℕ) : ℝ)) / 2) := hr
    _ = _ := by congr 1; ring

end Paper
