/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import FourierFormalization.BinaryLinear
public import FourierFormalization.Counting
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-! Exact finite Grassmann counts and the manuscript's inclusive bounds. -/

@[expose] public section

noncomputable section

open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Paper

theorem grass_card_mul_prod (n d : ℕ) (hd : d ≤ n) :
    Nat.card (Grass n d) * ∏ i : Fin d, (2 ^ d - 2 ^ (i : ℕ)) =
      ∏ i : Fin d, (2 ^ n - 2 ^ (i : ℕ)) := by
  simpa only [Grass, BinarySpace, ZMod.card] using
    (SubspaceConvolution.card_finrank_eq_mul_prod_fin (K := ZMod 2) (n := n) (j := d) hd)

theorem grass_numerator_pos (n d : ℕ) (hd : d ≤ n) :
    0 < ∏ i : Fin d, (2 ^ n - 2 ^ (i : ℕ)) := by
  apply Finset.prod_pos
  intro i _
  exact Nat.sub_pos_of_lt (Nat.pow_lt_pow_right (by decide) (i.isLt.trans_le hd))

theorem grass_card_pos (n d : ℕ) (hd : d ≤ n) : 0 < Nat.card (Grass n d) := by
  have hprod := grass_numerator_pos n d hd
  rw [← grass_card_mul_prod n d hd] at hprod
  exact Nat.pos_of_mul_pos_right hprod

theorem grass_nonempty (n d : ℕ) (hd : d ≤ n) : Nonempty (Grass n d) :=
  (Nat.card_pos_iff.mp (grass_card_pos n d hd)).1

theorem grass_card_real_pos (n d : ℕ) (hd : d ≤ n) : (0 : ℝ) < Nat.card (Grass n d) := by
  exact_mod_cast grass_card_pos n d hd

private theorem cast_binary_power_sub (n i : ℕ) (hi : i ≤ n) :
    ((2 ^ n - 2 ^ i : ℕ) : ℝ) = (2 ^ n : ℝ) - (2 ^ i : ℝ) := by
  rw [Nat.cast_sub (Nat.pow_le_pow_right (by decide : 0 < 2) hi)]
  norm_cast

theorem grass_card_real_mul_prod (n d : ℕ) (hd : d ≤ n) :
    (Nat.card (Grass n d) : ℝ) * ∏ i : Fin d, ((2 ^ d : ℝ) - (2 ^ (i : ℕ) : ℝ)) =
      ∏ i : Fin d, ((2 ^ n : ℝ) - (2 ^ (i : ℕ) : ℝ)) := by
  have h := congrArg (fun x : ℕ => (x : ℝ)) (grass_card_mul_prod n d hd)
  push_cast only [Nat.cast_mul, Nat.cast_prod] at h
  simp_rw [cast_binary_power_sub d _ (Fin.isLt _).le,
    cast_binary_power_sub n _ ((Fin.isLt _).trans_le hd).le] at h
  exact h


theorem grass_denominator_real_pos (d : ℕ) :
    0 < ∏ i : Fin d, ((2 ^ d : ℝ) - (2 ^ (i : ℕ) : ℝ)) := by
  apply Finset.prod_pos
  intro i _
  rw [← cast_binary_power_sub d i i.isLt.le]
  exact_mod_cast Nat.sub_pos_of_lt (Nat.pow_lt_pow_right (by decide) i.isLt)

/-- The exact real Grassmann product, with empty product at dimension zero. -/
theorem grass_card_eq_prod (n d : ℕ) (hd : d ≤ n) :
    (Nat.card (Grass n d) : ℝ) =
      ∏ i : Fin d, (((2 ^ n : ℝ) - (2 ^ (i : ℕ) : ℝ)) /
        ((2 ^ d : ℝ) - (2 ^ (i : ℕ) : ℝ))) := by
  rw [Finset.prod_div_distrib]
  exact (eq_div_iff (ne_of_gt (grass_denominator_real_pos d))).mpr
    (grass_card_real_mul_prod n d hd)

private theorem grass_factor_lower (n d : ℕ) (hd : d ≤ n) (i : Fin d) :
    (2 ^ (n - d) : ℝ) * ((2 ^ d : ℝ) - (2 ^ (i : ℕ) : ℝ)) ≤
      (2 ^ n : ℝ) - (2 ^ (i : ℕ) : ℝ) := by
  have hpow : (2 ^ n : ℝ) = (2 ^ (n - d) : ℝ) * (2 ^ d : ℝ) := by
    rw [← pow_add, Nat.sub_add_cancel hd]
  have hc : (1 : ℝ) ≤ 2 ^ (n - d) := one_le_pow₀ (by norm_num)
  have hi : (0 : ℝ) ≤ 2 ^ (i : ℕ) := by positivity
  rw [hpow]
  nlinarith [mul_le_mul_of_nonneg_right hc hi]

private theorem grass_factor_upper (n d : ℕ) (hd : d ≤ n) (i : Fin d) :
    (2 ^ n : ℝ) - (2 ^ (i : ℕ) : ℝ) ≤
      (2 ^ (n - d + 1) : ℝ) * ((2 ^ d : ℝ) - (2 ^ (i : ℕ) : ℝ)) := by
  have hdpos : 0 < d := Nat.zero_lt_of_lt i.isLt
  have hile : (i : ℕ) ≤ d - 1 := by omega
  have hi : (2 ^ (i : ℕ) : ℝ) ≤ 2 ^ (d - 1) := by
    exact_mod_cast Nat.pow_le_pow_right (by decide : 0 < 2) hile
  have hdouble : (2 ^ d : ℝ) = 2 * 2 ^ (d - 1) := by
    conv_lhs => rw [← Nat.sub_add_cancel hdpos, pow_add]
    norm_num
    ring
  have hden : (2 ^ (d - 1) : ℝ) ≤ (2 ^ d : ℝ) - (2 ^ (i : ℕ) : ℝ) := by
    rw [hdouble]
    linarith
  calc
    (2 ^ n : ℝ) - (2 ^ (i : ℕ) : ℝ) ≤ (2 ^ n : ℝ) := sub_le_self _ (by positivity)
    _ = (2 ^ (n - d + 1) : ℝ) * 2 ^ (d - 1) := by
      rw [← pow_add]
      congr 1
      omega
    _ ≤ (2 ^ (n - d + 1) : ℝ) * ((2 ^ d : ℝ) - (2 ^ (i : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left hden (by positivity)

/-- Lemma 2.2: both weak bounds include zero and full dimension. -/
theorem grass_card_bounds (n d : ℕ) (hd : d ≤ n) :
    (2 ^ (d * (n - d)) : ℝ) ≤ Nat.card (Grass n d) ∧
      (Nat.card (Grass n d) : ℝ) ≤ 2 ^ (d * (n - d + 1)) := by
  have hden : ∀ i : Fin d, (0 : ℝ) ≤ (2 ^ d : ℝ) - (2 ^ (i : ℕ) : ℝ) := by
    intro i
    rw [← cast_binary_power_sub d i i.isLt.le]
    positivity
  have hlo := Finset.prod_le_prod₀
    (fun (i : Fin d) (_ : i ∈ Finset.univ) =>
      mul_nonneg (by positivity : (0 : ℝ) ≤ 2 ^ (n - d)) (hden i))
    (fun i (_ : i ∈ Finset.univ) => grass_factor_lower n d hd i)
  have hhi := Finset.prod_le_prod₀ (fun (i : Fin d) (_ : i ∈ Finset.univ) => by
      have : (2 ^ (i : ℕ) : ℝ) ≤ 2 ^ n := by
        exact_mod_cast Nat.pow_le_pow_right (by decide : 0 < 2) (i.isLt.le.trans hd)
      exact sub_nonneg.mpr this)
    (fun i (_ : i ∈ Finset.univ) => grass_factor_upper n d hd i)
  simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, ← pow_mul, Nat.mul_comm (n - d) d,
    Nat.mul_comm (n - d + 1) d] at hlo hhi
  rw [← grass_card_real_mul_prod n d hd] at hlo hhi
  exact ⟨(mul_le_mul_iff_left₀ (grass_denominator_real_pos d)).mp hlo,
    (mul_le_mul_iff_left₀ (grass_denominator_real_pos d)).mp hhi⟩

end Paper
