/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import FourierFormalization.Sampling
public import FourierFormalization.BinaryLinear
public import FourierFormalization.Reduction

/-! Finite centered moments and exact moments of missed-subspace indicators.
No independence of the subspace indicators is assumed. -/

@[expose] public section

noncomputable section

open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Paper

def variance {n : ℕ} (ρ : ℝ) (X : RowSet n → ℝ) : ℝ :=
  expectation ρ (fun Q => (X Q - expectation ρ X) ^ 2)

def covariance {n : ℕ} (ρ : ℝ) (X Y : RowSet n → ℝ) : ℝ :=
  expectation ρ (fun Q => X Q * Y Q) - expectation ρ X * expectation ρ Y

theorem expectation_congr {n : ℕ} (ρ : ℝ) (X Y : RowSet n → ℝ)
    (h : ∀ Q, X Q = Y Q) : expectation ρ X = expectation ρ Y :=
  congrArg (expectation ρ) (funext h)

theorem variance_eq_second_moment_sub {n : ℕ} (ρ : ℝ) (X : RowSet n → ℝ) :
    variance ρ X = expectation ρ (fun Q => X Q ^ 2) - expectation ρ X ^ 2 := by
  unfold variance
  calc
    _ = expectation ρ (fun Q => X Q ^ 2 - (2 * expectation ρ X) * X Q +
        expectation ρ X ^ 2) := by
      apply expectation_congr
      intro Q
      ring
    _ = _ := by
      rw [expectation_add, expectation_sub, expectation_const_mul, expectation_const]
      ring

theorem variance_eq_covariance_self {n : ℕ} (ρ : ℝ) (X : RowSet n → ℝ) :
    variance ρ X = covariance ρ X X := by
  rw [variance_eq_second_moment_sub]
  simp only [covariance, pow_two]

theorem covariance_symm {n : ℕ} (ρ : ℝ) (X Y : RowSet n → ℝ) :
    covariance ρ X Y = covariance ρ Y X := by
  simp only [covariance, mul_comm]

theorem covariance_sum_sum {n : ℕ} {ι κ : Type*} (ρ : ℝ) (s : Finset ι) (t : Finset κ)
    (X : ι → RowSet n → ℝ) (Y : κ → RowSet n → ℝ) :
    covariance ρ (fun Q => ∑ i ∈ s, X i Q) (fun Q => ∑ j ∈ t, Y j Q) =
      ∑ i ∈ s, ∑ j ∈ t, covariance ρ (X i) (Y j) := by
  unfold covariance
  simp_rw [Finset.sum_mul_sum, expectation_sum]
  simp only [Finset.sum_sub_distrib, Finset.sum_mul_sum]

theorem variance_sum_covariance {n : ℕ} {ι : Type*} (ρ : ℝ) (s : Finset ι)
    (X : ι → RowSet n → ℝ) :
    variance ρ (fun Q => ∑ i ∈ s, X i Q) = ∑ i ∈ s, ∑ j ∈ s, covariance ρ (X i) (X j) := by
  rw [variance_eq_covariance_self, covariance_sum_sum]

def subspaceRows {n : ℕ} (V : Submodule (ZMod 2) (BinarySpace n)) : RowSet n :=
  Finset.univ.filter (fun a => a ∈ V)

@[simp] theorem mem_subspaceRows {n : ℕ} (V : Submodule (ZMod 2) (BinarySpace n))
    (a : BinarySpace n) : a ∈ subspaceRows V ↔ a ∈ V := by
  simp [subspaceRows]

theorem subspaceRows_card {n : ℕ} (V : Submodule (ZMod 2) (BinarySpace n)) :
    (subspaceRows V).card = Nat.card V := by
  let : Fintype V := Fintype.ofFinite V
  rw [Nat.card_eq_fintype_card]
  exact (Fintype.card_subtype (fun a : BinarySpace n => a ∈ V)).symm

theorem misses_iff_avoidance {n : ℕ} (Q : RowSet n)
    (V : Submodule (ZMod 2) (BinarySpace n)) :
    Misses Q V ↔ ∀ a ∈ subspaceRows (annihilator V), a ∉ Q := by
  constructor
  · intro h a ha hQ
    exact h a hQ ((mem_subspaceRows _ _).mp ha)
  · intro h a ha haV
    exact h a ((mem_subspaceRows _ _).mpr haV) ha

theorem probability_misses {n : ℕ} (ρ : ℝ)
    (V : Submodule (ZMod 2) (BinarySpace n)) :
    probability ρ (fun Q => Misses Q V) = (1 - ρ) ^ Nat.card (annihilator V) := by
  calc
    _ = probability ρ (fun Q => ∀ a ∈ subspaceRows (annihilator V), a ∉ Q) := by
      apply probability_congr
      intro Q
      exact misses_iff_avoidance Q V
    _ = (1 - ρ) ^ (subspaceRows (annihilator V)).card := probability_avoidance ρ _
    _ = _ := by rw [subspaceRows_card]

theorem expectation_witnessIndicator {n : ℕ} (ρ : ℝ)
    (V : Submodule (ZMod 2) (BinarySpace n)) :
    expectation ρ (witnessIndicator V) = (1 - ρ) ^ Nat.card (annihilator V) := by
  calc
    _ = probability ρ (fun Q => Misses Q V) := by
      unfold witnessIndicator
      exact expectation_indicator ρ (fun Q => Misses Q V)
    _ = _ := probability_misses ρ V

theorem witnessIndicator_mean (n k : ℕ) (ρ : ℝ) (V : Grass n k) :
    expectation ρ (witnessIndicator V.val) = (1 - ρ) ^ (2 ^ (n - k)) := by
  rw [expectation_witnessIndicator, annihilator_card, V.property]

theorem witnessCount_mean (n k : ℕ) (ρ : ℝ) :
    expectation ρ (witnessCount n k) =
      (Nat.card (Grass n k) : ℝ) * (1 - ρ) ^ (2 ^ (n - k)) := by
  unfold witnessCount
  rw [expectation_sum]
  simp [witnessIndicator_mean, Nat.card_eq_fintype_card]

theorem witnessCount_mean_positive (n k : ℕ) (ρ : ℝ) (hρ : ρ < 1)
    [Nonempty (Grass n k)] : 0 < expectation ρ (witnessCount n k) := by
  rw [witnessCount_mean]
  apply mul_pos
  · rw [Nat.card_eq_fintype_card]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (Grass n k))
  · exact pow_pos (sub_pos.mpr hρ) _

theorem witnessCount_variance_covariance (n k : ℕ) (ρ : ℝ) :
    variance ρ (witnessCount n k) =
      ∑ U : Grass n k, ∑ V : Grass n k,
        covariance ρ (witnessIndicator U.val) (witnessIndicator V.val) := by
  exact variance_sum_covariance ρ Finset.univ (fun V : Grass n k => witnessIndicator V.val)

theorem expectation_product_witnessIndicator {n : ℕ} (ρ : ℝ)
    (U V : Submodule (ZMod 2) (BinarySpace n)) :
    expectation ρ (fun Q => witnessIndicator U Q * witnessIndicator V Q) =
      (1 - ρ) ^ (subspaceRows (annihilator U) ∪ subspaceRows (annihilator V)).card := by
  calc
    _ = probability ρ (fun Q => Misses Q U ∧ Misses Q V) := by
      unfold expectation probability witnessIndicator
      apply Finset.sum_congr rfl
      intro Q _
      by_cases hU : Misses Q U <;> by_cases hV : Misses Q V <;> simp [hU, hV]
    _ = probability ρ (fun Q =>
        (∀ a ∈ subspaceRows (annihilator U), a ∉ Q) ∧
        (∀ b ∈ subspaceRows (annihilator V), b ∉ Q)) := by
      apply probability_congr
      intro Q
      rw [misses_iff_avoidance, misses_iff_avoidance]
    _ = _ := probability_joint_avoidance ρ _ _

theorem covariance_witnessIndicator (n k : ℕ) (ρ : ℝ) (U V : Grass n k) :
    covariance ρ (witnessIndicator U.val) (witnessIndicator V.val) =
      (1 - ρ) ^ (subspaceRows (annihilator U.val) ∪ subspaceRows (annihilator V.val)).card -
        ((1 - ρ) ^ (2 ^ (n - k))) ^ 2 := by
  unfold covariance
  rw [expectation_product_witnessIndicator, witnessIndicator_mean, witnessIndicator_mean, pow_two]

theorem subspaceRows_inf {n : ℕ} (U V : Submodule (ZMod 2) (BinarySpace n)) :
    subspaceRows (U ⊓ V) = subspaceRows U ∩ subspaceRows V := by
  ext a
  simp

theorem annihilator_union_card (n k : ℕ) (U V : Grass n k) :
    (subspaceRows (annihilator U.val) ∪ subspaceRows (annihilator V.val)).card +
        2 ^ intersectionDimension U.val V.val = 2 ^ (n - k) + 2 ^ (n - k) := by
  have h := Finset.card_union_add_card_inter
    (subspaceRows (annihilator U.val)) (subspaceRows (annihilator V.val))
  rw [← subspaceRows_inf, subspaceRows_card, subspaceRows_card, subspaceRows_card,
    subspace_card, annihilator_card, annihilator_card, U.property, V.property] at h
  exact h

theorem bernoulli_power_eq_exp (ρ : ℝ) (hρ : ρ < 1) (r : ℕ) :
    (1 - ρ) ^ r = Real.exp (-logarithmicRate ρ * (r : ℝ)) := by
  rw [logarithmicRate, neg_neg, mul_comm, Real.exp_nat_mul,
    Real.exp_log (sub_pos.mpr hρ)]

theorem witnessIndicator_product_mean (n k : ℕ) (ρ : ℝ) (hρ : ρ < 1)
    (U V : Grass n k) :
    expectation ρ (fun Q => witnessIndicator U.val Q * witnessIndicator V.val Q) =
      ((1 - ρ) ^ (2 ^ (n - k))) ^ 2 *
        Real.exp (logarithmicRate ρ * (2 ^ intersectionDimension U.val V.val : ℝ)) := by
  have hcard :
      ((subspaceRows (annihilator U.val) ∪ subspaceRows (annihilator V.val)).card : ℝ) =
        (2 ^ (n - k) : ℝ) + (2 ^ (n - k) : ℝ) -
          (2 ^ intersectionDimension U.val V.val : ℝ) := by
    have hcast :
        ((subspaceRows (annihilator U.val) ∪ subspaceRows (annihilator V.val)).card : ℝ) +
          (2 ^ intersectionDimension U.val V.val : ℝ) =
            (2 ^ (n - k) : ℝ) + (2 ^ (n - k) : ℝ) := by
      exact_mod_cast annihilator_union_card n k U V
    linarith
  rw [expectation_product_witnessIndicator, bernoulli_power_eq_exp ρ hρ,
    bernoulli_power_eq_exp ρ hρ]
  push_cast
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  rw [hcard]
  ring

/-- Claim 3.2, with the zero-dimensional intersection contributing one point.
The only parameter restriction is the strict upper endpoint needed for log. -/
theorem witnessIndicator_covariance_ratio (n k : ℕ) (ρ : ℝ) (hρ : ρ < 1)
    (U V : Grass n k) :
    covariance ρ (witnessIndicator U.val) (witnessIndicator V.val) /
        ((1 - ρ) ^ (2 ^ (n - k))) ^ 2 =
      covarianceKernel ρ (intersectionDimension U.val V.val) := by
  have hs : (1 - ρ) ^ (2 ^ (n - k)) ≠ 0 :=
    ne_of_gt (pow_pos (sub_pos.mpr hρ) _)
  unfold covariance covarianceKernel
  rw [witnessIndicator_product_mean n k ρ hρ U V,
    witnessIndicator_mean, witnessIndicator_mean]
  apply (div_eq_iff (pow_ne_zero 2 hs)).mpr
  ring

theorem intersectionDimension_le (n k : ℕ) (U V : Grass n k) :
    intersectionDimension U.val V.val ≤ n - k := by
  calc
    _ ≤ Module.finrank (ZMod 2) (annihilator U.val) := Submodule.finrank_mono inf_le_left
    _ = n - k := by rw [annihilator_finrank, U.property]

theorem sum_pairs_by_intersectionDimension (n k : ℕ) (f : ℕ → ℝ) :
    (∑ U : Grass n k, ∑ V : Grass n k, f (intersectionDimension U.val V.val)) =
      ∑ d ∈ pairRange n k, (pairCount n k d : ℝ) * f d := by
  have hm : ∀ UV ∈ (Finset.univ : Finset (Grass n k × Grass n k)),
      intersectionDimension UV.1.val UV.2.val ∈ pairRange n k := by
    intro UV _
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (intersectionDimension_le n k UV.1 UV.2))
  have hcount : ∀ d : ℕ,
      ((Finset.univ : Finset (Grass n k × Grass n k)).filter fun UV =>
        intersectionDimension UV.1.val UV.2.val = d).card = pairCount n k d := by
    intro d
    unfold pairCount
    rw [Nat.card_eq_fintype_card]
    exact (Fintype.card_subtype
      (fun UV : Grass n k × Grass n k => intersectionDimension UV.1.val UV.2.val = d)).symm
  have hf := Finset.sum_fiberwise_of_maps_to' hm f
  simpa only [Finset.sum_const, nsmul_eq_mul, hcount, Fintype.sum_prod_type] using hf.symm

theorem pairCount_sum (n k : ℕ) :
    (∑ d ∈ pairRange n k, (pairCount n k d : ℝ)) = (Nat.card (Grass n k) : ℝ) ^ 2 := by
  have h := sum_pairs_by_intersectionDimension n k (fun _ => 1)
  simpa [Nat.card_eq_fintype_card, pow_two] using h.symm

theorem pairWeight_sum (n k : ℕ) [Nonempty (Grass n k)] :
    (∑ d ∈ pairRange n k, pairWeight n k d) = 1 := by
  have hM : (Nat.card (Grass n k) : ℝ) ≠ 0 := by
    rw [Nat.card_eq_fintype_card]
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card (Grass n k) ≠ 0)
  unfold pairWeight
  calc
    _ = (∑ d ∈ pairRange n k, (pairCount n k d : ℝ)) /
        (Nat.card (Grass n k) : ℝ) ^ 2 := by
      simp only [div_eq_mul_inv, Finset.sum_mul]
    _ = 1 := by rw [pairCount_sum, div_self (pow_ne_zero 2 hM)]

theorem normalized_variance_identity (n k : ℕ) (ρ : ℝ) (hρ : ρ < 1)
    [Nonempty (Grass n k)] :
    expectation ρ (fun Q => (witnessCount n k Q - expectation ρ (witnessCount n k)) ^ 2) /
        expectation ρ (witnessCount n k) ^ 2 =
      ∑ d ∈ pairRange n k, pairWeight n k d * covarianceKernel ρ d := by
  have hs : (1 - ρ) ^ (2 ^ (n - k)) ≠ 0 := ne_of_gt (pow_pos (sub_pos.mpr hρ) _)
  have hM : (Nat.card (Grass n k) : ℝ) ≠ 0 := by
    rw [Nat.card_eq_fintype_card]
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card (Grass n k) ≠ 0)
  have hcov : ∀ U V : Grass n k,
      covariance ρ (witnessIndicator U.val) (witnessIndicator V.val) =
        ((1 - ρ) ^ (2 ^ (n - k))) ^ 2 *
          covarianceKernel ρ (intersectionDimension U.val V.val) := by
    intro U V
    have h := (div_eq_iff (pow_ne_zero 2 hs)).mp
      (witnessIndicator_covariance_ratio n k ρ hρ U V)
    simpa only [mul_comm] using h
  change variance ρ (witnessCount n k) / expectation ρ (witnessCount n k) ^ 2 = _
  rw [witnessCount_variance_covariance, witnessCount_mean]
  simp_rw [hcov, ← Finset.mul_sum]
  rw [sum_pairs_by_intersectionDimension]
  unfold pairWeight
  have hsum : (∑ d ∈ pairRange n k,
      (pairCount n k d : ℝ) / (Nat.card (Grass n k) : ℝ) ^ 2 * covarianceKernel ρ d) =
      (∑ d ∈ pairRange n k, (pairCount n k d : ℝ) * covarianceKernel ρ d) /
        (Nat.card (Grass n k) : ℝ) ^ 2 := by
    calc
      _ = ∑ d ∈ pairRange n k, ((pairCount n k d : ℝ) * covarianceKernel ρ d) /
          (Nat.card (Grass n k) : ℝ) ^ 2 := by
        apply Finset.sum_congr rfl
        intro d _
        ring
      _ = _ := by simp only [div_eq_mul_inv, Finset.sum_mul]
  rw [hsum]
  field_simp [hs, hM]

end Paper
