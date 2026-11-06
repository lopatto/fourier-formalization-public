/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import FourierFormalization.Characters
public import FourierFormalization.SubspaceFourier
public import FourierFormalization.Grassmann
public import FourierFormalization.Moments
public import FourierFormalization.Quantitative
public import FourierFormalization.TailEstimates
public import FourierFormalization.PairCounting

/-! Assembly of the manuscript's quantitative theorem from the proved Fourier,
finite probability, combinatorial and scalar prerequisites. -/

@[expose] public section

noncomputable section

open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Paper

/-- The logarithmic and actual-expectation bridges carry no extra hypotheses. -/
theorem samplingIdentities : SamplingIdentities :=
  ⟨logarithmic_threshold, recovery_threshold, fun n ρ _ _ => expectedRows_eq n ρ⟩

theorem kernelObligations (n k : ℕ) (ρ : ℝ)
    (hdim : dimensionsAdmissible n k) (hρ : 0 ≤ ρ) (hsmall : ρ ≤ samplingThreshold n k) :
    KernelObligations n k ρ := by
  let : Nonempty (Grass n k) := grass_nonempty n k hdim.2.1
  have hρlt : ρ < 1 := lt_trans (sampling_lt_half hdim hsmall) (by norm_num)
  refine {
    mass_nonnegative := sampleMass_nonneg_of_sampling hdim hρ hsmall
    mass_total := sampleMass_sum n ρ
    indicator_nonzero := fun V => normalizedIndicator_nonzero V.val
    indicator_sparse := normalizedIndicator_sparse
    indicator_kernel := fun V Q hV => normalizedIndicator_kernel_of_misses V.val Q hV
    mean_positive := witnessCount_mean_positive n k ρ hρlt
    variance_identity := normalized_variance_identity n k ρ hρlt
    weight_mass := (pairWeight_sum n k).le
    low_nonnegative := lowError_nonneg n
    low_kernel := fun d _ hd => low_kernel_bound hdim hρ hsmall d hd
    high_weight := fun _ hd hcut => pairWeight_high_bound hdim hd hcut
    high_kernel := covarianceKernel_le_highKernelCap hdim hρ hsmall
    high_card := high_range_card_bound hdim
    high_arithmetic := high_arithmetic_bound hdim hρ hsmall
    error_le := quantitativeBound_le_inv hdim }

theorem kernelObligationFamily : KernelObligationFamily := kernelObligations

/-- Theorem 3.1, including the normalized indicator of the same missed subspace. -/
theorem finiteKernel (n k : ℕ) (ρ : ℝ)
    (hdim : dimensionsAdmissible n k) (hρ : 0 ≤ ρ)
    (hsmall : ρ ≤ samplingThreshold n k) :
    probability ρ (fun Q => witnessCount n k Q = 0) ≤ quantitativeBound n k ∧
    quantitativeBound n k ≤ 1 / (n : ℝ) ∧
    1 - 1 / (n : ℝ) ≤ probability ρ (MissedSubspace n k) ∧
    1 - 1 / (n : ℝ) ≤ probability ρ (SparseKernel (n := n) (2 ^ k)) ∧
    1 - 1 / (n : ℝ) ≤ probability ρ (fun Q => ∃ V : Grass n k,
      Misses Q V.val ∧ normalizedIndicator V.val ≠ 0 ∧
      Sparse (2 ^ k) (normalizedIndicator V.val) ∧
      KernelOn Q (normalizedIndicator V.val)) := by
  exact finite_kernel_of_obligations (kernelObligations n k ρ hdim hρ hsmall)

/-- Corollary 3.4, uniform in the sparsity and row-inclusion parameters. -/
theorem uniformKernel :
    ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ (n k : ℕ) (ρ : ℝ), N₀ ≤ n →
      dimensionsAdmissible n k → 0 ≤ ρ →
      ρ ≤ c₀ * (2 ^ k : ℝ) / (2 ^ n : ℝ) * log₂ (2 ^ k : ℝ) *
        log₂ ((2 ^ n : ℝ) / (2 ^ k : ℝ)) →
      1 - ε < probability ρ (SparseKernel (n := n) (2 ^ k)) := by
  exact uniform_kernel_of_obligations kernelObligationFamily samplingIdentities

/-- Theorem 3.6, finite success bounds and their strict contrapositive. -/
theorem finiteRecovery (n k : ℕ) (ρ δ : ℝ)
    (hdim : dimensionsAdmissible n k) (hρ : 0 ≤ ρ) (hρ₁ : ρ ≤ 1)
    (hδ₀ : 0 < δ) (hδ₁ : δ < 1) :
    (expectedRows n ρ ≤ recoveryThreshold n k →
      probability ρ (Recovery (n := n) (2 ^ k)) ≤ 1 / (n : ℝ) ∧
      probability ρ (RIP (n := n) (2 ^ k) δ) ≤ 1 / (n : ℝ)) ∧
    ((1 / (n : ℝ) < probability ρ (Recovery (n := n) (2 ^ k)) ∨
      1 / (n : ℝ) < probability ρ (RIP (n := n) (2 ^ k) δ)) →
      recoveryThreshold n k < expectedRows n ρ) := by
  exact finite_recovery_principal_of_obligations kernelObligationFamily samplingIdentities
    n k ρ δ hdim hρ hρ₁ hδ₀ hδ₁

/-- The same necessary sampling bound applies to any exact uniform decoder
and to complex RIP with sample-dependent scalar normalization. -/
theorem finiteDecoderComplex (n k : ℕ) (ρ δ : ℝ)
    (hdim : dimensionsAdmissible n k) (hρ : 0 ≤ ρ) (hρ₁ : ρ ≤ 1)
    (_hδ₀ : 0 < δ) (hδ₁ : δ < 1)
    (hq : expectedRows n ρ ≤ recoveryThreshold n k) :
    probability ρ (UniformDecoder (n := n) (2 ^ k)) ≤ 1 / (n : ℝ) ∧
      probability ρ (ComplexRIP (n := n) (2 ^ k) δ) ≤ 1 / (n : ℝ) := by
  exact finite_decoder_complex_of_obligations
    (kernelObligations n k ρ hdim hρ
      (sampling_bound_of_expected_rows samplingIdentities hdim.2.1 hρ hρ₁ hq)) hδ₁

/-- Theorem 3.6's explicit positive-constant lower bound along arbitrary
admissible sequences whose dimensions tend to infinity. -/
theorem necessarySampling (n k : ℕ → ℕ) (ρ : ℕ → ℝ) (δ : ℝ)
    (hδ₀ : 0 < δ) (hδ₁ : δ < 1)
    (hn : ∀ N : ℕ, ∃ J : ℕ, ∀ j ≥ J, N ≤ n j)
    (hadm : ∃ J : ℕ, ∀ j ≥ J,
      dimensionsAdmissible (n j) (k j) ∧ 0 ≤ ρ j ∧ ρ j ≤ 1)
    (hsuccess : ∃ η : ℝ, 0 < η ∧
      ((∃ J : ℕ, ∀ j ≥ J, η ≤ probability (ρ j) (Recovery (n := n j) (2 ^ k j))) ∨
       (∃ J : ℕ, ∀ j ≥ J, η ≤ probability (ρ j) (RIP (n := n j) (2 ^ k j) δ)))) :
    ∃ J : ℕ, ∀ j ≥ J,
      recoveryThreshold (n j) (k j) < expectedRows (n j) (ρ j) := by
  exact necessary_sampling_of_obligations kernelObligationFamily samplingIdentities
    n k ρ δ hδ₀ hδ₁ hn hadm hsuccess

/-- The Walsh family exhibits the manuscript's bounded orthonormal example
with the same necessary sampling conclusion. -/
theorem boundedOrthonormalExample :
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
        ((∃ J : ℕ, ∀ j ≥ J,
          η ≤ probability (ρ j) (Recovery (n := n j) (2 ^ k j))) ∨
         (∃ J : ℕ, ∀ j ≥ J,
          η ≤ probability (ρ j) (RIP (n := n j) (2 ^ k j) δ)))) →
      ∃ J : ℕ, ∀ j ≥ J,
        recoveryThreshold (n j) (k j) < expectedRows (n j) (ρ j)) := by
  exact bounded_orthonormal_example_of_obligations characterObligations
    kernelObligationFamily samplingIdentities

end Paper
