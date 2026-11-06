/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import FourierFormalization.Definitions
public import FourierFormalization.DefinitionLemmas
public import FourierFormalization.ReductionLogic

/-!
Finite second-moment and recovery consequences of Fourier, moment, pair-counting
and scalar estimates. `MainTheorems` supplies these estimates from proved lemmas.
-/

@[expose] public section

noncomputable section

open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Paper
/-- Dimension of the intersection of two binary annihilators. -/
def intersectionDimension {n : ℕ} (U V : Submodule (ZMod 2) (BinarySpace n)) : ℕ :=
  Module.finrank (ZMod 2) ↥(annihilator U ⊓ annihilator V)
/-- Number of ordered subspace pairs with a prescribed annihilator intersection dimension. -/
def pairCount (n k d : ℕ) : ℕ :=
  Nat.card {UV : Grass n k × Grass n k //
    intersectionDimension UV.1.val UV.2.val = d}
/-- Ordered-pair count divided by the squared Grassmannian cardinality. -/
def pairWeight (n k d : ℕ) : ℝ :=
  (pairCount n k d : ℝ) / (Nat.card (Grass n k) : ℝ) ^ 2
/-- Natural-logarithmic rate of omission, `-log (1 - ρ)`. -/
def logarithmicRate (ρ : ℝ) : ℝ := -Real.log (1 - ρ)
/-- Normalized covariance at a given annihilator intersection dimension. -/
def covarianceKernel (ρ : ℝ) (d : ℕ) : ℝ :=
  Real.exp (logarithmicRate ρ * (2 ^ d : ℝ)) - 1
/-- The nonnegative intersection dimensions up to `n - k`. -/
def pairRange (n k : ℕ) : Finset ℕ := Finset.range (n - k + 1)
/-- Natural floor of `n - k - 3 log₂ n` used to split the variance sum. -/
def varianceCutoff (n k : ℕ) : ℕ :=
  ⌊((n - k : ℕ) : ℝ) - 3 * log₂ (n : ℝ)⌋₊
/-- Low-dimension contribution to the quantitative error bound. -/
def lowError (n : ℕ) : ℝ := 4 * c₀ / (n : ℝ)
/-- High-dimension contribution to the quantitative error bound. -/
def highError (n k : ℕ) : ℝ :=
  (3 * log₂ (n : ℝ) + 1) *
    Real.exp (-Real.log 2 * (k : ℝ) * ((n - k : ℕ) : ℝ) / 4)
/-- Exponential bound on the normalized count in a high-dimension stratum. -/
def highPairWeight (n k : ℕ) : ℝ :=
  Real.exp (-Real.log 2 * (k : ℝ) * ((n - k : ℕ) : ℝ) / 2)
/-- Uniform covariance-kernel cap for intersection dimensions at most `n - k`. -/
def highKernelCap (n k : ℕ) (ρ : ℝ) : ℝ :=
  Real.exp (logarithmicRate ρ * (2 ^ (n - k) : ℝ))

/-- Fourier, moment, pair-counting and scalar estimates used by the finite
second-moment argument. -/
structure KernelObligations (n k : ℕ) (ρ : ℝ) : Prop where
  mass_nonnegative : ∀ Q : RowSet n, 0 ≤ sampleMass ρ Q
  mass_total : (∑ Q : RowSet n, sampleMass ρ Q) = 1
  indicator_nonzero : ∀ V : Grass n k, normalizedIndicator V.val ≠ 0
  indicator_sparse : ∀ V : Grass n k, Sparse (2 ^ k) (normalizedIndicator V.val)
  indicator_kernel : ∀ (V : Grass n k) (Q : RowSet n),
    Misses Q V.val → KernelOn Q (normalizedIndicator V.val)
  mean_positive : 0 < expectation ρ (witnessCount n k)
  variance_identity :
    expectation ρ (fun Q => (witnessCount n k Q - expectation ρ (witnessCount n k)) ^ 2) /
        expectation ρ (witnessCount n k) ^ 2 =
      ∑ d ∈ pairRange n k, pairWeight n k d * covarianceKernel ρ d
  weight_mass : (∑ d ∈ pairRange n k, pairWeight n k d) ≤ 1
  low_nonnegative : 0 ≤ lowError n
  low_kernel : ∀ d ∈ pairRange n k, d ≤ varianceCutoff n k →
    covarianceKernel ρ d ≤ lowError n
  high_weight : ∀ d ∈ pairRange n k, varianceCutoff n k < d →
    pairWeight n k d ≤ highPairWeight n k
  high_kernel : ∀ d ∈ pairRange n k,
    covarianceKernel ρ d ≤ highKernelCap n k ρ
  high_card :
    (((pairRange n k).filter fun d => varianceCutoff n k < d).card : ℝ) ≤
      3 * log₂ (n : ℝ) + 1
  high_arithmetic :
    (3 * log₂ (n : ℝ) + 1) * (highPairWeight n k * highKernelCap n k ρ) ≤
      highError n k
  error_le : quantitativeBound n k ≤ 1 / (n : ℝ)

theorem pairWeight_nonnegative (n k d : ℕ) : 0 ≤ pairWeight n k d := by
  unfold pairWeight
  positivity

theorem probability_mono {n : ℕ} (ρ : ℝ) (hw : ∀ Q : RowSet n, 0 ≤ sampleMass ρ Q)
    (E F : RowSet n → Prop) (hEF : ∀ Q, E Q → F Q) :
    probability ρ E ≤ probability ρ F := by
  unfold probability
  apply Finset.sum_le_sum
  intro Q _
  by_cases hE : E Q
  · simp [hE, hEF Q hE]
  · by_cases hF : F Q <;> simp [hE, hF, hw Q]

theorem witnessCount_nonnegative (n k : ℕ) (Q : RowSet n) :
    0 ≤ witnessCount n k Q := by
  apply Finset.sum_nonneg
  intro V _
  unfold witnessIndicator
  split <;> norm_num

theorem witnessCount_eq_zero_iff (n k : ℕ) (Q : RowSet n) :
    witnessCount n k Q = 0 ↔ ¬ MissedSubspace n k Q := by
  classical
  rw [witnessCount, Finset.sum_eq_zero_iff_of_nonneg]
  · simp [witnessIndicator, MissedSubspace]
  · intro V _
    unfold witnessIndicator
    split <;> norm_num

theorem missedSubspace_sparseKernel {n k : ℕ} {ρ : ℝ}
    (h : KernelObligations n k ρ) (Q : RowSet n) :
    MissedSubspace n k Q → SparseKernel (2 ^ k) Q := by
  rintro ⟨V, hV⟩
  exact ⟨normalizedIndicator V.val, h.indicator_nonzero V, h.indicator_sparse V,
    h.indicator_kernel V Q hV⟩

theorem normalized_variance_le_quantitativeBound {n k : ℕ} {ρ : ℝ}
    (h : KernelObligations n k ρ) :
    expectation ρ (fun Q => (witnessCount n k Q - expectation ρ (witnessCount n k)) ^ 2) /
        expectation ρ (witnessCount n k) ^ 2 ≤ quantitativeBound n k := by
  rw [h.variance_identity]
  have hsplit := ReductionLogic.weighted_split_bound (pairRange n k)
    (fun d => d ≤ varianceCutoff n k) (pairWeight n k) (covarianceKernel ρ)
    (lowError n) (highPairWeight n k * highKernelCap n k ρ)
    h.low_nonnegative (fun d _ => pairWeight_nonnegative n k d) h.weight_mass
    h.low_kernel (by
      intro d hd hhigh
      exact (mul_le_mul_of_nonneg_left (h.high_kernel d hd) (pairWeight_nonnegative n k d)).trans
        (mul_le_mul_of_nonneg_right (h.high_weight d hd (Nat.lt_of_not_ge hhigh))
          (le_of_lt (Real.exp_pos _))))
  have hcard :
      (((pairRange n k).filter fun d => ¬ d ≤ varianceCutoff n k).card : ℝ) *
          (highPairWeight n k * highKernelCap n k ρ) ≤ highError n k := by
    calc
      _ ≤ (3 * log₂ (n : ℝ) + 1) * (highPairWeight n k * highKernelCap n k ρ) := by
        apply mul_le_mul_of_nonneg_right
        · simpa only [not_le] using h.high_card
        · unfold highPairWeight highKernelCap
          positivity
      _ ≤ _ := h.high_arithmetic
  calc
    _ ≤ lowError n + highError n k := hsplit.trans (add_le_add le_rfl hcard)
    _ = quantitativeBound n k := rfl

/-- Finite kernel bounds and subspace witnesses from the intermediate estimates. -/
theorem finite_kernel_of_obligations {n k : ℕ} {ρ : ℝ}
    (h : KernelObligations n k ρ) :
    probability ρ (fun Q => witnessCount n k Q = 0) ≤ quantitativeBound n k ∧
    quantitativeBound n k ≤ 1 / (n : ℝ) ∧
    1 - 1 / (n : ℝ) ≤ probability ρ (MissedSubspace n k) ∧
    1 - 1 / (n : ℝ) ≤ probability ρ (SparseKernel (n := n) (2 ^ k)) ∧
    1 - 1 / (n : ℝ) ≤ probability ρ (fun Q : RowSet n => ∃ V : Grass n k,
      Misses Q V.val ∧ normalizedIndicator V.val ≠ 0 ∧
        Sparse (2 ^ k) (normalizedIndicator V.val) ∧ KernelOn Q (normalizedIndicator V.val)) := by
  have hzero : probability ρ (fun Q => witnessCount n k Q = 0) ≤ quantitativeBound n k := by
    exact (ReductionLogic.zero_event_le_second_moment (sampleMass ρ) (witnessCount n k)
      h.mass_nonnegative h.mean_positive).trans (normalized_variance_le_quantitativeBound h)
  have hcompl : probability ρ (MissedSubspace n k) +
      probability ρ (fun Q => witnessCount n k Q = 0) = 1 := by
    simp_rw [witnessCount_eq_zero_iff]
    unfold probability
    rw [← Finset.sum_add_distrib]
    calc
      _ = ∑ Q : RowSet n, sampleMass ρ Q := by
        apply Finset.sum_congr rfl
        intro Q _
        by_cases hQ : MissedSubspace n k Q <;> simp [hQ]
      _ = 1 := h.mass_total
  have hmiss : 1 - 1 / (n : ℝ) ≤ probability ρ (MissedSubspace n k) := by
    linarith [hzero.trans h.error_le]
  refine ⟨hzero, h.error_le, hmiss, ?_, ?_⟩
  · exact hmiss.trans (probability_mono ρ h.mass_nonnegative
      (MissedSubspace n k) (SparseKernel (n := n) (2 ^ k)) (missedSubspace_sparseKernel h))
  · exact hmiss.trans (probability_mono ρ h.mass_nonnegative
      (MissedSubspace n k)
      (fun Q : RowSet n => ∃ V : Grass n k, Misses Q V.val ∧
        normalizedIndicator V.val ≠ 0 ∧ Sparse (2 ^ k) (normalizedIndicator V.val) ∧
          KernelOn Q (normalizedIndicator V.val)) (by
        rintro Q ⟨V, hV⟩
        exact ⟨V, hV, h.indicator_nonzero V, h.indicator_sparse V, h.indicator_kernel V Q hV⟩))

theorem sparse_zero {n K : ℕ} : Sparse K (0 : Signal n) := by
  simp [Sparse, signalSupport]

private theorem walsh_zero_reduction {n : ℕ} : walsh (0 : Signal n) = 0 := by
  ext a
  simp [walsh]

theorem squaredEnergy_positive {n : ℕ} {f : Signal n} (hf : f ≠ 0) :
    0 < squaredEnergy f := by
  have hex : ∃ x, f x ≠ 0 := by
    by_contra h
    apply hf
    funext x
    by_contra hx
    exact h ⟨x, hx⟩
  obtain ⟨x, hx⟩ := hex
  exact Finset.sum_pos' (fun i _ => sq_nonneg (f i))
    ⟨x, Finset.mem_univ x, sq_pos_of_ne_zero hx⟩

theorem sparseKernel_not_recovery {n K : ℕ} {Q : RowSet n}
    (h : SparseKernel K Q) : ¬ Recovery K Q := by
  rintro hrec
  obtain ⟨f, hf, hs, hk⟩ := h
  exact hf (hrec f 0 hs sparse_zero (by simpa [walsh_zero_reduction, KernelOn] using hk))

theorem sparseKernel_not_rip {n K : ℕ} {Q : RowSet n} {δ : ℝ}
    (hδ : δ < 1) (h : SparseKernel K Q) : ¬ RIP K δ Q := by
  rintro ⟨a, ha⟩
  obtain ⟨f, hf, hs, hk⟩ := h
  have he : rowEnergy Q f = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    simp [hk x hx]
  have hlo := (ha f hs).1
  rw [he, mul_zero] at hlo
  have hpos := mul_pos (sub_pos.mpr hδ) (squaredEnergy_positive hf)
  linarith

theorem decoder_implies_recovery {n K : ℕ} {Q : RowSet n}
    (h : UniformDecoder K Q) : Recovery K Q := by
  obtain ⟨D, hD⟩ := h
  intro f g hf hg heq
  have hfg : restrictedWalsh Q f = restrictedWalsh Q g := by
    funext a
    exact heq a.val a.property
  calc
    f = D (restrictedWalsh Q f) := (hD f hf).symm
    _ = D (restrictedWalsh Q g) := congrArg D hfg
    _ = g := hD g hg

theorem sparseKernel_not_decoder {n K : ℕ} {Q : RowSet n}
    (h : SparseKernel K Q) : ¬ UniformDecoder K Q := by
  exact fun hD => sparseKernel_not_recovery h (decoder_implies_recovery hD)

theorem sparseKernel_not_complexRIP {n K : ℕ} {Q : RowSet n} {δ : ℝ}
    (hδ : δ < 1) (h : SparseKernel K Q) : ¬ ComplexRIP K δ Q := by
  exact fun hI => sparseKernel_not_rip hδ h (complexRIP_implies_rip K δ Q hI)

theorem finite_recovery_of_obligations {n k : ℕ} {ρ δ : ℝ}
    (h : KernelObligations n k ρ) (hδ : δ < 1) :
    probability ρ (Recovery (n := n) (2 ^ k)) ≤ 1 / (n : ℝ) ∧
      probability ρ (RIP (n := n) (2 ^ k) δ) ≤ 1 / (n : ℝ) := by
  have hzero := (finite_kernel_of_obligations h).1.trans h.error_le
  have hrec : ∀ Q : RowSet n, Recovery (2 ^ k) Q → witnessCount n k Q = 0 := by
    intro Q hQ
    apply (witnessCount_eq_zero_iff n k Q).mpr
    intro hmiss
    exact sparseKernel_not_recovery (missedSubspace_sparseKernel h Q hmiss) hQ
  have hrip : ∀ Q : RowSet n, RIP (2 ^ k) δ Q → witnessCount n k Q = 0 := by
    intro Q hQ
    apply (witnessCount_eq_zero_iff n k Q).mpr
    intro hmiss
    exact sparseKernel_not_rip hδ (missedSubspace_sparseKernel h Q hmiss) hQ
  exact ⟨(probability_mono ρ h.mass_nonnegative
      (Recovery (n := n) (2 ^ k)) _ hrec).trans hzero,
    (probability_mono ρ h.mass_nonnegative
      (RIP (n := n) (2 ^ k) δ) _ hrip).trans hzero⟩

theorem finite_decoder_complex_of_obligations {n k : ℕ} {ρ δ : ℝ}
    (h : KernelObligations n k ρ) (hδ : δ < 1) :
    probability ρ (UniformDecoder (n := n) (2 ^ k)) ≤ 1 / (n : ℝ) ∧
      probability ρ (ComplexRIP (n := n) (2 ^ k) δ) ≤ 1 / (n : ℝ) := by
  have hfinite := finite_recovery_of_obligations h hδ
  exact ⟨(probability_mono ρ h.mass_nonnegative
      (UniformDecoder (n := n) (2 ^ k)) (Recovery (n := n) (2 ^ k))
      (fun _ hD => decoder_implies_recovery hD)).trans hfinite.1,
    (probability_mono ρ h.mass_nonnegative
      (ComplexRIP (n := n) (2 ^ k) δ) (RIP (n := n) (2 ^ k) δ)
      (fun Q hI => complexRIP_implies_rip (2 ^ k) δ Q hI)).trans hfinite.2⟩

/-- Logarithmic threshold identities and the exact expected row count. -/
structure SamplingIdentities : Prop where
  logarithmic_threshold : ∀ n k : ℕ, k ≤ n →
    c₀ * (2 ^ k : ℝ) / (2 ^ n : ℝ) * log₂ (2 ^ k : ℝ) *
        log₂ ((2 ^ n : ℝ) / (2 ^ k : ℝ)) = samplingThreshold n k
  recovery_threshold : ∀ n k : ℕ, k ≤ n →
    recoveryThreshold n k = (2 ^ n : ℝ) * samplingThreshold n k
  expected_rows : ∀ (n : ℕ) (ρ : ℝ), 0 ≤ ρ → ρ ≤ 1 →
    expectedRows n ρ = (2 ^ n : ℝ) * ρ

theorem sampling_bound_of_expected_rows {n k : ℕ} {ρ : ℝ}
    (h : SamplingIdentities) (hkn : k ≤ n) (hρ : 0 ≤ ρ) (hρ₁ : ρ ≤ 1)
    (hq : expectedRows n ρ ≤ recoveryThreshold n k) :
    ρ ≤ samplingThreshold n k := by
  rw [h.expected_rows n ρ hρ hρ₁, h.recovery_threshold n k hkn] at hq
  exact le_of_mul_le_mul_left hq (by positivity : 0 < (2 ^ n : ℝ))

/-- The intermediate estimates for every admissible finite sampling parameter. -/
def KernelObligationFamily : Prop :=
  ∀ (n k : ℕ) (ρ : ℝ), dimensionsAdmissible n k → 0 ≤ ρ →
    ρ ≤ samplingThreshold n k → KernelObligations n k ρ

theorem uniform_kernel_of_obligations (h : KernelObligationFamily)
    (hids : SamplingIdentities) :
    ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ (n k : ℕ) (ρ : ℝ), N₀ ≤ n →
      dimensionsAdmissible n k → 0 ≤ ρ →
      ρ ≤ c₀ * (2 ^ k : ℝ) / (2 ^ n : ℝ) * log₂ (2 ^ k : ℝ) *
        log₂ ((2 ^ n : ℝ) / (2 ^ k : ℝ)) →
      1 - ε < probability ρ (SparseKernel (n := n) (2 ^ k)) := by
  intro ε hε
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (1 / ε)
  refine ⟨N₀, ?_⟩
  intro n k ρ hn hdim hρ hbound
  rw [hids.logarithmic_threshold n k hdim.2.1] at hbound
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 256) hdim.1)
  have hnlarge : 1 / ε < (n : ℝ) := hN₀.trans_le (Nat.cast_le.mpr hn)
  have hsmall : 1 / (n : ℝ) < ε := by
    apply (div_lt_iff₀ hnpos).mpr
    have hmul := (div_lt_iff₀ hε).mp hnlarge
    nlinarith
  have hfinite := (finite_kernel_of_obligations (h n k ρ hdim hρ hbound)).2.2.2.1
  linarith

theorem finite_recovery_principal_of_obligations
    (h : KernelObligationFamily) (hids : SamplingIdentities)
    (n k : ℕ) (ρ δ : ℝ) (hdim : dimensionsAdmissible n k)
    (hρ : 0 ≤ ρ) (hρ₁ : ρ ≤ 1) (_hδ₀ : 0 < δ) (hδ₁ : δ < 1) :
    (expectedRows n ρ ≤ recoveryThreshold n k →
      probability ρ (Recovery (n := n) (2 ^ k)) ≤ 1 / (n : ℝ) ∧
      probability ρ (RIP (n := n) (2 ^ k) δ) ≤ 1 / (n : ℝ)) ∧
    ((1 / (n : ℝ) < probability ρ (Recovery (n := n) (2 ^ k)) ∨
      1 / (n : ℝ) < probability ρ (RIP (n := n) (2 ^ k) δ)) →
      recoveryThreshold n k < expectedRows n ρ) := by
  have hb : expectedRows n ρ ≤ recoveryThreshold n k →
      probability ρ (Recovery (n := n) (2 ^ k)) ≤ 1 / (n : ℝ) ∧
      probability ρ (RIP (n := n) (2 ^ k) δ) ≤ 1 / (n : ℝ) := by
    intro hq
    exact finite_recovery_of_obligations
      (h n k ρ hdim hρ (sampling_bound_of_expected_rows hids hdim.2.1 hρ hρ₁ hq)) hδ₁
  refine ⟨hb, ?_⟩
  intro hsuccess
  by_contra hnot
  have hf := hb (le_of_not_gt hnot)
  rcases hsuccess with hr | hi
  · exact (not_lt_of_ge hf.1) hr
  · exact (not_lt_of_ge hf.2) hi

/-- Explicit `Ω` quantifiers, with arbitrary dimension sequences, eventual
admissibility, and one positive eventual lower bound on either success event. -/
theorem necessary_sampling_of_obligations
    (h : KernelObligationFamily) (hids : SamplingIdentities)
    (n k : ℕ → ℕ) (ρ : ℕ → ℝ) (δ : ℝ) (hδ₀ : 0 < δ) (hδ₁ : δ < 1)
    (hn : ∀ N : ℕ, ∃ J : ℕ, ∀ j ≥ J, N ≤ n j)
    (hadm : ∃ J : ℕ, ∀ j ≥ J,
      dimensionsAdmissible (n j) (k j) ∧ 0 ≤ ρ j ∧ ρ j ≤ 1)
    (hsuccess : ∃ η : ℝ, 0 < η ∧
      ((∃ J : ℕ, ∀ j ≥ J, η ≤ probability (ρ j) (Recovery (n := n j) (2 ^ k j))) ∨
       (∃ J : ℕ, ∀ j ≥ J, η ≤ probability (ρ j) (RIP (n := n j) (2 ^ k j) δ)))) :
    ∃ J : ℕ, ∀ j ≥ J, recoveryThreshold (n j) (k j) < expectedRows (n j) (ρ j) := by
  obtain ⟨η, hη, hsuccess⟩ := hsuccess
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / η)
  obtain ⟨Jn, hJn⟩ := hn N
  obtain ⟨Ja, hJa⟩ := hadm
  have hsmall : ∀ j ≥ Jn, 0 < (n j : ℝ) → 1 / (n j : ℝ) < η := by
    intro j hj hnj
    have hlarge : 1 / η < (n j : ℝ) := hN.trans_le (Nat.cast_le.mpr (hJn j hj))
    apply (div_lt_iff₀ hnj).mpr
    have hmul := (div_lt_iff₀ hη).mp hlarge
    nlinarith
  rcases hsuccess with ⟨Js, hJs⟩ | ⟨Js, hJs⟩
  · refine ⟨max Jn (max Ja Js), ?_⟩
    intro j hj
    have hjn : Jn ≤ j := le_trans (le_max_left _ _) hj
    have hja : Ja ≤ j := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hj
    have hjs : Js ≤ j := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hj
    obtain ⟨hdim, hρ, hρ₁⟩ := hJa j hja
    have hnj : 0 < (n j : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 256) hdim.1)
    apply (finite_recovery_principal_of_obligations h hids (n j) (k j) (ρ j) δ
      hdim hρ hρ₁ hδ₀ hδ₁).2
    exact Or.inl ((hsmall j hjn hnj).trans_le (hJs j hjs))
  · refine ⟨max Jn (max Ja Js), ?_⟩
    intro j hj
    have hjn : Jn ≤ j := le_trans (le_max_left _ _) hj
    have hja : Ja ≤ j := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hj
    have hjs : Js ≤ j := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hj
    obtain ⟨hdim, hρ, hρ₁⟩ := hJa j hja
    have hnj : 0 < (n j : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 256) hdim.1)
    apply (finite_recovery_principal_of_obligations h hids (n j) (k j) (ρ j) δ
      hdim hρ hρ₁ hδ₀ hδ₁).2
    exact Or.inr ((hsmall j hjn hnj).trans_le (hJs j hjs))

end Paper
