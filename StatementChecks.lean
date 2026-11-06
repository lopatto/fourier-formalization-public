/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

import Solution

/-! Independent expected types and semantic checks for the principal results
and critical prerequisites. This module is outside Solution's import closure. -/

public section

noncomputable section

open scoped BigOperators
open Paper
attribute [local instance] Classical.propDecidable

namespace StatementChecks

/-! The five principal contracts are written independently, using
the concrete Paper models. -/

example : ∀ (n k : ℕ) (ρ : ℝ),
    dimensionsAdmissible n k → 0 ≤ ρ → ρ ≤ samplingThreshold n k →
    probability ρ (fun Q => witnessCount n k Q = 0) ≤ quantitativeBound n k ∧
    quantitativeBound n k ≤ 1 / (n : ℝ) ∧
    1 - 1 / (n : ℝ) ≤ probability ρ (MissedSubspace n k) ∧
    1 - 1 / (n : ℝ) ≤ probability ρ (SparseKernel (n := n) (2 ^ k)) ∧
    1 - 1 / (n : ℝ) ≤ probability ρ (fun Q : RowSet n => ∃ V : Grass n k,
      Misses Q V.val ∧ normalizedIndicator V.val ≠ 0 ∧
        Sparse (2 ^ k) (normalizedIndicator V.val) ∧
          KernelOn Q (normalizedIndicator V.val)) := by
  exact @Paper.finiteKernel

example : ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ (n k : ℕ) (ρ : ℝ), N₀ ≤ n →
    dimensionsAdmissible n k → 0 ≤ ρ →
    ρ ≤ c₀ * (2 ^ k : ℝ) / (2 ^ n : ℝ) * log₂ (2 ^ k : ℝ) *
      log₂ ((2 ^ n : ℝ) / (2 ^ k : ℝ)) →
    1 - ε < probability ρ (SparseKernel (n := n) (2 ^ k)) := by
  exact @Paper.uniformKernel

example : ∀ (n k : ℕ) (ρ δ : ℝ),
    dimensionsAdmissible n k → 0 ≤ ρ → ρ ≤ 1 → 0 < δ → δ < 1 →
    (expectedRows n ρ ≤ recoveryThreshold n k →
      probability ρ (Recovery (n := n) (2 ^ k)) ≤ 1 / (n : ℝ) ∧
      probability ρ (RIP (n := n) (2 ^ k) δ) ≤ 1 / (n : ℝ)) ∧
    ((1 / (n : ℝ) < probability ρ (Recovery (n := n) (2 ^ k)) ∨
      1 / (n : ℝ) < probability ρ (RIP (n := n) (2 ^ k) δ)) →
      recoveryThreshold n k < expectedRows n ρ) := by
  exact @Paper.finiteRecovery

example : ∀ (n k : ℕ → ℕ) (ρ : ℕ → ℝ) (δ : ℝ), 0 < δ → δ < 1 →
    (∀ N : ℕ, ∃ J : ℕ, ∀ j ≥ J, N ≤ n j) →
    (∃ J : ℕ, ∀ j ≥ J,
      dimensionsAdmissible (n j) (k j) ∧ 0 ≤ ρ j ∧ ρ j ≤ 1) →
    (∃ η : ℝ, 0 < η ∧
      ((∃ J : ℕ, ∀ j ≥ J,
        η ≤ probability (ρ j) (Recovery (n := n j) (2 ^ k j))) ∨
       (∃ J : ℕ, ∀ j ≥ J,
        η ≤ probability (ρ j) (RIP (n := n j) (2 ^ k j) δ)))) →
    ∃ J : ℕ, ∀ j ≥ J,
      recoveryThreshold (n j) (k j) < expectedRows (n j) (ρ j) := by
  exact @Paper.necessarySampling

example :
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
  exact @Paper.boundedOrthonormalExample

/-! Checked prerequisite types and essential definition meanings. These
property checks allow implementation changes that preserve the contract. -/

example (n d : ℕ) (hd : d ≤ n) :
    Nat.card {V : Submodule (ZMod 2) (Fin n → ZMod 2) //
        Module.finrank (ZMod 2) V = d} *
      ∏ i : Fin d, (2 ^ d - 2 ^ (i : ℕ)) =
      ∏ i : Fin d, (2 ^ n - 2 ^ (i : ℕ)) := by
  simpa only [ZMod.card] using
    (SubspaceConvolution.card_finrank_eq_mul_prod_fin
      (K := ZMod 2) (n := n) (j := d) hd)

example (n : ℕ) (x y : Fin n → ZMod 2) :
    Paper.dotProduct n x y = ∑ i, x i * y i := by
  exact Paper.dotProduct_apply n x y

example {n : ℕ} (V : Submodule (ZMod 2) (Fin n → ZMod 2))
    (a : Fin n → ZMod 2) :
    a ∈ annihilator V ↔ ∀ v ∈ V, (∑ i, a i * v i) = 0 := by
  simpa only [Paper.dotProduct_apply] using Paper.mem_annihilator_iff V a

example : ∀ {n : ℕ} (V : Submodule (ZMod 2) (Fin n → ZMod 2)),
    Module.finrank (ZMod 2) (annihilator V) = n - Module.finrank (ZMod 2) V := by
  exact @Paper.annihilator_finrank

example : ∀ {n : ℕ} (V : Submodule (ZMod 2) (Fin n → ZMod 2)),
    annihilator (annihilator V) = V := by
  exact @Paper.annihilator_annihilator

example : ∀ {n : ℕ} (V : Submodule (ZMod 2) (Fin n → ZMod 2)),
    Nat.card V = 2 ^ Module.finrank (ZMod 2) V := by
  exact @Paper.subspace_card

example {n : ℕ} (f : (Fin n → ZMod 2) → ℝ) (x : Fin n → ZMod 2) :
    x ∈ signalSupport f ↔ f x ≠ 0 := by
  exact Paper.mem_signalSupport_iff f x

example {n : ℕ} (f : (Fin n → ZMod 2) → ℝ) :
    squaredEnergy f = ∑ x, |f x| ^ 2 := by
  exact Paper.squaredEnergy_eq_sum_abs_sq f

example {n : ℕ} (f : Signal n) (a : BinarySpace n) :
    walsh f a = 1 / Real.sqrt (2 ^ n : ℝ) *
      ∑ x, f x * (if (∑ i, a i * x i) = 0 then 1 else -1) := by
  simp only [walsh, character, Paper.dotProduct_apply, one_div]

example {n : ℕ} (V : Submodule (ZMod 2) (BinarySpace n))
    (x : BinarySpace n) (hx : x ∈ V) :
    normalizedIndicator V x = 1 / Real.sqrt (Nat.card V : ℝ) := by
  simp [normalizedIndicator, hx, one_div]

example {n : ℕ} (V : Submodule (ZMod 2) (BinarySpace n))
    (x : BinarySpace n) (hx : x ∉ V) : normalizedIndicator V x = 0 := by
  simp [normalizedIndicator, hx]

example {n : ℕ} (ρ : ℝ) (ω : BinarySpace n → Bool) :
    sampleMass ρ (Paper.bitRowsEquiv n ω) =
      ∏ a : BinarySpace n, if ω a = true then ρ else 1 - ρ := by
  exact Paper.sampleMass_bitRowsEquiv ρ ω

example (n : ℕ) (ρ : ℝ) : (∑ Q : RowSet n, sampleMass ρ Q) = 1 := by
  exact Paper.sampleMass_sum n ρ

example {n : ℕ} (ρ : ℝ) (hρ : 0 ≤ ρ) (hρ₁ : ρ ≤ 1) (Q : RowSet n) :
    0 ≤ sampleMass ρ Q := by
  exact Paper.sampleMass_nonneg ρ hρ hρ₁ Q

example {n : ℕ} (Q : RowSet n) : sampleMass 0 Q = if Q = ∅ then 1 else 0 := by
  exact Paper.sampleMass_zero Q

example {n : ℕ} (Q : RowSet n) :
    sampleMass 1 Q = if Q = Finset.univ then 1 else 0 := by
  exact Paper.sampleMass_one Q

example {n : ℕ} (ρ : ℝ) (E : RowSet n → Prop) :
    probability ρ E = ∑ Q : RowSet n,
      if E Q then (∏ a : BinarySpace n, if a ∈ Q then ρ else 1 - ρ) else 0 := by
  simp only [probability, sampleMass]

example (n : ℕ) (ρ : ℝ) :
    expectedRows n ρ = ∑ Q : RowSet n,
      (∏ a : BinarySpace n, if a ∈ Q then ρ else 1 - ρ) * (Q.card : ℝ) := by
  simp only [expectedRows, expectation, sampleMass]

example (n k : ℕ) (Q : RowSet n) :
    witnessCount n k Q = ∑ V : Grass n k,
      if (∀ a ∈ Q, a ∉ annihilator V.val) then (1 : ℝ) else 0 := by
  unfold witnessCount
  apply Finset.sum_congr rfl
  intro V _
  unfold witnessIndicator Misses
  exact congrArg (fun d : Decidable (∀ a ∈ Q, a ∉ annihilator V.val) =>
    @ite ℝ _ d 1 0) (Subsingleton.elim _ _)

example (n k : ℕ) : dimensionsAdmissible n k ↔
    256 ≤ n ∧ k ≤ n ∧
      12 * (Real.log (n : ℝ) / Real.log 2) ≤ min (k : ℝ) ((n : ℝ) - (k : ℝ)) := by
  constructor <;> intro h <;> exact h

example : c₀ = Real.log 2 / 8 := by
  simp only [c₀]

example (x : ℝ) : log₂ x = Real.log x / Real.log 2 := by
  simp only [log₂]

example (n k : ℕ) : samplingThreshold n k =
    (Real.log 2 / 8) * (2 ^ k : ℝ) / (2 ^ n : ℝ) *
      (k : ℝ) * ((n - k : ℕ) : ℝ) := by
  simp only [samplingThreshold, c₀]

example (n k : ℕ) : quantitativeBound n k =
    4 * (Real.log 2 / 8) / (n : ℝ) +
      (3 * (Real.log (n : ℝ) / Real.log 2) + 1) *
        Real.exp (-Real.log 2 * (k : ℝ) * ((n - k : ℕ) : ℝ) / 4) := by
  simp only [quantitativeBound, c₀, log₂]

example (n k : ℕ) : recoveryThreshold n k =
    (Real.log 2 / 8) * (2 ^ k : ℝ) *
      (Real.log (2 ^ k : ℝ) / Real.log 2) *
        (Real.log ((2 ^ n : ℝ) / (2 ^ k : ℝ)) / Real.log 2) := by
  simp only [recoveryThreshold, c₀, log₂]

example {n : ℕ} (K : ℕ) (Q : RowSet n) :
    SparseKernel K Q ↔ ∃ f : Signal n, f ≠ 0 ∧
      (Finset.univ.filter (fun x => f x ≠ 0)).card ≤ K ∧
        ∀ a ∈ Q, walsh f a = 0 := by
  constructor
  · rintro ⟨f, hf, hs, hk⟩
    exact ⟨f, hf, hs, hk⟩
  · rintro ⟨f, hf, hs, hk⟩
    exact ⟨f, hf, hs, hk⟩

example (n k : ℕ) (Q : RowSet n) :
    witnessCount n k Q = 0 ↔ ¬ ∃ V : Grass n k, Misses Q V.val := by
  exact Paper.witnessCount_eq_zero_iff n k Q

example {n : ℕ} (K : ℕ) (Q : RowSet n) :
    Recovery K Q ↔ ∀ f g : Signal n,
      (Finset.univ.filter (fun x => f x ≠ 0)).card ≤ K →
      (Finset.univ.filter (fun x => g x ≠ 0)).card ≤ K →
      (∀ a ∈ Q, walsh f a = walsh g a) → f = g := by
  constructor
  · intro h f g hf hg heq
    exact h f g hf hg heq
  · intro h f g hf hg heq
    exact h f g hf hg heq

example {n : ℕ} (K : ℕ) (δ : ℝ) (Q : RowSet n) :
    RIP K δ Q ↔ ∃ a : ℝ, ∀ f : Signal n,
      (Finset.univ.filter (fun x => f x ≠ 0)).card ≤ K →
      (1 - δ) * (∑ x, (f x) ^ 2) ≤ a ^ 2 * (∑ x ∈ Q, (walsh f x) ^ 2) ∧
      a ^ 2 * (∑ x ∈ Q, (walsh f x) ^ 2) ≤ (1 + δ) * (∑ x, (f x) ^ 2) := by
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, fun f hf => ha f hf⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, fun f hf => ha f hf⟩

example : ∀ {n : ℕ} (K : ℕ) (δ : ℝ) (Q : RowSet n),
    ComplexRIP K δ Q → RIP K δ Q := by
  exact @Paper.complexRIP_implies_rip

example {n : ℕ} (K : ℕ) (δ : ℝ) (Q : RowSet n) :
    ComplexRIP K δ Q ↔ ∃ a : ℂ, ∀ f : ComplexSignal n,
      (Finset.univ.filter (fun x => f x ≠ 0)).card ≤ K →
      (1 - δ) * (∑ x, ‖f x‖ ^ 2) ≤
        ‖a‖ ^ 2 * (∑ x ∈ Q, ‖complexWalsh f x‖ ^ 2) ∧
      ‖a‖ ^ 2 * (∑ x ∈ Q, ‖complexWalsh f x‖ ^ 2) ≤
        (1 + δ) * (∑ x, ‖f x‖ ^ 2) := by
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, fun f hf => ha f hf⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, fun f hf => ha f hf⟩

example : ∀ {n K : ℕ} {Q : RowSet n}, UniformDecoder K Q → Recovery K Q := by
  exact @Paper.decoder_implies_recovery

/-! The reduction checks have additional *explicit intermediate proof
parameters*. KernelObligations consists of Fourier, moment, pair-counting and
scalar estimates; SamplingIdentities contains algebraic sampling/log bridges.
These are conditional contracts, not extra hypotheses on final principals. -/

example {n k : ℕ} {ρ : ℝ} (h : KernelObligations n k ρ) :
    (∑ Q : RowSet n, sampleMass ρ Q *
      (witnessCount n k Q - ∑ R : RowSet n, sampleMass ρ R * witnessCount n k R) ^ 2) /
        (∑ Q : RowSet n, sampleMass ρ Q * witnessCount n k Q) ^ 2 =
      ∑ d ∈ Finset.range (n - k + 1),
        (Nat.card {UV : Grass n k × Grass n k //
          Module.finrank (ZMod 2) ↥(annihilator UV.1.val ⊓ annihilator UV.2.val) = d} : ℝ) /
          (Nat.card (Grass n k) : ℝ) ^ 2 *
            (Real.exp (-Real.log (1 - ρ) * (2 ^ d : ℝ)) - 1) := by
  exact h.variance_identity

example {n k : ℕ} {ρ : ℝ} (h : KernelObligations n k ρ) :
    ∀ d ∈ Finset.range (n - k + 1),
      ⌊((n - k : ℕ) : ℝ) - 3 * log₂ (n : ℝ)⌋₊ < d →
      (Nat.card {UV : Grass n k × Grass n k //
        Module.finrank (ZMod 2) ↥(annihilator UV.1.val ⊓ annihilator UV.2.val) = d} : ℝ) /
        (Nat.card (Grass n k) : ℝ) ^ 2 ≤
          Real.exp (-Real.log 2 * (k : ℝ) * ((n - k : ℕ) : ℝ) / 2) := by
  exact h.high_weight

example (h : SamplingIdentities) :
    ∀ (n : ℕ) (ρ : ℝ), 0 ≤ ρ → ρ ≤ 1 →
      expectedRows n ρ = (2 ^ n : ℝ) * ρ := by
  exact h.expected_rows

example (h : SamplingIdentities) : ∀ n k : ℕ, k ≤ n →
    recoveryThreshold n k = (2 ^ n : ℝ) * samplingThreshold n k := by
  exact h.recovery_threshold

example (h : SamplingIdentities) : ∀ n k : ℕ, k ≤ n →
    c₀ * (2 ^ k : ℝ) / (2 ^ n : ℝ) * log₂ (2 ^ k : ℝ) *
      log₂ ((2 ^ n : ℝ) / (2 ^ k : ℝ)) = samplingThreshold n k := by
  exact h.logarithmic_threshold

example {n : ℕ} (h : CharacterObligations n) : ∀ a : BinarySpace n,
    (∑ x : BinarySpace n, character a x) = if a = 0 then (2 ^ n : ℝ) else 0 := by
  exact h.cancellation

example {n : ℕ} (h : CharacterObligations n) : ∀ a b x : BinarySpace n,
    character a x * character b x = character (a - b) x := by
  exact h.product

example : ∀ {n k : ℕ} {ρ : ℝ}, KernelObligations n k ρ →
    probability ρ (fun Q => witnessCount n k Q = 0) ≤ quantitativeBound n k ∧
    quantitativeBound n k ≤ 1 / (n : ℝ) ∧
    1 - 1 / (n : ℝ) ≤ probability ρ (MissedSubspace n k) ∧
    1 - 1 / (n : ℝ) ≤ probability ρ (SparseKernel (n := n) (2 ^ k)) ∧
    1 - 1 / (n : ℝ) ≤ probability ρ (fun Q : RowSet n => ∃ V : Grass n k,
      Misses Q V.val ∧ normalizedIndicator V.val ≠ 0 ∧
        Sparse (2 ^ k) (normalizedIndicator V.val) ∧
          KernelOn Q (normalizedIndicator V.val)) := by
  exact @Paper.finite_kernel_of_obligations

example : KernelObligationFamily → SamplingIdentities →
    ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ (n k : ℕ) (ρ : ℝ), N₀ ≤ n →
      dimensionsAdmissible n k → 0 ≤ ρ →
      ρ ≤ c₀ * (2 ^ k : ℝ) / (2 ^ n : ℝ) * log₂ (2 ^ k : ℝ) *
        log₂ ((2 ^ n : ℝ) / (2 ^ k : ℝ)) →
      1 - ε < probability ρ (SparseKernel (n := n) (2 ^ k)) := by
  exact @Paper.uniform_kernel_of_obligations

example : KernelObligationFamily → SamplingIdentities →
    ∀ (n k : ℕ) (ρ δ : ℝ), dimensionsAdmissible n k →
      0 ≤ ρ → ρ ≤ 1 → 0 < δ → δ < 1 →
      (expectedRows n ρ ≤ recoveryThreshold n k →
        probability ρ (Recovery (n := n) (2 ^ k)) ≤ 1 / (n : ℝ) ∧
        probability ρ (RIP (n := n) (2 ^ k) δ) ≤ 1 / (n : ℝ)) ∧
      ((1 / (n : ℝ) < probability ρ (Recovery (n := n) (2 ^ k)) ∨
        1 / (n : ℝ) < probability ρ (RIP (n := n) (2 ^ k) δ)) →
        recoveryThreshold n k < expectedRows n ρ) := by
  exact @Paper.finite_recovery_principal_of_obligations

example : KernelObligationFamily → SamplingIdentities →
    ∀ (n k : ℕ → ℕ) (ρ : ℕ → ℝ) (δ : ℝ), 0 < δ → δ < 1 →
      (∀ N : ℕ, ∃ J : ℕ, ∀ j ≥ J, N ≤ n j) →
      (∃ J : ℕ, ∀ j ≥ J,
        dimensionsAdmissible (n j) (k j) ∧ 0 ≤ ρ j ∧ ρ j ≤ 1) →
      (∃ η : ℝ, 0 < η ∧
        ((∃ J : ℕ, ∀ j ≥ J,
          η ≤ probability (ρ j) (Recovery (n := n j) (2 ^ k j))) ∨
         (∃ J : ℕ, ∀ j ≥ J,
          η ≤ probability (ρ j) (RIP (n := n j) (2 ^ k j) δ)))) →
      ∃ J : ℕ, ∀ j ≥ J,
        recoveryThreshold (n j) (k j) < expectedRows (n j) (ρ j) := by
  exact @Paper.necessary_sampling_of_obligations

example : (∀ n : ℕ, CharacterObligations n) → KernelObligationFamily → SamplingIdentities →
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
  exact @Paper.bounded_orthonormal_example_of_obligations

/-! Newly discharged prerequisites, checked independently of the obligation
records. These examples have no intermediate proof parameters. -/

example (n k : ℕ) (hk : k ≤ n) :
    c₀ * (2 ^ k : ℝ) / (2 ^ n : ℝ) * log₂ (2 ^ k : ℝ) *
      log₂ ((2 ^ n : ℝ) / (2 ^ k : ℝ)) = samplingThreshold n k := by
  exact Paper.logarithmic_threshold n k hk

example (n k : ℕ) (hk : k ≤ n) :
    recoveryThreshold n k = (2 ^ n : ℝ) * samplingThreshold n k := by
  exact Paper.recovery_threshold n k hk

example (n : ℕ) (ρ : ℝ) : expectedRows n ρ = (2 ^ n : ℝ) * ρ := by
  exact Paper.expectedRows_eq n ρ

example {n : ℕ} (ρ : ℝ) (A : Finset (Fin n → ZMod 2)) :
    probability ρ (fun Q : RowSet n => ∀ a ∈ A, a ∉ Q) = (1 - ρ) ^ A.card := by
  exact Paper.probability_avoidance ρ A

example {n : ℕ} (ρ : ℝ) (A B : Finset (Fin n → ZMod 2)) :
    probability ρ (fun Q : RowSet n =>
      (∀ a ∈ A, a ∉ Q) ∧ (∀ b ∈ B, b ∉ Q)) = (1 - ρ) ^ (A ∪ B).card := by
  exact Paper.probability_joint_avoidance ρ A B

example {n : ℕ} (a b x : Fin n → ZMod 2) :
    character a x * character b x = character (a - b) x := by
  exact Paper.character_product a b x

example {n : ℕ} (V : Submodule (ZMod 2) (Fin n → ZMod 2))
    (a : Fin n → ZMod 2) :
    (∑ x : V, character a x) = if a ∈ annihilator V then (Nat.card V : ℝ) else 0 := by
  exact Paper.character_sum_subspace V a

example {n : ℕ} (V : Submodule (ZMod 2) (Fin n → ZMod 2)) :
    Nat.card V * Nat.card (annihilator V) = 2 ^ n := by
  exact Paper.subspace_card_mul_annihilator_card V


/-! Exact Fourier witnesses and orthogonality, with no obligation parameters. -/
example {n : ℕ} (V : Submodule (ZMod 2) (Fin n → ZMod 2)) :
    walsh (normalizedIndicator V) = normalizedIndicator (annihilator V) := by
  exact Paper.normalizedIndicator_walsh V

example {n : ℕ} (V : Submodule (ZMod 2) (Fin n → ZMod 2)) :
    squaredEnergy (normalizedIndicator V) = 1 := by
  exact Paper.normalizedIndicator_energy V

example {n : ℕ} (V : Submodule (ZMod 2) (Fin n → ZMod 2)) :
    (signalSupport (normalizedIndicator V)).card = 2 ^ Module.finrank (ZMod 2) V := by
  exact Paper.normalizedIndicator_support_card_eq_pow V

example {n : ℕ} (V : Submodule (ZMod 2) (Fin n → ZMod 2)) (Q : RowSet n) :
    KernelOn Q (normalizedIndicator V) ↔ Misses Q V := by
  exact Paper.normalizedIndicator_kernel_iff V Q

example (n : ℕ) (a b : Fin n → ZMod 2) :
    (∑ x : Fin n → ZMod 2,
      ((Real.sqrt (2 ^ n : ℝ))⁻¹ * character x a) *
        ((Real.sqrt (2 ^ n : ℝ))⁻¹ * character x b)) = if a = b then 1 else 0 := by
  exact Paper.walsh_column_orthogonality n a b

example {n : ℕ} (f : (Fin n → ZMod 2) → ℝ) : walsh (walsh f) = f := by
  exact Paper.walsh_involution f


/-! Exact counting and scalar/moment inputs under their reviewed hypotheses. -/
example (n d : ℕ) (hd : d ≤ n) :
    (2 ^ (d * (n - d)) : ℝ) ≤ Nat.card (Grass n d) ∧
      (Nat.card (Grass n d) : ℝ) ≤ 2 ^ (d * (n - d + 1)) := by
  exact Paper.grass_card_bounds n d hd

example (n d : ℕ) (hd : d ≤ n) :
    (Nat.card (Grass n d) : ℝ) =
      ∏ i : Fin d, (((2 ^ n : ℝ) - (2 ^ (i : ℕ) : ℝ)) /
        ((2 ^ d : ℝ) - (2 ^ (i : ℕ) : ℝ))) := by
  exact Paper.grass_card_eq_prod n d hd

example {n : ℕ} (S A : Submodule (ZMod 2) (Fin n → ZMod 2)) (hSA : S ≤ A) :
    Module.finrank (ZMod 2) (A.map S.mkQ) =
      Module.finrank (ZMod 2) A - Module.finrank (ZMod 2) S := by
  exact Paper.quotient_image_finrank S A hSA

example {n d : ℕ} (S : Grass n d) (r : ℕ) :
    Nat.card {W : Submodule (ZMod 2) ((Fin n → ZMod 2) ⧸ S.val) //
      Module.finrank (ZMod 2) W = r} = Nat.card (Grass (n - d) r) := by
  exact Paper.quotientGrass_card S r

example (n k : ℕ) (ρ : ℝ) (hρ : ρ < 1) (U V : Grass n k) :
    covariance ρ (witnessIndicator U.val) (witnessIndicator V.val) /
      ((1 - ρ) ^ (2 ^ (n - k))) ^ 2 =
        Real.exp (-Real.log (1 - ρ) * (2 ^ intersectionDimension U.val V.val : ℝ)) - 1 := by
  exact Paper.witnessIndicator_covariance_ratio n k ρ hρ U V

example (n k : ℕ) (ρ : ℝ) (hk : k ≤ n) (hρ : ρ < 1) :
    expectation ρ (fun Q => (witnessCount n k Q - expectation ρ (witnessCount n k)) ^ 2) /
      expectation ρ (witnessCount n k) ^ 2 =
        ∑ d ∈ pairRange n k, pairWeight n k d * covarianceKernel ρ d := by
  let : Nonempty (Grass n k) := Paper.grass_nonempty n k hk
  exact Paper.normalized_variance_identity n k ρ hρ

example {n k : ℕ} (h : dimensionsAdmissible n k) : quantitativeBound n k ≤ 1 / (n : ℝ) := by
  exact Paper.quantitativeBound_le_inv h

example {n k : ℕ} {ρ : ℝ} (h : dimensionsAdmissible n k) (hρ : 0 ≤ ρ)
    (hsmall : ρ ≤ samplingThreshold n k) (d : ℕ) (hd : d ≤ varianceCutoff n k) :
    covarianceKernel ρ d ≤ lowError n := by
  exact Paper.low_kernel_bound h hρ hsmall d hd


example (n k d : ℕ) :
    pairCount n k d ≤ Nat.card (Grass n d) * Nat.card (Grass (n - d) (n - k - d)) ^ 2 := by
  exact Paper.pairCount_le_grass_product n k d

example {n k d : ℕ} (h : dimensionsAdmissible n k)
    (hd : d ∈ pairRange n k) (hcut : varianceCutoff n k < d) :
    pairWeight n k d ≤ highPairWeight n k := by
  exact Paper.pairWeight_high_bound h hd hcut


example (n k : ℕ) (ρ δ : ℝ) (hdim : dimensionsAdmissible n k)
    (hρ : 0 ≤ ρ) (hρ₁ : ρ ≤ 1) (hδ₀ : 0 < δ) (hδ₁ : δ < 1)
    (hq : expectedRows n ρ ≤ recoveryThreshold n k) :
    probability ρ (UniformDecoder (n := n) (2 ^ k)) ≤ 1 / (n : ℝ) ∧
      probability ρ (ComplexRIP (n := n) (2 ^ k) δ) ≤ 1 / (n : ℝ) := by
  exact Paper.finiteDecoderComplex n k ρ δ hdim hρ hρ₁ hδ₀ hδ₁ hq

end StatementChecks
