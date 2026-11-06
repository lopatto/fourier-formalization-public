/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import FourierFormalization.DefinitionLemmas
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-! Exact finite identities for the manuscript's independent row-inclusion law.
The polynomial identities are valid for every real parameter; probability
inequalities separately require the usual interval `0 ≤ ρ ≤ 1`. -/

@[expose] public section

noncomputable section

open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Paper

theorem expectation_const (n : ℕ) (ρ c : ℝ) :
    expectation ρ (fun _Q : RowSet n => c) = c := by
  unfold expectation
  rw [← Finset.sum_mul, sampleMass_sum, one_mul]

theorem expectation_add {n : ℕ} (ρ : ℝ) (X Y : RowSet n → ℝ) :
    expectation ρ (fun Q => X Q + Y Q) = expectation ρ X + expectation ρ Y := by
  simp only [expectation, mul_add, Finset.sum_add_distrib]

theorem expectation_sub {n : ℕ} (ρ : ℝ) (X Y : RowSet n → ℝ) :
    expectation ρ (fun Q => X Q - Y Q) = expectation ρ X - expectation ρ Y := by
  simp only [expectation, mul_sub, Finset.sum_sub_distrib]

theorem expectation_mul_const {n : ℕ} (ρ c : ℝ) (X : RowSet n → ℝ) :
    expectation ρ (fun Q => X Q * c) = expectation ρ X * c := by
  simp only [expectation, mul_assoc, Finset.sum_mul]

theorem expectation_const_mul {n : ℕ} (ρ c : ℝ) (X : RowSet n → ℝ) :
    expectation ρ (fun Q => c * X Q) = c * expectation ρ X := by
  simpa only [mul_comm] using expectation_mul_const ρ c X

theorem expectation_sum {n : ℕ} {ι : Type*} (ρ : ℝ) (s : Finset ι)
    (X : ι → RowSet n → ℝ) :
    expectation ρ (fun Q => ∑ i ∈ s, X i Q) = ∑ i ∈ s, expectation ρ (X i) := by
  simp only [expectation, Finset.mul_sum]
  exact Finset.sum_comm

theorem expectation_indicator {n : ℕ} (ρ : ℝ) (E : RowSet n → Prop) :
    expectation ρ (fun Q => if E Q then 1 else 0) = probability ρ E := by
  unfold expectation probability
  apply Finset.sum_congr rfl
  intro Q _
  by_cases hQ : E Q <;> simp [hQ]

theorem probability_congr {n : ℕ} (ρ : ℝ) (E F : RowSet n → Prop)
    (h : ∀ Q, E Q ↔ F Q) : probability ρ E = probability ρ F := by
  unfold probability
  apply Finset.sum_congr rfl
  intro Q _
  simp only [h Q]

theorem probability_complement {n : ℕ} (ρ : ℝ) (E : RowSet n → Prop) :
    probability ρ (fun Q => ¬ E Q) = 1 - probability ρ E := by
  have hsum : probability ρ E + probability ρ (fun Q => ¬ E Q) = 1 := by
    unfold probability
    rw [← Finset.sum_add_distrib]
    calc
      _ = ∑ Q : RowSet n, sampleMass ρ Q := by
        apply Finset.sum_congr rfl
        intro Q _
        by_cases hQ : E Q <;> simp [hQ]
      _ = 1 := sampleMass_sum n ρ
  linarith

private theorem avoidance_product (n : ℕ) (ρ : ℝ) (A : RowSet n)
    (ω : BinarySpace n → Bool) :
    (if ∀ a ∈ A, ω a = false then
      ∏ a : BinarySpace n, if ω a = true then ρ else 1 - ρ else 0) =
      ∏ a : BinarySpace n,
        if a ∈ A then (if ω a = true then 0 else 1 - ρ)
        else (if ω a = true then ρ else 1 - ρ) := by
  by_cases h : ∀ a ∈ A, ω a = false
  · rw [ite_eq_left h]
    apply Finset.prod_congr rfl
    intro a _
    by_cases ha : a ∈ A
    · simp [ha, h a ha]
    · simp [ha]
  · rw [ite_eq_right h]
    obtain ⟨a, ha⟩ := not_forall.mp h
    obtain ⟨haA, haF⟩ := not_imp.mp ha
    have haT : ω a = true := by
      cases hω : ω a
      · exact False.elim (haF hω)
      · rfl
    symm
    exact Finset.prod_eq_zero (Finset.mem_univ a) (by simp [haA, haT])

/-- Every prescribed collection of rows is omitted with its exact independent
inclusion probability, including parameters zero and one. -/
theorem probability_avoidance {n : ℕ} (ρ : ℝ) (A : RowSet n) :
    probability ρ (fun Q : RowSet n => ∀ a ∈ A, a ∉ Q) = (1 - ρ) ^ A.card := by
  unfold probability
  calc
    _ = ∑ ω : BinarySpace n → Bool,
        if ∀ a ∈ A, ω a = false then
          ∏ a : BinarySpace n, if ω a = true then ρ else 1 - ρ else 0 := by
      rw [← (bitRowsEquiv n).sum_comp]
      apply Finset.sum_congr rfl
      intro ω _
      simp [bitRowsEquiv, sampleMass]
    _ = ∑ ω : BinarySpace n → Bool, ∏ a : BinarySpace n,
        if a ∈ A then (if ω a = true then 0 else 1 - ρ)
        else (if ω a = true then ρ else 1 - ρ) := by
      apply Finset.sum_congr rfl
      intro ω _
      exact avoidance_product n ρ A ω
    _ = ∏ a : BinarySpace n, ∑ b : Bool,
        if a ∈ A then (if b = true then 0 else 1 - ρ)
        else (if b = true then ρ else 1 - ρ) :=
      (Fintype.prod_sum (fun (a : BinarySpace n) (b : Bool) =>
        if a ∈ A then (if b = true then (0 : ℝ) else 1 - ρ)
        else (if b = true then ρ else 1 - ρ))).symm
    _ = ∏ a : BinarySpace n, if a ∈ A then 1 - ρ else 1 := by
      apply Finset.prod_congr rfl
      intro a _
      by_cases ha : a ∈ A <;> simp [ha, add_comm, sub_eq_add_neg]
    _ = (1 - ρ) ^ A.card := by
      rw [Finset.prod_ite_mem_eq]
      simp

theorem probability_joint_avoidance {n : ℕ} (ρ : ℝ) (A B : RowSet n) :
    probability ρ (fun Q : RowSet n =>
      (∀ a ∈ A, a ∉ Q) ∧ (∀ b ∈ B, b ∉ Q)) = (1 - ρ) ^ (A ∪ B).card := by
  rw [← probability_avoidance ρ (A ∪ B)]
  apply probability_congr
  intro Q
  simp only [Finset.mem_union]
  constructor
  · rintro ⟨hA, hB⟩ a (ha | hb)
    · exact hA a ha
    · exact hB a hb
  · intro h
    exact ⟨fun a ha => h a (Or.inl ha), fun b hb => h b (Or.inr hb)⟩

theorem probability_row_inclusion {n : ℕ} (ρ : ℝ) (a : BinarySpace n) :
    probability ρ (fun Q : RowSet n => a ∈ Q) = ρ := by
  have havoid : probability ρ (fun Q : RowSet n => a ∉ Q) = 1 - ρ := by
    simpa using probability_avoidance ρ {a}
  have hcompl := probability_complement ρ (fun Q : RowSet n => a ∈ Q)
  linarith

theorem expectation_row_indicator {n : ℕ} (ρ : ℝ) (a : BinarySpace n) :
    expectation ρ (fun Q : RowSet n => if a ∈ Q then 1 else 0) = ρ := by
  calc
    _ = probability ρ (fun Q : RowSet n => a ∈ Q) := by
      unfold expectation probability
      apply Finset.sum_congr rfl
      intro Q _
      by_cases hQ : a ∈ Q <;> simp [hQ]
    _ = ρ := probability_row_inclusion ρ a

/-- The expectation in the manuscript is the actual mean row cardinality,
not a separately defined surrogate parameter. -/
theorem expectedRows_eq (n : ℕ) (ρ : ℝ) : expectedRows n ρ = (2 ^ n : ℝ) * ρ := by
  have hcard : ∀ Q : RowSet n,
      (Q.card : ℝ) = ∑ a : BinarySpace n, if a ∈ Q then 1 else 0 := by
    intro Q
    simp
  unfold expectedRows
  simp_rw [hcard]
  rw [expectation_sum]
  simp only [expectation_row_indicator, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  simp [BinarySpace, ZMod.card]

end Paper
