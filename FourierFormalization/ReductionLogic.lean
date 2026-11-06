/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

public section

namespace Paper.ReductionLogic

/-! Finite weighted-event, second-moment and sum-splitting inequalities. -/

theorem event_mono {ι : Type*} [Fintype ι] (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (E F : ι → Prop) [DecidablePred E] [DecidablePred F]
    (hEF : ∀ i, E i → F i) :
    (∑ i, if E i then w i else 0) ≤ ∑ i, if F i then w i else 0 := by
  apply Finset.sum_le_sum
  intro i _
  by_cases hE : E i
  · simp [hE, hEF i hE]
  · by_cases hF : F i <;> simp [hE, hF, hw i]

theorem event_add_complement {ι : Type*} [Fintype ι] (w : ι → ℝ)
    (E : ι → Prop) [DecidablePred E] :
    (∑ i, if E i then w i else 0) + (∑ i, if ¬ E i then w i else 0) = ∑ i, w i := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hE : E i <;> simp [hE]

theorem zero_event_le_second_moment {ι : Type*} [Fintype ι]
    (w Z : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hμ : 0 < ∑ i, w i * Z i) :
    (∑ i, if Z i = 0 then w i else 0) ≤
      (∑ i, w i * (Z i - ∑ j, w j * Z j) ^ 2) / (∑ j, w j * Z j) ^ 2 := by
  classical
  apply (le_div_iff₀ (sq_pos_of_pos hμ)).mpr
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  by_cases hZ : Z i = 0
  · simp [hZ]
  · simp only [hZ, ↓reduceIte, zero_mul]
    exact mul_nonneg (hw i) (sq_nonneg _)

theorem weighted_split_bound {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (P : ι → Prop) [DecidablePred P] (a b : ι → ℝ)
    (A H : ℝ) (hA : 0 ≤ A) (ha : ∀ i ∈ s, 0 ≤ a i)
    (hs : ∑ i ∈ s, a i ≤ 1)
    (hlow : ∀ i ∈ s, P i → b i ≤ A)
    (hhigh : ∀ i ∈ s, ¬ P i → a i * b i ≤ H) :
    (∑ i ∈ s, a i * b i) ≤ A + ((s.filter fun i => ¬ P i).card : ℝ) * H := by
  have hlowmass : ∑ i ∈ s.filter P, a i ≤ 1 := by
    exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun i hi _ => ha i hi)).trans hs
  have hlo : (∑ i ∈ s.filter P, a i * b i) ≤ A := by
    calc
      _ ≤ ∑ i ∈ s.filter P, a i * A := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_left (hlow i (Finset.mem_filter.mp hi).1
          (Finset.mem_filter.mp hi).2) (ha i (Finset.mem_filter.mp hi).1)
      _ = (∑ i ∈ s.filter P, a i) * A := by rw [Finset.sum_mul]
      _ ≤ A := by simpa using mul_le_mul_of_nonneg_right hlowmass hA
  have hhi : (∑ i ∈ s.filter fun i => ¬ P i, a i * b i) ≤
      ((s.filter fun i => ¬ P i).card : ℝ) * H := by
    calc
      _ ≤ ∑ _i ∈ s.filter fun i => ¬ P i, H := by
        apply Finset.sum_le_sum
        intro i hi
        exact hhigh i (Finset.mem_filter.mp hi).1 (Finset.mem_filter.mp hi).2
      _ = _ := by simp
  rw [← Finset.sum_filter_add_sum_filter_not s P]
  exact add_le_add hlo hhi

end Paper.ReductionLogic
