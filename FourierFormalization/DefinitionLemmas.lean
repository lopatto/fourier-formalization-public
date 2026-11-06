/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import FourierFormalization.Definitions
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Semantic identities for the binary pairing, finite Euclidean energy,
Bernoulli row subsets and real-to-complex signals. -/

@[expose] public section

noncomputable section

open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Paper

theorem dotProduct_apply (n : ℕ) (x y : BinarySpace n) :
    dotProduct n x y = ∑ i, x i * y i := by
  simp [dotProduct, Matrix.toBilin'_apply', _root_.dotProduct]

theorem dotProduct_symm (n : ℕ) (x y : BinarySpace n) :
    dotProduct n x y = dotProduct n y x := by
  simp only [dotProduct_apply]
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

/-- Annihilator membership with the tested vector in the first argument. -/
theorem mem_annihilator_iff {n : ℕ}
    (V : Submodule (ZMod 2) (BinarySpace n)) (a : BinarySpace n) :
    a ∈ annihilator V ↔ ∀ v ∈ V, dotProduct n a v = 0 := by
  simp only [annihilator, LinearMap.BilinForm.mem_orthogonal_iff]
  constructor
  · intro h v hv
    rw [dotProduct_symm]
    exact h v hv
  · intro h v hv
    rw [dotProduct_symm]
    exact h v hv

theorem mem_signalSupport_iff {n : ℕ} (f : Signal n) (x : BinarySpace n) :
    x ∈ signalSupport f ↔ f x ≠ 0 := by
  simp [signalSupport]

theorem squaredEnergy_eq_sum_abs_sq {n : ℕ} (f : Signal n) :
    squaredEnergy f = ∑ x, |f x| ^ 2 := by
  simp [squaredEnergy]

theorem walsh_zero (n : ℕ) : walsh (0 : Signal n) = 0 := by
  funext a
  simp [walsh]

theorem rowEnergy_eq_zero_of_kernel {n : ℕ} (Q : RowSet n) (f : Signal n)
    (h : KernelOn Q f) : rowEnergy Q f = 0 := by
  exact Finset.sum_eq_zero (fun a ha => by simp [h a ha])

/-- Finite row subsets are equivalent to Boolean functions on the binary space. -/
def bitRowsEquiv (n : ℕ) : (BinarySpace n → Bool) ≃ RowSet n where
  toFun ω := Finset.univ.filter (fun a => ω a = true)
  invFun Q := fun a => decide (a ∈ Q)
  left_inv ω := by
    funext a
    cases h : ω a <;> simp [h]
  right_inv Q := by
    ext a
    simp

theorem sampleMass_bitRowsEquiv {n : ℕ} (ρ : ℝ) (ω : BinarySpace n → Bool) :
    sampleMass ρ (bitRowsEquiv n ω) =
      ∏ a : BinarySpace n, if ω a = true then ρ else 1 - ρ := by
  simp [sampleMass, bitRowsEquiv]

/-- Normalization is an algebraic finite-product identity, even before
restricting the parameter to the probability interval. -/
theorem sampleMass_sum (n : ℕ) (ρ : ℝ) :
    ∑ Q : RowSet n, sampleMass ρ Q = 1 := by
  calc
    ∑ Q : RowSet n, sampleMass ρ Q =
        ∑ ω : BinarySpace n → Bool, sampleMass ρ (bitRowsEquiv n ω) :=
      ((bitRowsEquiv n).sum_comp (sampleMass ρ)).symm
    _ = ∏ a : BinarySpace n, ∑ b : Bool, if b = true then ρ else 1 - ρ := by
      simpa only [sampleMass_bitRowsEquiv] using
        (Fintype.prod_sum (fun (_ : BinarySpace n) (b : Bool) =>
          if b = true then ρ else 1 - ρ)).symm
    _ = 1 := by
      simp [sub_eq_add_neg, add_comm]

theorem sampleMass_nonneg {n : ℕ} (ρ : ℝ) (hρ : 0 ≤ ρ) (hρ₁ : ρ ≤ 1)
    (Q : RowSet n) : 0 ≤ sampleMass ρ Q := by
  apply Finset.prod_nonneg
  intro a _
  split
  · exact hρ
  · exact sub_nonneg.mpr hρ₁

theorem sampleMass_zero {n : ℕ} (Q : RowSet n) :
    sampleMass 0 Q = if Q = ∅ then 1 else 0 := by
  split_ifs with h
  · subst Q
    simp [sampleMass]
  · obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr h
    exact Finset.prod_eq_zero (Finset.mem_univ a) (by simp [ha])

theorem sampleMass_one {n : ℕ} (Q : RowSet n) :
    sampleMass 1 Q = if Q = Finset.univ then 1 else 0 := by
  split_ifs with h
  · subst Q
    simp [sampleMass]
  · have hnall : ¬ ∀ a : BinarySpace n, a ∈ Q :=
      fun hall => h (Finset.eq_univ_of_forall hall)
    obtain ⟨a, ha⟩ := not_forall.mp hnall
    exact Finset.prod_eq_zero (Finset.mem_univ a) (by simp [ha])

def realToComplex {n : ℕ} (f : Signal n) : ComplexSignal n :=
  fun x => (f x : ℂ)

theorem complexSupport_realToComplex {n : ℕ} (f : Signal n) :
    complexSupport (realToComplex f) = signalSupport f := by
  ext x
  simp [complexSupport, signalSupport, realToComplex]

theorem complexSparse_realToComplex {n : ℕ} (K : ℕ) (f : Signal n) :
    ComplexSparse K (realToComplex f) ↔ Sparse K f := by
  simp only [ComplexSparse, Sparse, complexSupport_realToComplex]

theorem complexSquaredEnergy_realToComplex {n : ℕ} (f : Signal n) :
    complexSquaredEnergy (realToComplex f) = squaredEnergy f := by
  simp [complexSquaredEnergy, squaredEnergy, realToComplex]

theorem complexWalsh_realToComplex {n : ℕ} (f : Signal n) :
    complexWalsh (realToComplex f) = realToComplex (walsh f) := by
  funext a
  simp [complexWalsh, realToComplex, walsh]

theorem complexRowEnergy_realToComplex {n : ℕ} (Q : RowSet n) (f : Signal n) :
    complexRowEnergy Q (realToComplex f) = rowEnergy Q f := by
  simp [complexRowEnergy, rowEnergy, complexWalsh_realToComplex, realToComplex]

/-- Restrict complex RIP to real signals and choose the real normalization
`‖a‖`. This includes normalization depending on `Q`. -/
theorem complexRIP_implies_rip {n : ℕ} (K : ℕ) (δ : ℝ) (Q : RowSet n)
    (h : ComplexRIP K δ Q) : RIP K δ Q := by
  obtain ⟨a, ha⟩ := h
  refine ⟨‖a‖, ?_⟩
  intro f hf
  have hreal := ha (realToComplex f) ((complexSparse_realToComplex K f).mpr hf)
  simpa only [complexSquaredEnergy_realToComplex, complexRowEnergy_realToComplex] using hreal

end Paper
