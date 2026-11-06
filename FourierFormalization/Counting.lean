/-
Copyright (c) 2026 Shlomo A. Perles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shlomo A. Perles
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

/-!
Finite subspace counting, adapted from shlomi-perles/subspace-convolution
commit f9b0a122432aa18f3ce292fc798437c1b5bc2692,
lean/SubspaceConvolution/Coloring/SubspaceCount.lean, Apache-2.0.

-/

@[expose] public section

open Finset Module

namespace SubspaceConvolution

/-! ## Counting subspaces of a given dimension over a finite field -/

section Grassmannian

variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]

/-- The span of a linearly independent `j`-tuple, as a `j`-dimensional subspace. -/
def spanOfLinearIndependent {j : ℕ} (s : {s : Fin j → V // LinearIndependent K s}) :
    {W : Submodule K V // finrank K W = j} :=
  ⟨Submodule.span K (Set.range s.1), by rw [finrank_span_eq_card s.2, Fintype.card_fin]⟩

/-- The linearly independent `j`-tuples spanning a `j`-dimensional subspace `W` are exactly the
ordered bases of `W`. -/
def spanOfLinearIndependentFiberEquiv {j : ℕ} (W : {W : Submodule K V // finrank K W = j})
    [FiniteDimensional K W.1] :
    {s // spanOfLinearIndependent s = W} ≃ {t : Fin j → W.1 // LinearIndependent K t} where
  toFun s := ⟨fun i => ⟨s.1.1 i, by
      have h : (spanOfLinearIndependent s.1).1 = W.1 := congrArg Subtype.val s.2
      rw [← h]
      exact Submodule.subset_span (Set.mem_range_self i)⟩,
    LinearIndependent.of_comp W.1.subtype s.1.2⟩
  invFun t := ⟨⟨W.1.subtype ∘ t.1, t.2.map' _ (Submodule.ker_subtype _)⟩, by
    apply Subtype.ext
    change Submodule.span K (Set.range (W.1.subtype ∘ t.1)) = W.1
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact (t.1 i).2
    · rw [finrank_span_eq_card (t.2.map' _ (Submodule.ker_subtype _)), Fintype.card_fin, W.2]⟩
  left_inv s := rfl
  right_inv t := rfl

variable [Fintype K] [FiniteDimensional K V]

/-- **Counting ordered bases.** For `j ≤ n = dim V` over a finite field with `q` elements, the
number of `j`-dimensional subspaces times the number `∏_{i<j} (q^j - q^i)` of ordered bases of a
`j`-dimensional space equals the number `∏_{i<j} (q^n - q^i)` of linearly independent `j`-tuples
in `V`. -/
theorem card_finrank_eq_mul_prod {j : ℕ} (hj : j ≤ finrank K V) :
    Nat.card {W : Submodule K V // finrank K W = j} *
        ∏ i : Fin j, (Fintype.card K ^ j - Fintype.card K ^ (i : ℕ)) =
      ∏ i : Fin j, (Fintype.card K ^ finrank K V - Fintype.card K ^ (i : ℕ)) := by
  have : Finite V := Module.finite_of_finite K
  have : Fintype {W : Submodule K V // finrank K W = j} := Fintype.ofFinite _
  have hfib : ∀ W : {W : Submodule K V // finrank K W = j},
      Nat.card {s // spanOfLinearIndependent s = W} =
        ∏ i : Fin j, (Fintype.card K ^ j - Fintype.card K ^ (i : ℕ)) := by
    intro W
    rw [Nat.card_congr (spanOfLinearIndependentFiberEquiv W), card_linearIndependent W.2.ge, W.2]
  rw [← card_linearIndependent hj,
    ← Nat.card_congr (Equiv.sigmaFiberEquiv (spanOfLinearIndependent (K := K) (V := V) (j := j))),
    Nat.card_sigma, Finset.sum_congr rfl fun W _ => hfib W, Finset.sum_const, Finset.card_univ,
    smul_eq_mul, Nat.card_eq_fintype_card]

/-- `card_finrank_eq_mul_prod` for `V = K^n`. -/
theorem card_finrank_eq_mul_prod_fin {n j : ℕ} (hj : j ≤ n) :
    Nat.card {W : Submodule K (Fin n → K) // finrank K W = j} *
        ∏ i : Fin j, (Fintype.card K ^ j - Fintype.card K ^ (i : ℕ)) =
      ∏ i : Fin j, (Fintype.card K ^ n - Fintype.card K ^ (i : ℕ)) := by
  have h := card_finrank_eq_mul_prod (K := K) (V := Fin n → K) (j := j)
    (by rwa [Module.finrank_fin_fun])
  rwa [Module.finrank_fin_fun] at h

end Grassmannian

end SubspaceConvolution
