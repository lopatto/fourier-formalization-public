/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import FourierFormalization.Grassmann
public import FourierFormalization.QuotientGrassmann
public import FourierFormalization.Reduction
public import FourierFormalization.TailEstimates

/-! An injective quotient encoding of ordered annihilator-intersection pairs. -/

@[expose] public section

noncomputable section

open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Paper

private abbrev PairQuotientData (n k d : ℕ) :=
  Σ S : Grass n d,
    {A : Submodule (ZMod 2) (BinarySpace n ⧸ S.val) //
      Module.finrank (ZMod 2) A = n - k - d} ×
    {B : Submodule (ZMod 2) (BinarySpace n ⧸ S.val) //
      Module.finrank (ZMod 2) B = n - k - d}

private abbrev pairQuotientEncode {n k d : ℕ}
    (p : {UV : Grass n k × Grass n k //
      intersectionDimension UV.1.val UV.2.val = d}) : PairQuotientData n k d := by
  let S : Grass n d := ⟨annihilator p.val.1.val ⊓ annihilator p.val.2.val, p.property⟩
  refine ⟨S, ⟨(annihilator p.val.1.val).map S.val.mkQ, ?_⟩,
    ⟨(annihilator p.val.2.val).map S.val.mkQ, ?_⟩⟩
  · rw [quotient_image_finrank _ _ inf_le_left, annihilator_finrank,
      p.val.1.property, S.property]
  · rw [quotient_image_finrank _ _ inf_le_right, annihilator_finrank,
      p.val.2.property, S.property]

private theorem pairQuotientEncode_injective (n k d : ℕ) :
    Function.Injective (@pairQuotientEncode n k d) := by
  intro p q hpq
  have hleft := congrArg (fun t : PairQuotientData n k d =>
    annihilator (t.2.1.val.comap t.1.val.mkQ)) hpq
  have hright := congrArg (fun t : PairQuotientData n k d =>
    annihilator (t.2.2.val.comap t.1.val.mkQ)) hpq
  simp [pairQuotientEncode, Submodule.comap_map_mkQ,
    annihilator_annihilator] at hleft hright
  apply Subtype.ext
  exact Prod.ext (Subtype.ext hleft) (Subtype.ext hright)

/-- The triple consisting of the intersection and two quotient images determines
an ordered pair. Dropping quotient trivial-intersection restrictions only enlarges
its target. No lower intersection endpoint is used. -/
theorem pairCount_le_grass_product (n k d : ℕ) :
    pairCount n k d ≤ Nat.card (Grass n d) * Nat.card (Grass (n - d) (n - k - d)) ^ 2 := by
  have h := Nat.card_le_card_of_injective (@pairQuotientEncode n k d)
    (pairQuotientEncode_injective n k d)
  unfold pairCount
  calc
    _ ≤ Nat.card (PairQuotientData n k d) := h
    _ = Nat.card (Grass n d) * Nat.card (Grass (n - d) (n - k - d)) ^ 2 := by
      rw [Nat.card_sigma]
      simp only [Nat.card_prod, quotientGrass_card]
      rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card,
        pow_two]


/-- The two Grassmann upper bounds give the explicit exponent used by Claim 3.3. -/
theorem pairCount_real_le_pow (n k d : ℕ) (hk : k ≤ n) (hd : d ≤ n - k) :
    (pairCount n k d : ℝ) ≤
      (2 ^ (d * (n - d + 1) + 2 * (n - k - d) * (k + 1)) : ℝ) := by
  have hdn : d ≤ n := hd.trans (Nat.sub_le _ _)
  have hr : n - k - d ≤ n - d := by omega
  have hrem : (n - d) - (n - k - d) = k := by omega
  have hfirst := (grass_card_bounds n d hdn).2
  have hsecond := (grass_card_bounds (n - d) (n - k - d) hr).2
  rw [hrem] at hsecond
  have hcount : (pairCount n k d : ℝ) ≤
      (Nat.card (Grass n d) : ℝ) * (Nat.card (Grass (n - d) (n - k - d)) : ℝ) ^ 2 := by
    exact_mod_cast pairCount_le_grass_product n k d
  calc
    (pairCount n k d : ℝ) ≤
        (Nat.card (Grass n d) : ℝ) * (Nat.card (Grass (n - d) (n - k - d)) : ℝ) ^ 2 := hcount
    _ ≤ (2 ^ (d * (n - d + 1)) : ℝ) *
        (2 ^ ((n - k - d) * (k + 1)) : ℝ) ^ 2 := by
      apply mul_le_mul hfirst
      · exact pow_le_pow_left₀ (by positivity) hsecond 2
      · positivity
      · positivity
    _ = (2 ^ (d * (n - d + 1) + 2 * (n - k - d) * (k + 1)) : ℝ) := by
      rw [← pow_mul, ← pow_add]
      congr 1
      ring


/-- Claim 3.3 on the actual high range needed by the second-moment proof. -/
theorem pairWeight_high_bound {n k d : ℕ} (ha : dimensionsAdmissible n k)
    (hd : d ∈ pairRange n k) (hcut : varianceCutoff n k < d) :
    pairWeight n k d ≤ highPairWeight n k := by
  have hdim : d ≤ n - k := by
    simpa only [pairRange, Finset.mem_range, Nat.lt_succ_iff] using hd
  exact high_pairWeight_of_count_bound ha hdim hcut
    (grass_card_bounds n k ha.2.1).1 (pairCount_real_le_pow n k d ha.2.1 hdim)

end Paper
