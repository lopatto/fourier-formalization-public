/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.Data.SetLike.Fintype
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
Finite binary Walsh models with Euclidean energies and independent row
inclusion. Probability and expectation are explicit finite real sums.
-/

@[expose] public section

noncomputable section

open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Paper

/-- The n-dimensional coordinate space over the two-element field. -/
abbrev BinarySpace (n : ℕ) := Fin n → ZMod 2
/-- Real-valued signals indexed by the binary coordinate space. -/
abbrev Signal (n : ℕ) := BinarySpace n → ℝ
/-- Complex-valued signals indexed by the binary coordinate space. -/
abbrev ComplexSignal (n : ℕ) := BinarySpace n → ℂ
/-- A finite set of selected rows, with no repeated rows. -/
abbrev RowSet (n : ℕ) := Finset (BinarySpace n)

/-- The binary coordinate pairing, valued in `ZMod 2`, not in `ℝ`. -/
def dotProduct (n : ℕ) : LinearMap.BilinForm (ZMod 2) (BinarySpace n) :=
  (1 : Matrix (Fin n) (Fin n) (ZMod 2)).toBilin'

/-- Binary annihilation. The pairing is symmetric, so the right-orthogonal
convention of Mathlib agrees with the manuscript's annihilator. -/
def annihilator {n : ℕ} (V : Submodule (ZMod 2) (BinarySpace n)) :
    Submodule (ZMod 2) (BinarySpace n) :=
  (dotProduct n).orthogonal V

/-- The dimension-k fiber of binary linear subspaces. -/
abbrev Grass (n k : ℕ) :=
  {V : Submodule (ZMod 2) (BinarySpace n) // Module.finrank (ZMod 2) V = k}

/-- The finite type of dimension-k binary subspaces. -/
instance grassFintype (n k : ℕ) : Fintype (Grass n k) := Fintype.ofFinite _

/-- The exact finite set of nonzero coordinates of a real signal. -/
def signalSupport {n : ℕ} (f : Signal n) : RowSet n :=
  Finset.univ.filter (fun x => f x ≠ 0)

/-- A signal has at most K nonzero coordinates. -/
def Sparse {n : ℕ} (K : ℕ) (f : Signal n) : Prop :=
  (signalSupport f).card ≤ K

/-- Squared Euclidean energy, as an explicit finite sum of squares. -/
def squaredEnergy {n : ℕ} (f : Signal n) : ℝ := ∑ x, (f x) ^ 2

/-- The representative-zero/one sign of the binary pairing. -/
def character {n : ℕ} (a x : BinarySpace n) : ℝ :=
  if dotProduct n a x = 0 then 1 else -1

/-- The normalized real Walsh transform, with N = 2^n. -/
def walsh {n : ℕ} (f : Signal n) : Signal n :=
  fun a => (Real.sqrt (2 ^ n : ℝ))⁻¹ * ∑ x, f x * character a x

/-- The indicator of a subspace divided by the square root of its cardinality. -/
def normalizedIndicator {n : ℕ} (V : Submodule (ZMod 2) (BinarySpace n)) :
    Signal n :=
  fun x => if x ∈ V then (Real.sqrt (Nat.card V : ℝ))⁻¹ else 0

/-- The Walsh transform restricted to the selected rows. -/
def restrictedWalsh {n : ℕ} (Q : RowSet n) (f : Signal n) : Q → ℝ :=
  fun a => walsh f a

/-- Squared Euclidean energy of the selected Walsh coefficients. -/
def rowEnergy {n : ℕ} (Q : RowSet n) (f : Signal n) : ℝ :=
  ∑ a ∈ Q, (walsh f a) ^ 2

/-- Every selected Walsh coefficient vanishes pointwise. -/
def KernelOn {n : ℕ} (Q : RowSet n) (f : Signal n) : Prop :=
  ∀ a ∈ Q, walsh f a = 0

/-- The sampled operator has a nonzero K-sparse real kernel vector. -/
def SparseKernel {n : ℕ} (K : ℕ) (Q : RowSet n) : Prop :=
  ∃ f : Signal n, f ≠ 0 ∧ Sparse K f ∧ KernelOn Q f

/-- The original row-inclusion law, written on finite subsets rather than
Boolean coordinate functions. It is a probability law for `0 ≤ ρ ≤ 1`. -/
def sampleMass {n : ℕ} (ρ : ℝ) (Q : RowSet n) : ℝ :=
  ∏ a : BinarySpace n, if a ∈ Q then ρ else 1 - ρ

/-- Expectation as the finite weighted sum for independent row inclusion. -/
def expectation {n : ℕ} (ρ : ℝ) (Z : RowSet n → ℝ) : ℝ :=
  ∑ Q : RowSet n, sampleMass ρ Q * Z Q

/-- Event probability as the finite sum of its row-inclusion masses. -/
def probability {n : ℕ} (ρ : ℝ) (E : RowSet n → Prop) : ℝ :=
  ∑ Q : RowSet n, if E Q then sampleMass ρ Q else 0

/-- The actual expected cardinality of the selected row set. -/
def expectedRows (n : ℕ) (ρ : ℝ) : ℝ :=
  expectation ρ (fun Q : RowSet n => (Q.card : ℝ))

/-- The selected rows avoid the annihilator of a subspace. -/
def Misses {n : ℕ} (Q : RowSet n) (V : Submodule (ZMod 2) (BinarySpace n)) : Prop :=
  ∀ a ∈ Q, a ∉ annihilator V

/-- The zero-one indicator that the rows miss a subspace annihilator. -/
def witnessIndicator {n : ℕ} (V : Submodule (ZMod 2) (BinarySpace n))
    (Q : RowSet n) : ℝ :=
  if Misses Q V then 1 else 0

/-- The number of dimension-k subspaces whose annihilators are missed. -/
def witnessCount (n k : ℕ) (Q : RowSet n) : ℝ :=
  ∑ V : Grass n k, witnessIndicator V.val Q

/-- Some dimension-k subspace has a missed annihilator. -/
def MissedSubspace (n k : ℕ) (Q : RowSet n) : Prop :=
  ∃ V : Grass n k, Misses Q V.val

/-- The selected Walsh operator is injective on all K-sparse real signals. -/
def Recovery {n : ℕ} (K : ℕ) (Q : RowSet n) : Prop :=
  ∀ f g : Signal n, Sparse K f → Sparse K g →
    (∀ a ∈ Q, walsh f a = walsh g a) → f = g

/-- One decoder recovers every K-sparse real signal exactly. -/
def UniformDecoder {n : ℕ} (K : ℕ) (Q : RowSet n) : Prop :=
  ∃ D : (Q → ℝ) → Signal n,
    ∀ f : Signal n, Sparse K f → D (restrictedWalsh Q f) = f

/-- One scalar is chosen for the whole sampled operator, before quantifying
over signals. The scalar may depend on the selected row set. -/
def RIP {n : ℕ} (K : ℕ) (δ : ℝ) (Q : RowSet n) : Prop :=
  ∃ a : ℝ, ∀ f : Signal n, Sparse K f →
    (1 - δ) * squaredEnergy f ≤ a ^ 2 * rowEnergy Q f ∧
    a ^ 2 * rowEnergy Q f ≤ (1 + δ) * squaredEnergy f

/-- The exact finite set of nonzero complex coordinates. -/
def complexSupport {n : ℕ} (f : ComplexSignal n) : RowSet n :=
  Finset.univ.filter (fun x => f x ≠ 0)

/-- A complex signal has at most K nonzero coordinates. -/
def ComplexSparse {n : ℕ} (K : ℕ) (f : ComplexSignal n) : Prop :=
  (complexSupport f).card ≤ K

/-- Squared complex Euclidean energy as a sum of squared coordinate norms. -/
def complexSquaredEnergy {n : ℕ} (f : ComplexSignal n) : ℝ :=
  ∑ x, ‖f x‖ ^ 2

/-- The same normalized Walsh matrix acting on complex signals. -/
def complexWalsh {n : ℕ} (f : ComplexSignal n) : ComplexSignal n :=
  fun a => ((Real.sqrt (2 ^ n : ℝ))⁻¹ : ℂ) *
    ∑ x, f x * (character a x : ℂ)

/-- Squared energy of the selected complex Walsh coefficients. -/
def complexRowEnergy {n : ℕ} (Q : RowSet n) (f : ComplexSignal n) : ℝ :=
  ∑ a ∈ Q, ‖complexWalsh f a‖ ^ 2

/-- One complex scalar normalizes RIP on all K-sparse complex signals. -/
def ComplexRIP {n : ℕ} (K : ℕ) (δ : ℝ) (Q : RowSet n) : Prop :=
  ∃ a : ℂ, ∀ f : ComplexSignal n, ComplexSparse K f →
    (1 - δ) * complexSquaredEnergy f ≤ ‖a‖ ^ 2 * complexRowEnergy Q f ∧
    ‖a‖ ^ 2 * complexRowEnergy Q f ≤ (1 + δ) * complexSquaredEnergy f

/-- The absolute constant ln(2)/8 used in the finite bounds. -/
def c₀ : ℝ := Real.log 2 / 8

/-- The base-two logarithm, expressed using the natural logarithm. -/
def log₂ (x : ℝ) : ℝ := Real.log x / Real.log 2

/-- The finite theorem hypotheses: n >= 256, k <= n and min(k,n-k) >= 12 log₂ n. -/
def dimensionsAdmissible (n k : ℕ) : Prop :=
  256 ≤ n ∧ k ≤ n ∧ 12 * log₂ (n : ℝ) ≤ (min k (n - k) : ℝ)

/-- The permitted row-inclusion probability c₀(K/N)k(n-k). -/
def samplingThreshold (n k : ℕ) : ℝ :=
  c₀ * (2 ^ k : ℝ) / (2 ^ n : ℝ) * (k : ℝ) * ((n - k : ℕ) : ℝ)

/-- The finite failure bound 4c₀/n + (3 log₂ n + 1) exp(-ln(2)k(n-k)/4). -/
def quantitativeBound (n k : ℕ) : ℝ :=
  4 * c₀ / (n : ℝ) + (3 * log₂ (n : ℝ) + 1) *
    Real.exp (-Real.log 2 * (k : ℝ) * ((n - k : ℕ) : ℝ) / 4)

/-- The necessary expected-row scale c₀ K log₂ K log₂(N/K). -/
def recoveryThreshold (n k : ℕ) : ℝ :=
  c₀ * (2 ^ k : ℝ) * log₂ (2 ^ k : ℝ) *
    log₂ ((2 ^ n : ℝ) / (2 ^ k : ℝ))

end Paper
