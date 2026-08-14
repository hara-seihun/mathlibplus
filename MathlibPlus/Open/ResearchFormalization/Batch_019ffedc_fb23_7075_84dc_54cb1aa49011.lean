import Mathlib

namespace MathlibPlus.Open.ResearchFormalizationBatch

open scoped BigOperators

/-! The following predicates are the direct Lean surfaces for the admitted claims
    whose carriers and auxiliary objects are fully specified by the lease packet. -/

/-- The dyadic exceptional set in Claim 13776, with the two choices of sign
    represented explicitly. -/
def dyadicExceptionalSet : Set ℝ :=
  {y | ∃ k : ℤ,
    y = Real.pi * (6 * (k : ℝ) + 1) / (6 * Real.log 2) ∨
    y = Real.pi * (6 * (k : ℝ) - 1) / (6 * Real.log 2)}

/-- The triadic exceptional set in Claim 13776. -/
def triadicExceptionalSet : Set ℝ :=
  {y | ∃ k : ℤ, y = Real.pi * (k : ℝ) / Real.log 3}

/-- Claim 13776: the dyadic and triadic exceptional sets are disjoint. -/
def dyadicTriadicExceptionalSetsDisjoint : Prop :=
  Disjoint dyadicExceptionalSet triadicExceptionalSet

/-- Distance from a real phase to the target class of π modulo 2π, expressed
    without choosing a representative of the quotient. -/
def phaseIsWithin (ε θ : ℝ) : Prop :=
  ∃ k : ℤ, |θ - (Real.pi + 2 * Real.pi * (k : ℝ))| < ε

/-- Claim 13784: one real spectral height can simultaneously put any finite
    collection of prime phases within any positive tolerance of π modulo 2π. -/
def simultaneousAdversePrimePhases : Prop :=
  ∀ S : Finset ℕ,
    (∀ p ∈ S, Nat.Prime p) →
    ∀ ε : ℝ, 0 < ε →
      ∃ x : ℝ, ∀ p ∈ S, phaseIsWithin ε (2 * x * Real.log p)

/-- The Borel band kernel from Claim 14414. -/
noncomputable def borelBandKernel (a q u : ℝ) : ℝ :=
  Real.rpow (1 + q * u) (-a)

/-- Claim 14414: for every positive exponent, every ordered square minor of
    the positive-domain Borel band kernel is strictly positive. -/
def borelBandKernelStrictlyTotallyPositive : Prop :=
  ∀ a : ℝ, 0 < a →
    ∀ n : ℕ, 0 < n →
      ∀ q u : Fin n → ℝ,
        ((∀ i, 0 < q i) ∧
          (∀ ⦃i j⦄, i < j → q i < q j) ∧
          (∀ i, 0 < u i) ∧
          (∀ ⦃i j⦄, i < j → u i < u j)) →
        0 < Matrix.det (fun i j => borelBandKernel a (q i) (u j))

/-- A sheet word uses one Boolean value in each of r one-based columns. -/
def lowSheetColumnSet {r : ℕ} (ε : Fin r → Bool) : Finset ℕ :=
  (Finset.univ.filter (fun j : Fin r => ε j = false)).image (fun j => j.1 + 1)

/-- Claim 14470: the Boolean orientation character, with one-based column
    indices as in the admitted formula. -/
def booleanOrientationCharacter {r : ℕ} (ε : Fin r → Bool) : ℤ :=
  (-1 : ℤ) ^
    (Nat.choose r 2 + Finset.sum (lowSheetColumnSet ε) (fun j => j - 1))

/-- Claim 14472: after the global rank sign is removed, the parity is exactly
    the number of low sheets in even-numbered columns. -/
def evenColumnOrientationRule {r : ℕ} (ε : Fin r → Bool) : Prop :=
  (-1 : ℤ) ^ (Finset.sum (lowSheetColumnSet ε) (fun j => j - 1)) =
    (-1 : ℤ) ^
      (Finset.filter (fun j => j % 2 = 0) (lowSheetColumnSet ε)).card

abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- All pairwise distances, including the zero self-distances, of a finite
    planar configuration. -/
noncomputable def planarPairwiseDistances (A : Finset Plane) : Finset ℝ := by
  classical
  exact (A.product A).image (fun p => dist p.1 p.2)

/-- Finite planar diameter, with zero adjoined so the empty configuration also
    has a defined diameter. -/
noncomputable def planarDiameter (A : Finset Plane) : ℝ := by
  classical
  exact (insert 0 (planarPairwiseDistances A)).sup' (by simp) id

/-- The minimum-distance-one condition for a finite planar configuration. -/
def planarUnitSeparated (A : Finset Plane) : Prop :=
  ∀ ⦃p⦄, p ∈ A → ∀ ⦃q⦄, q ∈ A → p ≠ q → 1 ≤ dist p q

/-- Existence of a pair at the prescribed minimum distance. -/
def planarHasUnitPair (A : Finset Plane) : Prop :=
  ∃ p ∈ A, ∃ q ∈ A, p ≠ q ∧ dist p q = 1

/-- Claim 16687: a fixed-cardinality planar configuration is a diameter
    minimizer at minimum distance one exactly when it satisfies the stated
    separation, contact, and comparison conditions. -/
def planarDiameterMinimizerAtUnitDistance
    (n : ℕ) (A : Finset Plane) : Prop :=
  A.card = n ∧
    planarUnitSeparated A ∧
    planarHasUnitPair A ∧
    ∀ B : Finset Plane,
      B.card = n →
      planarUnitSeparated B →
      planarHasUnitPair B →
      planarDiameter A ≤ planarDiameter B

end MathlibPlus.Open.ResearchFormalizationBatch
