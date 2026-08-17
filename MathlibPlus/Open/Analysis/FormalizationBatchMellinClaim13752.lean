import Mathlib
import MathlibPlus.Open.Analysis.FormalizationBatchMellin

namespace MathlibPlus.Open.Analysis.FormalizationBatchMellinClaim13752

open MeasureTheory Set
open scoped BigOperators

noncomputable section

abbrev PositiveNat := {n : ℕ // 0 < n}

/-- The common complex power convention on the positive integer carrier. -/
def profileSum (w : ℝ → ℝ) (N : ℝ) (a : ℂ) : ℂ :=
  ∑' n : PositiveNat,
    (ArithmeticFunction.moebius n.1 : ℂ) *
      (w ((n.1 : ℝ) / N) : ℂ) * Complex.cpow (n.1 : ℂ) (-a)

/-- The Mellin integral remaining after the lower scale cutoff. -/
def incompleteMellin (w : ℝ → ℝ) (N₀ : ℝ)
    (n : PositiveNat) (z : ℂ) : ℂ :=
  ∫ r in Ioi ((n.1 : ℝ) / N₀),
    (w r : ℂ) * Complex.cpow (r : ℂ) (z - 1)

/-- The individual terms of the incomplete-profile remainder. -/
def remainderTerm (w : ℝ → ℝ) (N₀ : ℝ)
    (a z : ℂ) (n : PositiveNat) : ℂ :=
  (ArithmeticFunction.moebius n.1 : ℂ) * Complex.cpow (n.1 : ℂ) (-a - z) *
    incompleteMellin w N₀ n z

/-- The incomplete-profile remainder in the exact order of the source formula. -/
def remainder (w : ℝ → ℝ) (N₀ : ℝ) (a z : ℂ) : ℂ :=
  ∑' n : PositiveNat, remainderTerm w N₀ a z n

/-- The truncated scale Mellin integral. -/
def scaleMellin (w : ℝ → ℝ) (N₀ : ℝ) (a z : ℂ) : ℂ :=
  ∫ N in Ioi N₀,
    profileSum w N a * Complex.cpow (N : ℂ) (-z - 1)

/-- `W` agrees with the profile Mellin transform on the initial half-plane. -/
def profileMellinCarrier (w : ℝ → ℝ) (W : ℂ → ℂ) : Prop :=
  ∀ z : ℂ, 0 < z.re →
    W z = MathlibPlus.Open.Analysis.FormalizationBatchMellin.realMellin w z

/-- Holomorphy in a neighborhood crossing the boundary `Re z = 0`. -/
def holomorphicNearBoundary (F : ℂ → ℂ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧
    AnalyticOnNhd ℂ F {z : ℂ | |z.re| < ε}

/-- A finite-sum description of the remainder, uniformly in its Mellin variable. -/
def finiteRemainderFamily (w : ℝ → ℝ) (N₀ : ℝ) (a : ℂ) : Prop :=
  ∃ S : Finset PositiveNat,
    (∀ z : ℂ,
      remainder w N₀ a z =
        S.sum (fun n => remainderTerm w N₀ a z n)) ∧
    (∀ n : PositiveNat, n ∉ S →
      ∀ z : ℂ, remainderTerm w N₀ a z n = 0)

/-- The compact profiles are exactly the hard cutoff and the polynomial profiles
from the reviewed compact-profile carrier. -/
def compactPolynomialProfile (w : ℝ → ℝ) : Prop :=
  ∃ m : ℕ,
    w = MathlibPlus.Open.Analysis.FormalizationBatchMellin.compactProfile m

/-- Claim 13752: the identity is asserted on an initial right half-plane;
its remainder has the stated smooth-profile continuation or compact-profile
finite-sum alternative. -/
def claim_13752 : Prop :=
  ∀ (w : ℝ → ℝ) (W : ℂ → ℂ) (N₀ : ℝ) (s : ℂ),
    0 < N₀ → s.re = 1 / 2 →
      (MathlibPlus.Open.Analysis.FormalizationBatchMellin.smoothFixedProfile w ∨
        compactPolynomialProfile w) →
      profileMellinCarrier w W →
        (∃ σ : ℝ, 0 < σ ∧ ∀ z : ℂ, σ < z.re →
          ∀ a : ℂ, (a = s ∨ a = 1) →
            scaleMellin w N₀ a z =
              W z / riemannZeta (a + z) - remainder w N₀ a z) ∧
        (MathlibPlus.Open.Analysis.FormalizationBatchMellin.smoothFixedProfile w →
          ∀ a : ℂ, (a = s ∨ a = 1) →
            holomorphicNearBoundary (remainder w N₀ a)) ∧
        (compactPolynomialProfile w →
          ∀ a : ℂ, (a = s ∨ a = 1) →
            finiteRemainderFamily w N₀ a)

end
end MathlibPlus.Open.Analysis.FormalizationBatchMellinClaim13752
