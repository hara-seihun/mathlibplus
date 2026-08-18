import Mathlib
import MathlibPlus.Open.Algebra.WeightedAlphabetSixClaim25978

open scoped BigOperators

namespace MathlibPlus.Open.Algebra.WeightedAlphabetSevenClaim25985

noncomputable section

abbrev Index := MathlibPlus.Open.Algebra.WeightedAlphabetSixClaim25978.Index
abbrev Composition := MathlibPlus.Open.Algebra.WeightedAlphabetSixClaim25978.Composition

abbrev zeroIndex := MathlibPlus.Open.Algebra.WeightedAlphabetSixClaim25978.zeroIndex
abbrev reflectIndex := MathlibPlus.Open.Algebra.WeightedAlphabetSixClaim25978.reflectIndex
def blockSum {m N : ℕ} (r : ℕ) (g : Index N → ℚ)
    (μ : Composition m N) : ℚ :=
  MathlibPlus.Open.Algebra.WeightedAlphabetSixClaim25978.blockSum r g μ

/-- The seven-part inclusion-exclusion difference at the empty subset. -/
def sevenfoldDifference {N : ℕ} (a : Index N → ℚ)
    (μ : Composition 7 N) : ℚ :=
  MathlibPlus.Open.Algebra.WeightedAlphabetSixClaim25978.mixedDifference a μ

/-- The residual `S₃(a) - S₂(a) + S₁(a)` on the seven-part fixed-total carrier. -/
def residual {N : ℕ} (a : Index N → ℚ)
    (μ : Composition 7 N) : ℚ :=
  blockSum 3 a μ - blockSum 2 a μ + blockSum 1 a μ

/-- Antisymmetry about the midpoint of the finite interval. -/
def antisymmetric (N : ℕ) (a : Index N → ℚ) : Prop :=
  ∀ t, a (reflectIndex N t) = -a t

/-- Extend a function on the verified finite interval using zero only outside it;
all differences below are evaluated at indices whose relevant translates lie in
that interval. -/
def extendIndex {N : ℕ} (a : Index N → ℚ) : ℕ → ℚ :=
  fun t => if h : t ≤ N then a ⟨t, h⟩ else 0

/-- Forward finite difference with step `h`. -/
def delta (h : ℕ) (f : ℕ → ℚ) : ℕ → ℚ :=
  fun t => f (t + h) - f t

abbrev iteratedDelta (r h : ℕ) (f : ℕ → ℚ) : ℕ → ℚ :=
  (delta h)^[r] f

/-- Claim 25985: under the constant-residual hypothesis, the exact sevenfold
fixed-total differences vanish, the fifth unit difference is constant, the
sixth unit difference vanishes, and the interval function is quintic while
retaining the stated antisymmetry. -/
def claim25985 : Prop :=
  ∀ (N : ℕ), 7 ≤ N →
    ∀ (a : Index N → ℚ),
      antisymmetric N a →
        let R := residual a
        (∀ μ : Composition 7 N,
          sevenfoldDifference a μ =
            2 * (R μ - a (zeroIndex N))) ∧
        ((∃ C : ℚ, ∀ μ : Composition 7 N, R μ = C) →
          (∀ μ : Composition 7 N, sevenfoldDifference a μ = 0) ∧
          (∃ C₅ : ℚ,
            ∀ j : ℕ, j + 5 ≤ N →
              iteratedDelta 5 1 (extendIndex a) j = C₅) ∧
          (∀ j : ℕ, j + 6 ≤ N →
            iteratedDelta 6 1 (extendIndex a) j = 0) ∧
          (∃ (c₀ c₁ c₂ c₃ c₄ c₅ : ℚ),
            ∀ t : Index N, a t =
              c₀ + c₁ * (t.1 : ℚ) + c₂ * (t.1 : ℚ) ^ 2 +
                c₃ * (t.1 : ℚ) ^ 3 + c₄ * (t.1 : ℚ) ^ 4 +
                c₅ * (t.1 : ℚ) ^ 5))

end

end MathlibPlus.Open.Algebra.WeightedAlphabetSevenClaim25985
