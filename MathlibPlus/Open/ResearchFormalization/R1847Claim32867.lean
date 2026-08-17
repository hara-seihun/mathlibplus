import Mathlib
import MathlibPlus.Open.ResearchFormalizationBatch_019ffee1_381d_7322_b2f6_d6e3063c8083

namespace MathlibPlus.Open.ResearchFormalization.R1847.Claim32867

open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

/-- The iterated logarithm in the tail expansion. -/
def logTwo (x : ℝ) : ℝ :=
  Real.log (Real.log x)

/-- The real extension of the base-sieve cutoff. -/
def realBaseCutoff (y : ℝ) : ℝ :=
  Real.sqrt (y / Real.log y)

/-- The exact finite set of primes in the tail `v(y) < p ≤ w`. -/
def tailPrimes (y w : ℝ) : Finset ℕ :=
  (Finset.range (Nat.floor w + 1)).filter
    (fun p => Nat.Prime p ∧ realBaseCutoff y < (p : ℝ))

/-- The Brun--Titchmarsh summand. -/
def tailSummand (y : ℝ) (p : ℕ) : ℝ :=
  (2 * y / (p : ℝ)) / Real.log (2 * y / (p : ℝ))

/-- The exact prime tail used in the admitted statement. -/
def tailSum (y w : ℝ) : ℝ :=
  ∑ p ∈ tailPrimes y w, tailSummand y p

/-- The displayed Mertens main integral. -/
def tailMainIntegral (y d : ℝ) : ℝ :=
  let L := Real.log y
  let v := Real.sqrt (y / L)
  let w := Real.sqrt y * Real.exp (d / 2)
  let H := L + Real.log 2
  (2 * y / H) *
    Real.log ((Real.log w) / (H - Real.log w) *
      (H - Real.log v) / Real.log v)

/-- A little-o relation at infinity. -/
def littleOAtTop (f : ℝ → ℝ) : Prop :=
  Filter.Tendsto f Filter.atTop (nhds 0)

/-- The absolute-value form of the eventual big-O relation. -/
def eventuallyBigO (f g : ℝ → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ᶠ x : ℝ in Filter.atTop, |f x| ≤ C * |g x|

/-- The uniform regime `ell + d = o(L)`. -/
def tailRegime (d : ℝ → ℝ) : Prop :=
  Filter.Tendsto
    (fun y : ℝ => (logTwo y + d y) / Real.log y)
    Filter.atTop (nhds 0)

/-- Claim 32867: the uniform prime-tail expansion and its equivalent main
integral estimate. -/
def uniformTailExpansion : Prop :=
  ∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ 0 ≤ C₂ ∧
    ∀ d : ℝ → ℝ, tailRegime d →
      (∀ᶠ y : ℝ in Filter.atTop,
        |tailSum y (Real.sqrt y * Real.exp (d y / 2)) -
            y / (Real.log y) ^ 2 *
              (4 * logTwo y + 4 * d y)| ≤
          C₁ * y / (Real.log y) ^ 2 *
            (1 + (logTwo y + d y) ^ 2 / Real.log y)) ∧
      (∀ᶠ y : ℝ in Filter.atTop,
        |tailSum y (Real.sqrt y * Real.exp (d y / 2)) -
            tailMainIntegral y (d y)| ≤
          C₂ * y / (Real.log y) ^ 2)

end

end MathlibPlus.Open.ResearchFormalization.R1847.Claim32867
