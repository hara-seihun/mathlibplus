import Mathlib
import MathlibPlus.Open.JacobsthalClaims
import MathlibPlus.Open.ResearchFormalizationBatch_019ffee1_381d_7322_b2f6_d6e3063c8083

namespace MathlibPlus.Open.ResearchFormalization.R1847.Claim32868

noncomputable section

attribute [local instance] Classical.propDecidable

/-- The iterated logarithm in the survivor scale. -/
def logTwo (x : ℝ) : ℝ :=
  Real.log (Real.log x)

/-- The coefficient-four survivor scale. -/
def survivorScale (x : ℝ) : ℝ :=
  x * logTwo x / (Real.log x) ^ 2

/-- The floor extension of the exact admitted base survivor minimum. -/
def realBaseSurvivorMinimum (y : ℝ) : ℝ :=
  MathlibPlus.Open.ResearchFormalizationBatch_019ffee1_381d_7322_b2f6_d6e3063c8083.baseSurvivorMinimum
    (Nat.floor y)

/-- The little-o relation used for the survivor lower bound. -/
def littleOAtTop (f : ℝ → ℝ) : Prop :=
  Filter.Tendsto f Filter.atTop (nhds 0)

/-- The exact Jacobsthal carrier at a real cutoff, via its integer floor. -/
def jacobsthalGap (w : ℝ) : ℝ :=
  MathlibPlus.Open.JacobsthalClaims.primeResidueCoveringLength (Nat.floor w)

/-- The eventual Vinogradov relation. -/
def eventuallyBigO (f g : ℝ → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ᶠ x : ℝ in Filter.atTop, |f x| ≤ C * |g x|

/-- A fixed coefficient gain in the exact survivor minimum. -/
def lowerSurvivorGain (δ : ℝ) : Prop :=
  ∃ e : ℝ → ℝ, littleOAtTop e ∧
    ∀ᶠ y : ℝ in Filter.atTop,
      (4 + δ + e y) * survivorScale y ≤
        realBaseSurvivorMinimum y

/-- The substitution `y = w²/(log w)^c`. -/
def rescaledY (c w : ℝ) : ℝ :=
  w ^ 2 / Real.rpow (Real.log w) c

/-- The corresponding value of `d = log(w²/y)`. -/
def rescaledD (c w : ℝ) : ℝ :=
  Real.log (w ^ 2 / rescaledY c w)

/-- The tail coefficient after the stated substitution. -/
def rescaledTailCoefficient (c : ℝ) (w : ℝ) : ℝ :=
  let y := rescaledY c w
  let L := Real.log y
  let ell := logTwo y
  let tail :=
    ∑ p ∈
        (Finset.range (Nat.floor w + 1)).filter
          (fun p => Nat.Prime p ∧
            Real.sqrt (y / L) < (p : ℝ)),
      (2 * y / (p : ℝ)) / Real.log (2 * y / (p : ℝ))
  tail / (y * ell / L ^ 2)

/-- Claim 32868: the fixed lower-survivor coefficient gain implies the
stated logarithmically subquadratic Jacobsthal bound, with the displayed
substitution and tail coefficient. -/
def fixedLowerSurvivorGain : Prop :=
  ∀ δ : ℝ, 0 < δ → lowerSurvivorGain δ →
    ∀ c : ℝ, 0 < c → c < δ / 4 →
      eventuallyBigO jacobsthalGap
        (fun w => w ^ 2 / Real.rpow (Real.log w) c) ∧
      eventuallyBigO
        (fun w => rescaledD c w - c * logTwo w)
        (fun _ => (1 : ℝ)) ∧
      Filter.Tendsto (rescaledTailCoefficient c)
        Filter.atTop (nhds (4 + 4 * c))

end

end MathlibPlus.Open.ResearchFormalization.R1847.Claim32868
