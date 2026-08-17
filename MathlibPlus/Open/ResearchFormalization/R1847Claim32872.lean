import Mathlib
import MathlibPlus.Open.JacobsthalClaims
import MathlibPlus.Open.ResearchFormalizationBatch_019ffee1_381d_7322_b2f6_d6e3063c8083

namespace MathlibPlus.Open.ResearchFormalization.R1847.Claim32872

noncomputable section

attribute [local instance] Classical.propDecidable

abbrev BasePrime (y : ℝ) :=
  MathlibPlus.Open.ResearchFormalizationBatch_019ffee1_381d_7322_b2f6_d6e3063c8083.BasePrime
    (Nat.floor y)

abbrev BaseChoice (y : ℝ) :=
  MathlibPlus.Open.ResearchFormalizationBatch_019ffee1_381d_7322_b2f6_d6e3063c8083.BaseChoice
    (Nat.floor y)

/-- The exact real cutoff below which the base residue choices are made. -/
def realBaseCutoff (y : ℝ) : ℝ :=
  Real.sqrt (y / Real.log y)

/-- The critical base survivor set for one complete choice below `v`. -/
def baseSurvivorSet (y : ℝ) (c : BaseChoice y) : Finset ℕ :=
  (Finset.range (Nat.floor y + 1)).filter
    (fun n => ∀ p : BasePrime y, n % p.1 ≠ (c p).val)

/-- The survivor set in the integer carrier of the affine-pronic trace. -/
def integerBaseSurvivorSet (y : ℝ) (c : BaseChoice y) : Finset ℤ :=
  (baseSurvivorSet y c).image Int.ofNat

/-- The affine-pronic trace `{B + u(u+1) : 0 ≤ u ≤ sqrt N}`. -/
def affinePronicTrace (N : ℝ) (B : ℤ) : Finset ℤ :=
  (Finset.range (Nat.floor (Real.sqrt N) + 1)).image
    (fun u : ℕ => B + (u : ℤ) * ((u : ℤ) + 1))

/-- The iterated logarithm in the moving window. -/
def logTwo (x : ℝ) : ℝ :=
  Real.log (Real.log x)

/-- The Jacobsthal carrier at a real endpoint. -/
def jacobsthalGap (w : ℝ) : ℝ :=
  MathlibPlus.Open.JacobsthalClaims.primeResidueCoveringLength (Nat.floor w)

/-- The near-extremal trace hypothesis at a given window function. -/
def nearExtremalTraceHypothesis
    (α : ℝ) (h : ℝ → ℝ) : Prop :=
  0 < α ∧
    Filter.Tendsto h Filter.atTop Filter.atTop ∧
    Filter.Tendsto (fun N : ℝ => h N / logTwo N)
      Filter.atTop (nhds 0) ∧
    ∀ᶠ N : ℝ in Filter.atTop,
      ∀ c : BaseChoice N,
        (integerBaseSurvivorSet N c).card ≤
            N / (Real.log N) ^ 2 * (4 * logTwo N + h N) →
          ∃ B : ℤ,
            α * Real.sqrt N ≤
              (integerBaseSurvivorSet N c ∩
                affinePronicTrace N B).card

/-- The endpoint `w = sqrt N exp((h/4 - sqrt h)/2)`. -/
def movingEndpoint (h : ℝ → ℝ) (N : ℝ) : ℝ :=
  Real.sqrt N * Real.exp ((h N / 4 - Real.sqrt (h N)) / 2)

/-- The eventual strict Jacobsthal conclusion. -/
def movingJacobsConclusion (h : ℝ → ℝ) : Prop :=
  ∃ N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
    jacobsthalGap (movingEndpoint h N) < N

/-- The endpoint in the square-root excess window. -/
def squareRootWindowEndpoint (N : ℝ) : ℝ :=
  movingEndpoint (fun X : ℝ => Real.sqrt (logTwo X)) N

/-- The final exponential estimate together with its `o(w²)` conclusion. -/
def littleOAtTop (f : ℝ → ℝ) : Prop :=
  Filter.Tendsto f Filter.atTop (nhds 0)

def squareRootWindowBound : Prop :=
  ∃ e : ℝ → ℝ, littleOAtTop e ∧
    (∃ N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      jacobsthalGap (squareRootWindowEndpoint N) ≤
        squareRootWindowEndpoint N ^ 2 *
          Real.exp (-(1 / 4 - e N) *
            Real.sqrt (logTwo (squareRootWindowEndpoint N)))) ∧
    Filter.Tendsto
      (fun N : ℝ =>
        jacobsthalGap (squareRootWindowEndpoint N) /
          squareRootWindowEndpoint N ^ 2)
      Filter.atTop (nhds 0)

/-- Claim 32872: the moving near-extremal trace window gives the strict
Jacobsthal conclusion, and the square-root window gives the displayed
subquadratic estimate. -/
def movingNearExtremalTraceWindow : Prop :=
  (∀ α : ℝ, ∀ h : ℝ → ℝ,
    nearExtremalTraceHypothesis α h →
      movingJacobsConclusion h) ∧
  (∀ α : ℝ,
    nearExtremalTraceHypothesis α
      (fun N : ℝ => Real.sqrt (logTwo N)) →
      squareRootWindowBound)

end

end MathlibPlus.Open.ResearchFormalization.R1847.Claim32872
