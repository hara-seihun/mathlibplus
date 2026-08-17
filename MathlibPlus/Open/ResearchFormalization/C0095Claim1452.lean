import Mathlib
import MathlibPlus.NumberTheory.BellottiGrowth

noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.C0095

open MathlibPlus.NumberTheory.BellottiGrowth

/-- The Hurwitz-zeta difference in the exact complex carrier of the source. -/
def hurwitzDifference (u σ t : ℝ) : ℂ :=
  HurwitzZeta.hurwitzZeta u (σ + t * Complex.I) -
    Complex.cpow (u : ℂ) (-(σ + t * Complex.I))

/-- The packet's Vinogradov--Korobov envelope with exponent coefficient 4. -/
def publishedVKEnvelope (A σ t : ℝ) : ℝ :=
  vkEnvelope A 4 σ t

/-- The Riemann-zeta bound at one point of a published envelope domain. -/
def zetaVKBound (A σ t : ℝ) : Prop :=
  ‖riemannZeta (σ + t * Complex.I)‖ ≤
    publishedVKEnvelope A σ t

/-- The Hurwitz-zeta-difference bound at one point of a published envelope
 domain. -/
def hurwitzVKBound (A σ t u : ℝ) : Prop :=
  ‖hurwitzDifference u σ t‖ ≤ publishedVKEnvelope A σ t

/-- Both named quantities, with the full real parameter domain `0<u≤1`. -/
def bothVKBounds (A σ t : ℝ) : Prop :=
  zetaVKBound A σ t ∧
    ∀ u : ℝ, 0 < u → u ≤ 1 → hurwitzVKBound A σ t u

/-- Claim 1452: the two published lower-range envelopes retain both the
Riemann-zeta and Hurwitz-zeta-difference bounds on their exact domains. -/
def publishedLowerRangeEnvelopes : Prop :=
  (∀ σ t : ℝ,
    3 ≤ |t| → |t| ≤ (10 : ℝ) ^ 108 →
      15 / 16 ≤ σ → σ ≤ 1 →
        bothVKBounds 70.6199 σ t) ∧
    ∀ σ t : ℝ,
      3 ≤ |t| →
        1 / 2 ≤ σ → σ ≤ 15 / 16 →
          bothVKBounds 58.1 σ t

end MathlibPlus.Open.ResearchFormalization.C0095
