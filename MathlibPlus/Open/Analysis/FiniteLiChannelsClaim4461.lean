import Mathlib
import MathlibPlus.Open.Analysis.BatchChannelPolynomials

open scoped BigOperators
noncomputable section

namespace MathlibPlus.Open.Analysis.D0015

abbrev channelPolynomial (support : Finset ℕ) (sequence : ℕ → ℝ) (r : ℕ) :
    Polynomial ℝ :=
  MathlibPlus.Open.Analysis.finiteChannelPolynomial support sequence r

abbrev finiteLiPolynomial (support : Finset ℕ) (sequence : ℕ → ℝ) :
    Polynomial ℝ :=
  MathlibPlus.Open.Analysis.finiteLiPolynomial support sequence

/-- The real finite channel attached to the single channel-polynomial family. -/
def finiteLiChannel (support : Finset ℕ) (sequence : ℕ → ℝ)
    (r : ℕ) (x : ℝ) : ℝ :=
  Real.exp (-x) * (channelPolynomial support sequence r).eval x

/-- Claim 4461: every finite channel has the displayed exponential-polynomial
form, and the zeroth member is the finite Li exponential generating function. -/
def finiteLiChannels_claim4461 : Prop :=
  ∀ (support : Finset ℕ) (sequence : ℕ → ℝ),
    (∀ (r : ℕ) (x : ℝ),
      finiteLiChannel support sequence r x =
        Real.exp (-x) * (channelPolynomial support sequence r).eval x) ∧
    (∀ x : ℝ,
      finiteLiChannel support sequence 0 x =
        Real.exp (-x) * (finiteLiPolynomial support sequence).eval x)

end MathlibPlus.Open.Analysis.D0015
