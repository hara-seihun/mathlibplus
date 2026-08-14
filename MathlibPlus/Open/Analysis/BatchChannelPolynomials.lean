import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Analysis

/-- The zeroth Poisson--Charlier polynomial in the finite-support model. -/
noncomputable def finiteChannelBasis (n : ℕ) : ℕ → Polynomial ℝ
  | 0 => Polynomial.C ((n.factorial : ℝ)⁻¹) * Polynomial.X ^ n
  | r + 1 => (finiteChannelBasis n r).derivative - finiteChannelBasis n r

/-- The finite order-`r` channel polynomial. -/
noncomputable def finiteChannelPolynomial (S : Finset ℕ) (S_f : ℕ → ℝ) (r : ℕ) : Polynomial ℝ :=
  ∑ n ∈ S, Polynomial.C (S_f n) * finiteChannelBasis n r

/-- The finite Li polynomial (the zeroth finite channel). -/
noncomputable def finiteLiPolynomial (S : Finset ℕ) (S_f : ℕ → ℝ) : Polynomial ℝ :=
  ∑ n ∈ S, Polynomial.C (S_f n / (n.factorial : ℝ)) * Polynomial.X ^ n

/-- Channel-polynomial recursion: `C₀` is the finite Li polynomial and
`C_(r+1) = C'_r - C_r`. -/
def channelPolynomialRecursion_claim4460 : Prop :=
  ∀ (S : Finset ℕ) (S_f : ℕ → ℝ),
    finiteChannelPolynomial S S_f 0 = finiteLiPolynomial S S_f ∧
      ∀ r : ℕ,
        finiteChannelPolynomial S S_f (r + 1) =
          (finiteChannelPolynomial S S_f r).derivative -
            finiteChannelPolynomial S S_f r

end MathlibPlus.Open.Analysis
