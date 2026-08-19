import MathlibPlus.Open.Analysis.Claim13423

namespace MathlibPlus.Open.Analysis.Claim13413

noncomputable section

open MathlibPlus.Open.Analysis.Claim13423

/-- Claim 13413: the signed divisor expansion of the finite sharp-prefix
energy is a strictly positive Cauchy-Gram quantity. -/
def claim13413 : Prop :=
  ∀ (y : ℕ) (c : ℝ),
    0 < c →
      let cauchyGramSum : ℝ :=
        Real.Gamma (2 * c) *
          ∑ d ∈ Nat.divisors
              (MathlibPlus.Open.Analysis.Claim13423.primorial y),
            ∑ e ∈ Nat.divisors
              (MathlibPlus.Open.Analysis.Claim13423.primorial y),
              (((ArithmeticFunction.moebius d : ℤ) : ℝ) *
                ((ArithmeticFunction.moebius e : ℤ) : ℝ) *
                Real.rpow ((d * e : ℕ) : ℝ) (2 * c - 2)) /
                Real.rpow ((d + e : ℕ) : ℝ) (2 * c)
      sharpEnergy y c = cauchyGramSum ∧
        0 < cauchyGramSum

end

end MathlibPlus.Open.Analysis.Claim13413
