import MathlibPlus.Open.NewResearch2.R0823LowFourierFunctional25093

namespace MathlibPlus.Open.NewResearch2.R0823.Claim25098

open scoped BigOperators

noncomputable section

/-- Claim 25098: the low Fourier functional is triangular on the falling-
factorial polynomial basis, with the displayed coefficient expression. -/
def claim25098 : Prop :=
  ∀ (n r s j : ℕ),
    2 * r + s ≤
        MathlibPlus.Open.NewResearch2.R0823RootBlockDefiniteness.M n →
      let falling : Polynomial ℚ :=
        ∏ k ∈ Finset.range j,
          (Polynomial.X - Polynomial.C (k : ℚ))
      if j < s then
        MathlibPlus.Open.NewResearch2.R0823LowFourierFunctional25093.lowFourierFunctional
            n r s falling = 0
      else
        MathlibPlus.Open.NewResearch2.R0823LowFourierFunctional25093.lowFourierFunctional
            n r s falling =
          (j.factorial : ℚ) * (-1 : ℚ) ^ s *
            (((Polynomial.C (1 : ℚ) + Polynomial.X) ^ r *
              (Polynomial.C (2 : ℚ) + Polynomial.X) ^
                (MathlibPlus.Open.NewResearch2.R0823RootBlockDefiniteness.M n -
                  2 * r - s)).coeff (j - s))

end
end MathlibPlus.Open.NewResearch2.R0823.Claim25098
