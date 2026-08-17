import MathlibPlus.Open.FormalizationBatch.FirstShell

namespace MathlibPlus.Open.FormalizationBatch.FirstShell

/-- Claim 13898: exact Wronskian factorization and degree of the residual
polynomial. -/
def wronskianFactorAndDegree_claim13898 : Prop :=
  ∀ r : ℕ,
    firstShellWronskian r =
        Polynomial.X ^ (r * (r - 1) / 2) * firstShellP r ∧
      (firstShellP r).natDegree = r * (r + 1) / 2

end MathlibPlus.Open.FormalizationBatch.FirstShell
