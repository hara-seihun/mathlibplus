import MathlibPlus.Open.LinearAlgebra.LayerTransferBound

namespace MathlibPlus.Open.LinearAlgebra.K0131Claim8999

open MathlibPlus.Open.LinearAlgebra

noncomputable section

/-- Claim 8999: the local conditioning value on an ordered positive layer,
with the positive scale and coefficient hypotheses retained in its carrier. -/
def localConditioningClaim8999
    (p_N q_N : ℕ) (a_N : ℕ → ℝ) (lambda_N c_N : ℝ)
    (hpq : p_N ≤ q_N) (hc : 0 < c_N)
    (ha : ∀ r ∈ Finset.Icc p_N (q_N + 1), 0 < a_N r) : ℝ :=
  localConditioning a_N lambda_N c_N p_N q_N hpq

end

end MathlibPlus.Open.LinearAlgebra.K0131Claim8999
