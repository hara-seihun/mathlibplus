import MathlibPlus.Basic

namespace MathlibPlus.GraphTheory.Claim9067

/-- The integer separation core of claim 9067: a correction whose magnitude is
at least `N + 1` cannot cancel a residual in `[-1, N - 1]` when `N` is
positive.  In the source, `N` is the positive number of labelled copies of
`G`; the graph-specific construction of the two terms is retained for
alignment review. -/
theorem domination_prevents_cancellation_claim9067
    {N correction residual : ℤ}
    (hN : 0 < N)
    (hcorrection : N + 1 ≤ |correction|)
    (hresidual_lower : -1 ≤ residual)
    (hresidual_upper : residual ≤ N - 1) :
    correction + residual ≠ 0 := by
  intro hzero
  by_cases hnonneg : 0 ≤ correction
  · rw [abs_of_nonneg hnonneg] at hcorrection
    omega
  · have hneg : correction < 0 := lt_of_not_ge hnonneg
    rw [abs_of_neg hneg] at hcorrection
    omega

end MathlibPlus.GraphTheory.Claim9067
