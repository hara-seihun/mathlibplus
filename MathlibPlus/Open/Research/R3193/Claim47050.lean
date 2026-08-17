import MathlibPlus.Open.Research.R3193.Claim47053

namespace MathlibPlus.Open.Research.R3193

/-- Claim 47050: in the shared-bit construction, the expected decrement of
`W`, the equal-weight average of component variances, after revealing the
complete transcript of component `j` is the displayed cubic formula. -/
def claim47050 : Prop :=
  ∀ (n : ℕ), 0 < n → ∀ j : Fin n,
    deltaW n j = (1 + ((n : ℝ) - 1) * p ^ 3) / (n : ℝ)

end MathlibPlus.Open.Research.R3193
