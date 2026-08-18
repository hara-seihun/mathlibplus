import MathlibPlus.Open.ResearchFormalization.Q0064Wronskian

namespace MathlibPlus.Open.ResearchFormalization.Q0064Wronskian

/-- Claim 16417: the first-shell sequence is the reviewed scalar transform of
`generalizedBell`, i.e. `Q_n(y) = 2^(n+1) (-1)^n H_{n+1}(y)`. -/
def claim16417_firstShellQHIdentity : Prop :=
  ∀ n : ℕ,
    Q n = ((2 : ℚ) ^ (n + 1) * (-1 : ℚ) ^ n) •
      MathlibPlus.Algebra.Claim16416.generalizedBell (n + 1)

end MathlibPlus.Open.ResearchFormalization.Q0064Wronskian
