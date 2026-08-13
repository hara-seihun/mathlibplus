import MathlibPlus.Basic

namespace MathlibPlus.AlgebraicGeometry

/-- Numerical admissibility for a pair of integer Chern coordinates. -/
def numericallyAdmissible_claim16989 (K2 c2 : ℤ) : Prop :=
  0 < K2 ∧ 0 < c2 ∧ 12 ∣ K2 + c2 ∧ 5 * K2 ≥ c2 - 36 ∧ K2 ≤ 3 * c2

end MathlibPlus.AlgebraicGeometry
