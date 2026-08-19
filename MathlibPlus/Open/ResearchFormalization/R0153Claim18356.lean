import MathlibPlus.Open.ResearchFormalization.R0153Claim18355

namespace MathlibPlus.Open.ResearchFormalization.R0153Claim18356

noncomputable section

/-- The unresolved feasibility predicate for the conditional Hankel square.
It records the existence of the displayed real factor for fixed `N`, `P`, `R`,
and `lam`; it does not assert that this predicate holds for any particular
case. -/
def factorizationFeasibilityObligation18356
    (N : ℕ) (P R : Polynomial ℝ) (lam : ℝ) : Prop :=
  ∃ L : Matrix (Fin N) (Fin N) ℝ,
    MathlibPlus.Open.ResearchFormalization.R0153Claim18355.polynomialHankel
        (P - (lam : ℝ) • R) N =
      L * Matrix.transpose L

end

end MathlibPlus.Open.ResearchFormalization.R0153Claim18356
