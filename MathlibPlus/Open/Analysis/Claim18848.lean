import MathlibPlus.Open.Analysis.FiniteShellNonrealZeros18851

open scoped BigOperators

namespace MathlibPlus.Open.Analysis.Claim18848

noncomputable section

private def finiteShellTransform (N : ℕ) (z : ℂ) : ℂ :=
  2 * ∫ u in Set.Ici (0 : ℝ),
    ((Finset.sum (Finset.Icc 1 N)
      (fun m => MathlibPlus.Analysis.ThetaMellin.thetaShell m u) : ℝ) : ℂ) *
        Complex.cos (z * (u : ℂ))

/-- Claim 18848: each finite positive theta-shell transform has only finitely
many real zeros. -/
def claim18848 : Prop :=
  ∀ N : ℕ, 1 ≤ N →
    Set.Finite {t : ℝ | finiteShellTransform N (t : ℂ) = (0 : ℂ)}

end

end MathlibPlus.Open.Analysis.Claim18848
