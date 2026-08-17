import MathlibPlus.Analysis.ThetaMellin

open scoped BigOperators

namespace MathlibPlus.Open.Analysis.FiniteShellNonrealZeros18851

/-- Claim 18851: for every finite positive shell cutoff, the explicitly
constructed cosine transform has infinitely many complex zeros but only
finitely many real zeros. -/
noncomputable def finiteShellNonrealZeros_claim18851 : Prop :=
  ∀ N : ℕ, 1 ≤ N →
    let phiN : ℝ → ℝ := fun u =>
      Finset.sum (Finset.Icc 1 N) (fun m =>
        MathlibPlus.Analysis.ThetaMellin.thetaShell m u)
    let XN : ℂ → ℂ := fun z =>
      2 * ∫ u in Set.Ici (0 : ℝ),
        (phiN u : ℂ) * Complex.cos (z * (u : ℂ))
    Set.Infinite {z : ℂ | XN z = 0} ∧
      Set.Finite {t : ℝ | XN (t : ℂ) = (0 : ℂ)}

end MathlibPlus.Open.Analysis.FiniteShellNonrealZeros18851
