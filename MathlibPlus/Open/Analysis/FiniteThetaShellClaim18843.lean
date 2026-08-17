import MathlibPlus.Analysis.ThetaMellin

open scoped BigOperators

namespace MathlibPlus.Open.Analysis.FiniteThetaShellClaim18843

/-- Claim 18843: a candidate finite-shell family and its cosine transform are
identified with the exact positive-index theta-shell sum and half-line
integral. -/
noncomputable def claim18843_finiteThetaShellCosineTransform
    (phi : ℕ → ℝ → ℝ) (X : ℕ → ℂ → ℂ) : Prop :=
  ∀ N : ℕ, 1 ≤ N →
    (∀ u : ℝ,
      phi N u =
        Finset.sum (Finset.Icc 1 N) (fun m =>
          MathlibPlus.Analysis.ThetaMellin.thetaShell m u)) ∧
    (∀ z : ℂ,
      X N z =
        2 * ∫ u in Set.Ici (0 : ℝ),
          (phi N u : ℂ) * Complex.cos (z * (u : ℂ)))

end MathlibPlus.Open.Analysis.FiniteThetaShellClaim18843
