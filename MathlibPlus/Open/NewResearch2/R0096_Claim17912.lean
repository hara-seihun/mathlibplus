import Mathlib

namespace MathlibPlus.Open.NewResearch2.R0096

noncomputable section

open scoped BigOperators

private def contiguousMinor (g : ℕ → ℕ → ℝ) (N a b : ℕ) : ℝ :=
  Matrix.det (fun i j : Fin N =>
    g (a + i.val) (b + j.val))

private def normalizedCorrelation (g : ℕ → ℕ → ℝ) (N a : ℕ) : ℝ :=
  contiguousMinor g N (a + 1) a /
    Real.sqrt (contiguousMinor g N a a *
      contiguousMinor g N (a + 1) (a + 1))

private def positiveDiagonalMinors
    (g : ℕ → ℕ → ℝ) (N a : ℕ) : Prop :=
  0 < contiguousMinor g N a a ∧
    0 < contiguousMinor g N (a + 1) (a + 1)

private def normalizedGramLorentzDeterminant
    (g : ℕ → ℕ → ℝ) (N a : ℕ) : ℝ :=
  1 - normalizedCorrelation g N a ^ 2

/-- Claim 17912: with the two diagonal contiguous minors positive, the
normalized correlation has absolute value below one exactly when the strict
unnormalized two-by-two Schur/Lorentz determinant is positive. -/
def claim17912 : Prop :=
  ∀ (g : ℕ → ℕ → ℝ) (N a : ℕ),
    positiveDiagonalMinors g N a →
      (|normalizedCorrelation g N a| < 1 ↔
        contiguousMinor g N (a + 1) a ^ 2 <
          contiguousMinor g N a a *
            contiguousMinor g N (a + 1) (a + 1)) ∧
      (|normalizedCorrelation g N a| < 1 ↔
        0 < normalizedGramLorentzDeterminant g N a)

end
end MathlibPlus.Open.NewResearch2.R0096
