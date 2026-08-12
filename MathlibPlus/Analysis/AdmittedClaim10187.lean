import MathlibPlus.Basic

namespace MathlibPlus.Analysis.Admitted10187

/-- The adjacent derivative exterior square from claim 10187.  Iterated `deriv`
is used so the definition remains total for functions lacking the required
smoothness; the source claim itself supplies the intended differentiability
context. -/
noncomputable def adjacentDerivativeExteriorSquare
    (F : ℝ → ℝ) (r : ℕ) (_hr : 1 ≤ r) (x : ℝ) : ℝ :=
  ((deriv^[r]) F) x * ((deriv^[r + 2]) F) x -
    ((deriv^[r + 1]) F) x ^ 2

end MathlibPlus.Analysis.Admitted10187
