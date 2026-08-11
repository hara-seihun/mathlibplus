import MathlibPlus.Open.Basic

open scoped BigOperators

namespace MathlibPlus.Open.Analysis.Claim854

/-- The strict seven-positive-factor determinant assertion from claim 854.
Polynomial derivatives at zero are represented by factorial-weighted
coefficients, and negative derivative orders are zero. -/
noncomputable def exactSevenPositiveProductDeterminant : Prop :=
  ∀ (α : Fin 7 → ℝ),
    (∀ i, 0 < α i) →
      let G : Polynomial ℝ :=
        ∏ i : Fin 7, (1 + Polynomial.C (α i) * Polynomial.X)
      let entry : Fin 5 → Fin 5 → ℝ := fun i j =>
        if (i : ℕ) ≤ 4 + (j : ℕ) then
          (Nat.factorial (4 + (j : ℕ) - (i : ℕ)) : ℝ) *
            G.coeff (4 + (j : ℕ) - (i : ℕ))
        else 0
      0 < Matrix.det entry

end MathlibPlus.Open.Analysis.Claim854

namespace MathlibPlus.Open.Analysis.Claim855

/-- The nonnegative product determinant assertion through seven factors.
The source's `D₅` is inlined so this registry node introduces no public helper
definition; negative derivative orders are represented by zero entries. -/
noncomputable def productDeterminantNonneg : Prop :=
  ∀ (N : ℕ) (α : Fin N → ℝ),
    (∀ i, 0 ≤ α i) → N ≤ 7 →
      let G : Polynomial ℝ :=
        ∏ i : Fin N, (1 + Polynomial.C (α i) * Polynomial.X)
      let entry : Fin 5 → Fin 5 → ℝ := fun i j =>
        if (i : ℕ) ≤ 4 + (j : ℕ) then
          (Nat.factorial (4 + (j : ℕ) - (i : ℕ)) : ℝ) *
            G.coeff (4 + (j : ℕ) - (i : ℕ))
        else 0
      0 ≤ Matrix.det entry

end MathlibPlus.Open.Analysis.Claim855
