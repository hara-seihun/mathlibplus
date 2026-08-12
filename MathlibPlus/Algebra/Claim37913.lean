import Mathlib

namespace MathlibPlus.Algebra

open MvPolynomial
noncomputable section

/-- Variables in the two exact forest aggregate polynomials of claim 37913. -/
def forestVarT_claim37913 : MvPolynomial (Fin 4) ℤ := X 0

def forestVarC2_claim37913 : MvPolynomial (Fin 4) ℤ := X 1

def forestVarC3_claim37913 : MvPolynomial (Fin 4) ℤ := X 2

def forestVarC4_claim37913 : MvPolynomial (Fin 4) ℤ := X 3

/-- Exact aggregate polynomial for `P₄` from claim 37913. -/
def forestAggregateP4_claim37913 : MvPolynomial (Fin 4) ℤ :=
  1 + 3 * forestVarT_claim37913 * forestVarC2_claim37913 +
    2 * forestVarT_claim37913 * forestVarC3_claim37913 +
    forestVarT_claim37913 * forestVarC4_claim37913 +
    forestVarT_claim37913 ^ 2 * forestVarC2_claim37913 ^ 2

/-- Exact aggregate polynomial for `K₁,₃` from claim 37913. -/
def forestAggregateStar_claim37913 : MvPolynomial (Fin 4) ℤ :=
  1 + 3 * forestVarT_claim37913 * forestVarC2_claim37913 +
    3 * forestVarT_claim37913 * forestVarC3_claim37913 +
    forestVarT_claim37913 * forestVarC4_claim37913

/-- The two displayed aggregate formulas are retained literally. -/
theorem claim37913_exact_forest_aggregates :
    forestAggregateP4_claim37913 =
        1 + 3 * forestVarT_claim37913 * forestVarC2_claim37913 +
          2 * forestVarT_claim37913 * forestVarC3_claim37913 +
          forestVarT_claim37913 * forestVarC4_claim37913 +
          forestVarT_claim37913 ^ 2 * forestVarC2_claim37913 ^ 2 ∧
      forestAggregateStar_claim37913 =
        1 + 3 * forestVarT_claim37913 * forestVarC2_claim37913 +
          3 * forestVarT_claim37913 * forestVarC3_claim37913 +
          forestVarT_claim37913 * forestVarC4_claim37913 := by
  constructor <;> rfl

end
end MathlibPlus.Algebra
