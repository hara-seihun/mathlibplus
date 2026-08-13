import Mathlib.Data.Real.Basic

/-!
# Reserve perturbation bounds (claim 21977)

The source gives five scalar expressions in the upper-bound variables
`a₀, b₀, g₀, g₁, g₂, r₀, r₁, r₂`.  No sign, ordering, or source-specific
meaning for those variables is added here; the declarations preserve only
the displayed formulas.
-/

namespace MathlibPlus.Analysis

/-- The displayed `dJ` expression from claim 21977. -/
def dJ_claim21977
    (a₀ b₀ g₀ g₁ g₂ r₀ r₁ r₂ : ℝ) : ℝ :=
  a₀ * (2 * g₀ * r₀ + r₀ ^ 2) + g₁ * r₀ + r₁ * g₀ + r₁ * r₀

/-- The displayed `K₀` expression from claim 21977. -/
def K0_claim21977
    (a₀ b₀ g₀ g₁ g₂ r₀ r₁ r₂ : ℝ) : ℝ :=
  b₀ * g₀ ^ 2 + g₀ * g₂ + g₁ ^ 2

/-- The displayed `dK` expression from claim 21977. -/
def dK_claim21977
    (a₀ b₀ g₀ g₁ g₂ r₀ r₁ r₂ : ℝ) : ℝ :=
  b₀ * (2 * g₀ * r₀ + r₀ ^ 2) +
    g₀ * r₂ + r₀ * g₂ + r₀ * r₂ + 2 * g₁ * r₁ + r₁ ^ 2

/-- The displayed `dC` expression from claim 21977. -/
def dC_claim21977
    (a₀ b₀ g₀ g₁ g₂ r₀ r₁ r₂ : ℝ) : ℝ :=
  dK_claim21977 a₀ b₀ g₀ g₁ g₂ r₀ r₁ r₂ * (g₀ + r₀) ^ 2 +
    K0_claim21977 a₀ b₀ g₀ g₁ g₂ r₀ r₁ r₂ * (2 * g₀ * r₀ + r₀ ^ 2)

/-- The displayed `J₀` expression from claim 21977. -/
def J0_claim21977
    (a₀ b₀ g₀ g₁ g₂ r₀ r₁ r₂ : ℝ) : ℝ :=
  (a₀ * g₀ + g₁) * g₀

end MathlibPlus.Analysis
