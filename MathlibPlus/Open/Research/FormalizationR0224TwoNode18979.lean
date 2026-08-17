import MathlibPlus.Open.Analysis.PositiveCounterfeitBatch

open scoped BigOperators

namespace MathlibPlus.Open.Research.FormalizationR0224TwoNode

noncomputable section

/-- The fixed anti-Loewner kernel attached to the counterfeit polynomial
`P₋(u)=1+7u+9u²`. -/
private def counterfeitLoewnerFunction (x : ℝ) : ℝ :=
  2 * Real.log 9 * Real.sinh (Real.log 9 * Real.sqrt x) /
    (Real.sqrt x *
      (2 * Real.cosh (Real.log 9 * Real.sqrt x) + 7 / 3))

/-- The exact diagonal-derivative/off-diagonal divided-difference matrix. -/
private def counterfeitLoewnerMatrix (r : ℕ) (x : Fin r → ℝ) :
    Matrix (Fin r) (Fin r) ℝ :=
  fun i j =>
    if i = j then
      -deriv counterfeitLoewnerFunction (x i)
    else
      -(counterfeitLoewnerFunction (x i) - counterfeitLoewnerFunction (x j)) /
        (x i - x j)

/-- Claim 18979: the fixed counterfeit's order-two anti-Loewner matrix at
nodes `9/16` and `1` has negative determinant. -/
def claim18979_twoNodeNegativeLoewnerDeterminant : Prop :=
  let nodes : Fin 2 → ℝ := fun i =>
    if i = 0 then 9 / 16 else 1
  let M := counterfeitLoewnerMatrix 2 nodes
  nodes 0 = 9 / 16 ∧
    nodes 1 = 1 ∧
      Matrix.det M < 0

end

end MathlibPlus.Open.Research.FormalizationR0224TwoNode
