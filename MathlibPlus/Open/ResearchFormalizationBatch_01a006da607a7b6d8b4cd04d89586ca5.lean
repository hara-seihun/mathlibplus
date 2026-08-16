import Mathlib

open scoped BigOperators

noncomputable section

namespace MathlibPlus.Open.ResearchFormalizationBatch_01a006da607a7b6d8b4cd04d89586ca5

/-- The rising factorial `(x)_n = ∏ u in [0,n), (x+u)`. -/
def risingFactorial (x : ℝ) : ℕ → ℝ
  | 0 => 1
  | n + 1 => risingFactorial x n * (x + (n : ℝ))

/-- Coefficients of the shifted Kummer series `A_j`. -/
def Acoef (α : ℝ) (j n : ℕ) : ℝ :=
  risingFactorial (α + (j : ℝ)) n /
    (((4 : ℝ) ^ n) * (n.factorial : ℝ) *
      risingFactorial ((2 : ℝ) * (j : ℝ) + (1 / 2 : ℝ)) n)

/-- Coefficients of the shifted Kummer series `P_j`. -/
def Pcoef (α : ℝ) (j n : ℕ) : ℝ :=
  risingFactorial (α + (j : ℝ) + 1) n /
    (((4 : ℝ) ^ n) * (n.factorial : ℝ) *
      risingFactorial ((2 : ℝ) * (j : ℝ) + (3 / 2 : ℝ)) n)

/-- The coefficientwise series carriers `A_j` and `P_j`. -/
def Aseries (α : ℝ) (j : ℕ) : ℕ → ℝ := fun n => Acoef α j n

def Pseries (α : ℝ) (j : ℕ) : ℕ → ℝ := fun n => Pcoef α j n

/-- The coefficientwise solution of the Bezout quotient equation. -/
def qCoeffLE (α : ℝ) (j u v : ℕ) : ℝ :=
  Finset.sum (Finset.range (u + 1)) (fun k =>
    (Acoef α j k * Pcoef α j (u + v - k) -
      if 0 < k then
        Pcoef α j (k - 1) * Acoef α j (u + v + 1 - k)
      else 0))

def qCoeff (α : ℝ) (j u v : ℕ) : ℝ :=
  if u ≤ v then qCoeffLE α j u v else qCoeffLE α j v u

/-- The positive-recursive denominator in the explicit pivot formula. -/
def pivotDenom : ℕ → ℝ
  | 0 => 2
  | j + 1 =>
      pivotDenom j *
        (2 * ((4 : ℝ) * (j : ℝ) + 1) *
          ((4 : ℝ) * (j : ℝ) + 3) ^ 2 *
          ((4 : ℝ) * (j : ℝ) + 5))

/-- The explicit pivot sequence `d_j = gammaPivot α j`. -/
def gammaPivot (α : ℝ) (j : ℕ) : ℝ :=
  ((Finset.prod (Finset.range (j + 1)) (fun u => α + (u : ℝ))) *
    (Finset.prod (Finset.range j) (fun u =>
      2 * α - (2 * ((u + 1 : ℕ) : ℝ) - 1)))) /
    pivotDenom j

/-- The contribution of the `j`th rank-one term to a fixed bivariate coefficient. -/
def rankOneCoefficient (α : ℝ) (u v j : ℕ) : ℝ :=
  if j ≤ u ∧ j ≤ v then
    gammaPivot α j * Pcoef α j (u - j) * Pcoef α j (v - j)
  else 0

/--
Coefficientwise rank-one expansion obtained by iterating the exact Darboux peel:
`(α/2) Q₀(z,w) = Σ j, d_j (zw)^j P_j(z)P_j(w)`, with finite support at
 each fixed coefficient.
-/
def claim10519_coefficientwiseRankOneExpansion : Prop :=
  (∀ (α : ℝ) (u v : ℕ),
    (α / 2) * qCoeff α 0 u v =
      Finset.sum (Finset.range (Nat.min u v + 1)) (fun j =>
        gammaPivot α j * Pcoef α j (u - j) * Pcoef α j (v - j))) ∧
  (∀ (α : ℝ) (u v : ℕ),
    Set.Finite {j : ℕ | rankOneCoefficient α u v j ≠ 0})

end MathlibPlus.Open.ResearchFormalizationBatch_01a006da607a7b6d8b4cd04d89586ca5
