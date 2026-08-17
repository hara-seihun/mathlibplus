import Mathlib
import MathlibPlus.Open.Analysis.PositiveCounterfeitBatch

open scoped BigOperators

namespace MathlibPlus.Open.Research.FormalizationR0224

noncomputable section

private def counterfeitNumeratorForLoewner (u : ℂ) : ℂ :=
  1 + 7 * u + 9 * u ^ 2

private def positiveFormalEulerExponents : Prop :=
  ∀ m : ℕ, 0 < m →
    ∃ q : ℕ,
      0 < q ∧
        MathlibPlus.Open.Analysis.positiveEulerExponent m = (q : ℝ)

private def counterfeitReciprocity : Prop :=
  ∀ u : ℂ, u ≠ 0 →
    counterfeitNumeratorForLoewner u =
      9 * u ^ 2 * counterfeitNumeratorForLoewner (1 / (9 * u))

/-- The fixed Note-367 anti-Loewner function for `P₋(u)=1+7u+9u²`. -/
private def counterfeitLoewnerFunction (x : ℝ) : ℝ :=
  2 * Real.log 9 * Real.sinh (Real.log 9 * Real.sqrt x) /
    (Real.sqrt x *
      (2 * Real.cosh (Real.log 9 * Real.sqrt x) + 7 / 3))

private def counterfeitLoewnerMatrix (r : ℕ) (x : Fin r → ℝ) :
    Matrix (Fin r) (Fin r) ℝ :=
  fun i j =>
    if i = j then
      -deriv counterfeitLoewnerFunction (x i)
    else
      -(counterfeitLoewnerFunction (x i) - counterfeitLoewnerFunction (x j)) /
        (x i - x j)

private def allOrderAntiLoewnerPositivity : Prop :=
  ∀ (r : ℕ) (x : Fin r → ℝ),
    (∀ i, 0 < x i) →
      (counterfeitLoewnerMatrix r x).PosSemidef

/-- Claim 18980: the fixed reciprocal polynomial has positive integral formal
Euler exponents and reciprocal symmetry, but its fixed anti-Loewner kernel has
a negative two-node determinant and therefore fails the all-order positivity
that a Stieltjes/anti-Loewner Gram representation would provide. -/
def positiveFormalEulerDataNotAllOrderLoewnerPositive18980 : Prop :=
  positiveFormalEulerExponents ∧
    counterfeitReciprocity ∧
    (let nodes : Fin 2 → ℝ := fun i =>
      if i = 0 then 9 / 16 else 1
     let M := counterfeitLoewnerMatrix 2 nodes
     nodes 0 = 9 / 16 ∧
       nodes 1 = 1 ∧
       Matrix.det M < 0) ∧
    ¬allOrderAntiLoewnerPositivity

end

end MathlibPlus.Open.Research.FormalizationR0224
