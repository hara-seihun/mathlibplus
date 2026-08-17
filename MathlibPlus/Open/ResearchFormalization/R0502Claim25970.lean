import Mathlib
import MathlibPlus.Open.Algebra.WeightedAlphabetSixClaim25976

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R0502Claim25970

abbrev Index :=
  MathlibPlus.Open.Algebra.WeightedAlphabetSixClaim25976.Index

abbrev Composition :=
  MathlibPlus.Open.Algebra.WeightedAlphabetSixClaim25976.Composition

abbrev reflectIndex :=
  MathlibPlus.Open.Algebra.WeightedAlphabetSixClaim25976.reflectIndex

def subsetIndex {m N : ℕ} (μ : Composition m N)
    (I : Finset (Fin m)) : Index N :=
  MathlibPlus.Open.Algebra.WeightedAlphabetSixClaim25976.subsetIndex μ I

abbrev zeroIndex :=
  MathlibPlus.Open.Algebra.WeightedAlphabetSixClaim25976.zeroIndex

abbrev sixFactorAnnihilator :=
  MathlibPlus.Open.Algebra.WeightedAlphabetSixClaim25976.sixFactorAnnihilator

/-- The symmetric three-active-part function extracted from a six-factor
annihilator. -/
def activeSymmetric (N : ℕ) (h k : Index N → ℚ) : Index N → ℚ :=
  fun t => h t + h (reflectIndex N t) + 4 * k t

/-- The fixed-total four-part quadratic functional equation. -/
def quadraticFunctionalEquation (N : ℕ) (u : Index N → ℚ) : Prop :=
  ∀ μ : Composition 4 N,
    u (subsetIndex μ ({0, 1} : Finset (Fin 4))) +
        u (subsetIndex μ ({0, 2} : Finset (Fin 4))) +
        u (subsetIndex μ ({0, 3} : Finset (Fin 4))) -
        u (subsetIndex μ ({0} : Finset (Fin 4))) -
        u (subsetIndex μ ({1} : Finset (Fin 4))) -
        u (subsetIndex μ ({2} : Finset (Fin 4))) -
        u (subsetIndex μ ({3} : Finset (Fin 4))) +
        u (zeroIndex N) = 0

/-- Polynomial degree at most two on the finite index interval. -/
def quadraticOnIndex (N : ℕ) (u : Index N → ℚ) : Prop :=
  ∃ (c l q : ℚ),
    ∀ t, u t = c + l * (t.1 : ℚ) + q * (t.1 : ℚ) ^ 2

/-- Claim 25970: the symmetric three-active-part reduction satisfies the
fixed-total quadratic equation and is quadratic on the full interval. -/
def claim25970 : Prop :=
  ∀ (N : ℕ) (f h k : Index N → ℚ),
    sixFactorAnnihilator N f h k →
      quadraticFunctionalEquation N (activeSymmetric N h k) ∧
        quadraticOnIndex N (activeSymmetric N h k)

end MathlibPlus.Open.ResearchFormalization.R0502Claim25970
