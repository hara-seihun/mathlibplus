import MathlibPlus.Algebra.Claim20663
import MathlibPlus.Open.ResearchFormalization.BatchR0383R0415R0460

open scoped BigOperators
open Polynomial

namespace MathlibPlus.Open.ResearchFormalization.BatchR0383R0415R0460

noncomputable section

private noncomputable def polynomialMahlerMeasure (p : Polynomial ℤ) : ℝ :=
  Polynomial.mahlerMeasure (p.map (algebraMap ℤ ℂ))

private noncomputable def plasticConstant : ℝ :=
  sInf {t : ℝ | 1 < t ∧ t ^ 3 = t + 1}

/-- Claim 20677: the fixed orientation transform of the degree-32 padded
Lehmer fixture is irreducible and nonreciprocal, and its Mahler measure is
strictly above the Lehmer number. -/
def claim20677 : Prop :=
  let P : Polynomial ℤ :=
    MathlibPlus.Algebra.Claim20663.lehmerPolynomial * (Polynomial.X + 1) ^ 22
  let a : Fin 17 → ℤ := fun i => P.coeff i.val
  let T : Polynomial ℤ :=
    fixedCoefficientTransform 16 a
  P.Monic ∧
    P.natDegree = 32 ∧
    polynomialMahlerMeasure P = MathlibPlus.Algebra.Claim20663.lehmerNumber ∧
    P =
      reciprocalCoefficientForm 16 a ∧
    Irreducible T ∧
    T.reverse ≠ T ∧
    plasticConstant ≤ polynomialMahlerMeasure T ∧
    MathlibPlus.Algebra.Claim20663.lehmerNumber < plasticConstant

end

end MathlibPlus.Open.ResearchFormalization.BatchR0383R0415R0460
