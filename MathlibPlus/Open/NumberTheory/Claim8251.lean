import Mathlib

open scoped BigOperators
noncomputable section

namespace MathlibPlus.Open.NumberTheory.Claim8251

/-- The generalized-Jordan coefficient from the admitted packet. -/
def generalizedJordanCoefficient (q : ℕ) (t : ℝ) (n : ℕ) : ℝ :=
  ∏ p ∈ n.primeFactors, if p = q then 1 else 1 - Real.rpow (p : ℝ) (-t)

/-- The summatory function appearing in the admitted packet. -/
def summatoryGeneralizedJordan (q : ℕ) (t : ℝ) (x : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 x, generalizedJordanCoefficient q t n

/-- The density constant, including its stipulated endpoint value at `t = 0`. -/
def densityConstant (q : ℕ) (t : ℝ) : ℂ :=
  if t = 0 then 0 else
    1 / (riemannZeta (Complex.ofReal (1 + t)) *
      Complex.ofReal (1 - Real.rpow (q : ℝ) (-1 - t)))

/-- The residue term `q^a - N⌊q^a/N⌋` used by the outer packet. -/
def residueTerm (N m : ℕ) : ℕ :=
  m - N * (m / N)

/-- The outer prime-power residue packet from the admitted statement. -/
def outerPrimePowerResiduePacket (q a : ℕ) (s : ℝ) : ℂ :=
  ∑' N : ℕ, if 1 < N ∧ ¬ q ∣ N then
    (Complex.ofReal (ArithmeticFunction.moebius N : ℝ)) *
      Complex.ofReal (residueTerm N (q ^ a) : ℝ) /
      Complex.ofReal (Real.rpow (N : ℝ) s)
  else 0

/-- Exact generalized-Jordan packet transform (Claim 8251). -/
def exactGeneralizedJordanPacketTransform_claim8251 : Prop :=
  ∀ (q a : ℕ) (t : ℝ), q.Prime → 1 ≤ a → 0 ≤ t → t ≤ 1 →
    outerPrimePowerResiduePacket q a (1 + t) =
      densityConstant q t * Complex.ofReal (q ^ a : ℝ) -
        Complex.ofReal (summatoryGeneralizedJordan q t (q ^ a))

end MathlibPlus.Open.NumberTheory.Claim8251
