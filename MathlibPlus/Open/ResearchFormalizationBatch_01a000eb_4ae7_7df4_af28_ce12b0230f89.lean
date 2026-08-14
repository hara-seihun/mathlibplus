import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalizationBatch_01a000eb_4ae7_7df4_af28_ce12b0230f89

/-- The exact finite weighted Abel contraction for complex phases. -/
def constantOneDiscreteWeightedAbelContraction : Prop :=
  ∀ (a b : ℤ) (u : ℤ → ℂ) (w : ℤ → ℝ) (B : ℝ),
    a < b →
    (∀ n : ℤ, a < n → n ≤ b → ‖u n‖ = 1) →
    (∀ n : ℤ, a < n → n ≤ b → 0 ≤ w n) →
    (∀ {n m : ℤ}, a < n → n < m → m ≤ b → w m ≤ w n) →
    (∀ m : ℤ, a < m → m ≤ b →
      ‖∑ n ∈ Finset.Ioc a m, u n‖ ≤ B) →
    ‖∑ n ∈ Finset.Ioc a b, (w n : ℂ) * u n‖ ≤ w (a + 1) * B

/-- The generalized Laguerre polynomial with parameter two. -/
noncomputable def generalizedLaguerreTwo (k : ℕ) (t : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (k + 1),
    (-1 : ℝ) ^ j * (Nat.choose (k + 2) (k - j) : ℝ) /
      (Nat.factorial j : ℝ) * t ^ j

/-- The integrated Laguerre atoms from the admitted statement. -/
noncomputable def integratedLaguerreAtom (n : ℕ) (t : ℝ) : ℝ :=
  if n < 2 then 0 else generalizedLaguerreTwo (n - 2) t

noncomputable def integratedLaguerreLaplace (n : ℕ) (s : ℝ) : ℝ :=
  ∫ t in Set.Ioi (0 : ℝ), Real.exp (-s * t) * integratedLaguerreAtom n t

/-- Laplace transform of the integrated Laguerre atoms. -/
def laplaceTransformIntegratedLaguerreAtoms : Prop :=
  (∀ (n : ℕ) (s : ℝ), 0 < s →
    integratedLaguerreLaplace n s =
      (n : ℝ) - s + s * (1 - 1 / s) ^ n) ∧
  (∀ s : ℝ, 0 < s →
    integratedLaguerreLaplace 0 s = 0 ∧ integratedLaguerreLaplace 1 s = 0)

noncomputable def poissonWeight (x : ℝ) (n : ℕ) : ℝ :=
  Real.exp (-x) * x ^ n / (Nat.factorial n : ℝ)

noncomputable def doubleLaplaceTuranSymbol (x s q : ℝ) : ℝ :=
  (1 / 2) * ∑' n : ℕ,
    poissonWeight x n *
      (integratedLaguerreLaplace n s * integratedLaguerreLaplace (n + 2) q +
        integratedLaguerreLaplace n q * integratedLaguerreLaplace (n + 2) s -
        2 * integratedLaguerreLaplace (n + 1) s * integratedLaguerreLaplace (n + 1) q)

/-- Exact double Laplace Turán symbol formula. -/
def exactDoubleLaplaceTuranSymbol : Prop :=
  ∀ (x s q : ℝ), 0 ≤ x → 0 < s → 0 < q →
    doubleLaplaceTuranSymbol x s q =
      ((s - q) ^ 2 / (2 * s * q)) *
          Real.exp (-x / s - x / q + x / (s * q)) - 1 +
        Real.exp (-x / s) *
          (1 - q / (2 * s) + x / (2 * s) - x / (2 * s ^ 2)) +
        Real.exp (-x / q) *
          (1 - s / (2 * q) + x / (2 * q) - x / (2 * q ^ 2))

noncomputable def lehmerPolynomial : Polynomial ℤ :=
  Polynomial.X ^ 10 + Polynomial.X ^ 9 - Polynomial.X ^ 7 - Polynomial.X ^ 6 -
    Polynomial.X ^ 5 - Polynomial.X ^ 4 - Polynomial.X ^ 3 + Polynomial.X + 1

noncomputable def lehmerPolynomialModTwo : Polynomial (ZMod 2) :=
  Polynomial.map (Int.castRingHom (ZMod 2)) lehmerPolynomial

def order31DegreeFiveIrreducible (P : Polynomial (ZMod 2)) : Prop :=
  P.Monic ∧ Irreducible P ∧ P.natDegree = 5 ∧
    ∀ z : AlgebraicClosure (ZMod 2),
      Polynomial.IsRoot (P.map (algebraMap (ZMod 2) (AlgebraicClosure (ZMod 2)))) z →
        IsPrimitiveRoot z 31

/-- The two-factor order-31 packet assertion for the Lehmer polynomial. -/
def lehmerPolynomialHasOrder31Packet : Prop :=
  (∃ P Q : Polynomial (ZMod 2),
    order31DegreeFiveIrreducible P ∧
      order31DegreeFiveIrreducible Q ∧ P ≠ Q ∧
      lehmerPolynomialModTwo = P * Q) ∧
    Set.ncard {P : Polynomial (ZMod 2) | order31DegreeFiveIrreducible P} = 6

/-- The one-plus-X-derivative operator on rational polynomials. -/
noncomputable def onePlusXDeriv (p : Polynomial ℚ) : Polynomial ℚ :=
  p + Polynomial.X * p.derivative

/-- Invertibility together with the coefficientwise division formula. -/
def onePlusXDerivInvertible : Prop :=
  (∀ (p : Polynomial ℚ) (a : ℕ),
    (onePlusXDeriv p).coeff a = (a + 1 : ℚ) * p.coeff a) ∧
    ∃ inverse : Polynomial ℚ → Polynomial ℚ,
      (∀ p, inverse (onePlusXDeriv p) = p) ∧
        (∀ p, onePlusXDeriv (inverse p) = p) ∧
          (∀ (p : Polynomial ℚ) (a : ℕ),
            (inverse p).coeff a = p.coeff a / (a + 1 : ℚ))

end MathlibPlus.Open.ResearchFormalizationBatch_01a000eb_4ae7_7df4_af28_ce12b0230f89
