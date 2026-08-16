import Mathlib

namespace MathlibPlus.Open.ResearchFormalization_12527_12532_01a00b46

/-- The exact quadratic factor and finite positive-pole product occurring in the counterfeit. -/
def positiveResidueMultiplierCounterfeit : Prop :=
  ∀ (K : ℕ) (B : ℝ),
    1 ≤ K → (K + 1 : ℕ) < B →
      ∀ (j : ℕ), 1 ≤ j → j ≤ K + 1 →
        let positivePoles : Finset ℕ := Finset.Icc 1 (K + 1)
        let quadratic (z : ℝ) : ℝ :=
          1 + (2 * B / (B ^ 2 + 1)) * z + z ^ 2 / (B ^ 2 + 1)
        let baseAmplitude : ℝ :=
          Finset.prod (positivePoles.erase j)
            (fun ℓ => (1 - (j : ℝ) / (ℓ : ℝ))⁻¹)
        let counterfeitAmplitude : ℝ :=
          Finset.prod (positivePoles.erase j)
            (fun ℓ => (1 - (j : ℝ) / (ℓ : ℝ))⁻¹) *
            (quadratic (-(j : ℝ)))⁻¹
        counterfeitAmplitude = baseAmplitude *
            ((B ^ 2 + 1) / ((B - (j : ℝ)) ^ 2 + 1)) ∧
          0 < (B ^ 2 + 1) / ((B - (j : ℝ)) ^ 2 + 1) ∧
          baseAmplitude ≠ 0 ∧ counterfeitAmplitude ≠ 0 ∧
          ((0 < baseAmplitude) ↔ (0 < counterfeitAmplitude)) ∧
          ((baseAmplitude < 0) ↔ (counterfeitAmplitude < 0)) ∧
          ((0 < counterfeitAmplitude) ↔ Even (j - 1)) ∧
          ((counterfeitAmplitude < 0) ↔ Odd (j - 1))

/-- The completed-theta kernel used by the coefficient and derivative moments. -/
noncomputable def completedThetaPhi (u : ℝ) : ℝ :=
  ∑' n : ℕ,
    if 0 < n then
      (4 * Real.pi ^ 2 * (n : ℝ) ^ 4 * Real.exp (((9 : ℝ) / 2) * u) -
          6 * Real.pi * (n : ℝ) ^ 2 * Real.exp (((5 : ℝ) / 2) * u)) *
        Real.exp (-Real.pi * (n : ℝ) ^ 2 * Real.exp (2 * u))
    else 0

/-- The normalized completed-theta coefficients, including the negative-index zeros. -/
noncomputable def completedThetaCoeff (m : ℤ) : ℝ :=
  if 0 ≤ m then
    (2 : ℝ) / (Nat.factorial (2 * Int.toNat m) : ℝ) *
      ∫ u in Set.Ioi (0 : ℝ), completedThetaPhi u * u ^ (2 * Int.toNat m)
  else 0

/-- The even derivative indexed by the row index, not by twice the row index. -/
noncomputable def thetaDerivative (i : ℕ) (u : ℝ) : ℝ :=
  iteratedDeriv (2 * i) completedThetaPhi u

/-- The ordered region `0 < u₁ < ⋯ < uᵣ`. -/
def orderedPositiveSimplex (r : ℕ) : Set (Fin r → ℝ) :=
  {u | (∀ ℓ : Fin r, 0 < u ℓ) ∧
    (∀ p q : Fin r, p.1 < q.1 → u p < u q)}

/-- Exact Andreief representation of the rectangular Toeplitz minors. -/
def rectangularToeplitzAndreief : Prop :=
  ∀ (r k : ℕ),
    Matrix.det (fun i j : Fin r =>
      completedThetaCoeff ((k + (j : ℕ) : ℤ) - (i : ℕ))) =
      ((2 : ℝ) ^ r /
        (∏ j : Fin r, (Nat.factorial (2 * (k + (j : ℕ))) : ℝ))) *
        ∫ u in orderedPositiveSimplex r,
          Matrix.det (fun i ℓ : Fin r => thetaDerivative (i : ℕ) (u ℓ)) *
            (∏ ℓ : Fin r, (u ℓ) ^ (2 * k)) *
            (Finset.prod Finset.univ (fun p : Fin r =>
              Finset.prod (Finset.univ.filter (fun q : Fin r => p.1 < q.1))
                (fun q => (u q) ^ 2 - (u p) ^ 2)))

end MathlibPlus.Open.ResearchFormalization_12527_12532_01a00b46
