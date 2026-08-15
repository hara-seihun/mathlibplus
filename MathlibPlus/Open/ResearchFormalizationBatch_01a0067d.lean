import Mathlib

open scoped BigOperators Topology
open Filter Asymptotics

namespace MathlibPlus.Open.Analysis

/-- Sharp local ratio estimate for a finite positive zero-diagonal Jacobi chain. -/
def sharpLocalEigenvectorRatioBound
    (N j : ℕ) (a v : ℕ → ℝ) (eigenvalue : ℝ) : Prop :=
  let A : ℕ → ℝ := fun r =>
    if r = N then 0 else
      sSup (Set.insert 0 {x : ℝ | ∃ ℓ, r ≤ ℓ ∧ ℓ < N ∧ x = a ℓ})
  (a 0 = 0 ∧
      a N = 0 ∧
      (∀ i, 1 ≤ i → i < N → 0 < a i) ∧
      (∀ i, i < N →
        (if i = 0 then 0 else a i * v (i - 1)) +
            (if i + 1 < N then a (i + 1) * v (i + 1) else 0) =
          eigenvalue * v i) ∧
      0 < eigenvalue ∧
      1 ≤ j ∧
      j < N) →
    ((eigenvalue > 2 * A (j + 1) →
        0 < |v j / v (j - 1)| ∧
        |v j / v (j - 1)| ≤
          2 * a j /
            (eigenvalue + Real.sqrt (eigenvalue ^ 2 - 4 * (A (j + 1)) ^ 2))) ∧
      (eigenvalue > 2 * A j →
        2 * a j /
            (eigenvalue + Real.sqrt (eigenvalue ^ 2 - 4 * (A (j + 1)) ^ 2)) < 1))

end MathlibPlus.Open.Analysis

namespace MathlibPlus.Open.ResearchFormalization

/-- C-0184 admissibility together with its stated asymptotic consequences. -/
def admissiblePolynomialProfileClass
    (P : ℕ → Polynomial ℝ) (a : ℕ → ℕ → ℝ) (d : ℕ → ℕ)
    (B : ℕ → ℝ) (k : ℕ) : Prop :=
  1 ≤ k ∧
    (∀ L,
      P L =
        (1 + ∑ j ∈ Finset.Icc 1 (d L),
          Polynomial.C (a L j) * Polynomial.X ^ j : Polynomial ℝ)) ∧
    (∀ L j, 1 ≤ j → j ≤ d L → |a L j| ≤ (B L) ^ j) ∧
    Tendsto
      (fun L : ℕ => ((B L) ^ k * (d L : ℝ)) / (L : ℝ))
      atTop (𝓝 0) ∧
    (fun L : ℕ => (d L : ℝ) * Real.log (B L)) =o[atTop]
      (fun L : ℕ => (L : ℝ)) ∧
    (fun L : ℕ => (d L : ℝ)) =o[atTop] (fun L : ℕ => (L : ℝ)) ∧
    Tendsto
      (fun L : ℕ => B L / Real.rpow (L : ℝ) (1 / (k : ℝ)))
      atTop (𝓝 0)

/-- C-0184 normalization after the transition scaling. -/
def profileNormalizationSurvivesTransitionScaling
    (P : ℕ → Polynomial ℝ) (a : ℕ → ℕ → ℝ) (d : ℕ → ℕ)
    (B T : ℕ → ℝ) (k : ℕ) (y : ℝ) : Prop :=
  1 ≤ k ∧
    (∀ L,
      P L =
        (1 + ∑ j ∈ Finset.Icc 1 (d L),
          Polynomial.C (a L j) * Polynomial.X ^ j : Polynomial ℝ)) ∧
    (∀ L j, 1 ≤ j → j ≤ d L → |a L j| ≤ (B L) ^ j) ∧
    Tendsto
      (fun L : ℕ => ((B L) ^ k * (d L : ℝ)) / (L : ℝ))
      atTop (𝓝 0) ∧
    (fun L : ℕ => (d L : ℝ) * Real.log (B L)) =o[atTop]
      (fun L : ℕ => (L : ℝ)) ∧
    (fun L : ℕ => (d L : ℝ)) =o[atTop] (fun L : ℕ => (L : ℝ)) ∧
    Tendsto
      (fun L : ℕ => B L / Real.rpow (L : ℝ) (1 / (k : ℝ)))
      atTop (𝓝 0) ∧
    0 < y ∧
    (∀ L, (T L) ^ 2 = Real.rpow (L : ℝ) (1 / (k : ℝ))) ∧
    (∀ L,
      B L / (T L) ^ 2 =
        B L / Real.rpow (L : ℝ) (1 / (k : ℝ))) ∧
    Tendsto
      (fun L : ℕ => B L / (T L) ^ 2)
      atTop (𝓝 0) ∧
    (∀ L,
      let Q : Polynomial ℂ :=
        (P L).map Complex.ofRealHom |>.comp
          (Polynomial.C (((T L : ℂ) ^ 2)⁻¹) *
            (Polynomial.X + Polynomial.C (Complex.I * Complex.ofReal y)) ^ 2)
      Q.natDegree ≤ 2 * d L) ∧
    (∀ L,
      let Q : Polynomial ℂ :=
        (P L).map Complex.ofRealHom |>.comp
          (Polynomial.C (((T L : ℂ) ^ 2)⁻¹) *
            (Polynomial.X + Polynomial.C (Complex.I * Complex.ofReal y)) ^ 2)
      Polynomial.eval (0 : ℂ) Q =
        Complex.ofReal
          (Polynomial.eval
            (-y ^ 2 / (T L) ^ 2) (P L))) ∧
    Tendsto
      (fun L : ℕ =>
        let Q : Polynomial ℂ :=
          (P L).map Complex.ofRealHom |>.comp
            (Polynomial.C (((T L : ℂ) ^ 2)⁻¹) *
              (Polynomial.X + Polynomial.C (Complex.I * Complex.ofReal y)) ^ 2)
        Polynomial.eval (0 : ℂ) Q)
      atTop (𝓝 (1 : ℂ))

end MathlibPlus.Open.ResearchFormalization
