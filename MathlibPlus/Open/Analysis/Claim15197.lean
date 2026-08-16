import MathlibPlus.Open.Analysis.Claim15188

open scoped BigOperators Matrix

namespace MathlibPlus.Open.Analysis.Claim15197

noncomputable section

open MathlibPlus.Open.Analysis.Claim15188

/-- Formal division by `z` for a series whose constant coefficient is zero,
represented by its shifted coefficient sequence. -/
def seriesTail (Q : PowerSeries ℝ) : PowerSeries ℝ :=
  PowerSeries.mk (fun j => PowerSeries.coeff (j + 1) Q)

/-- The coefficient of `D F` at a specified degree. -/
def productCoefficient (D : Polynomial ℝ) (F : PowerSeries ℝ) (m : ℕ) : ℝ :=
  PowerSeries.coeff m (Polynomial.toPowerSeries D * F)

/-- The literal reversal `z^n pi_n(z⁻¹)` through the stated rank. -/
def reverseAt (n : ℕ) (p : Polynomial ℝ) : Polynomial ℝ :=
  ∑ i ∈ Finset.range (n + 1),
    Polynomial.C (p.coeff i) * Polynomial.X ^ (n - i)

/-- The numerator obtained by truncating `D F` through degree `n-1`. -/
def padeNumerator (n : ℕ) (D : Polynomial ℝ) (F : PowerSeries ℝ) :
    Polynomial ℝ :=
  ∑ i ∈ Finset.range n,
    Polynomial.C (productCoefficient D F i) * Polynomial.X ^ i

/-- The exact normalized `[n-1/n]` Padé conditions used here.  In particular,
this predicate does not impose the invalid condition `natDegree D = n`. -/
def ordinaryPadeApproximant (n : ℕ) (F : PowerSeries ℝ)
    (D A : Polynomial ℝ) (firstDefect : ℝ) : Prop :=
  D.coeff 0 = 1 ∧
    (∀ m : ℕ, n ≤ m → A.coeff m = 0) ∧
    (∀ m : ℕ, m < 2 * n →
      productCoefficient D F m = A.coeff m) ∧
    productCoefficient D F (2 * n) = firstDefect

/--
The ordinary Padé formulation on the admitted logarithmic-derivative carrier.
The polynomial `P`, the formal series `Q=-zP'/P`, the quotient series
`F=Q/z=-P'/P`, and the formal-orthogonal family are all tied by hypotheses;
none is an unconstrained callback.  The denominator is only asserted to have
degree at most `n`, as required by the normalized `[n-1/n]` convention.
-/
def ordinaryPadeFormulation_claim15197 : Prop :=
  ∀ (n : ℕ) (P : Polynomial ℝ) (Q F : PowerSeries ℝ)
    (μ h : ℕ → ℝ) (π : ℕ → Polynomial ℝ),
    1 ≤ n →
    P.coeff 0 ≠ 0 →
    let Pseries : PowerSeries ℝ := Polynomial.toPowerSeries P
    let invP : PowerSeries ℝ := PowerSeries.inv Pseries
    let QP : PowerSeries ℝ :=
      -(PowerSeries.X * PowerSeries.derivative ℝ Pseries * invP)
    Q = QP →
    PowerSeries.constantCoeff Q = 0 →
    F = seriesTail Q →
    Q = PowerSeries.X * F →
    F = PowerSeries.mk μ →
    (∀ k : ℕ, k ≤ n →
      (π k).Monic ∧
        (π k).natDegree = k ∧
        Matrix.det (hankelSection μ (k + 1)) ≠ 0 ∧
        h k ≠ 0 ∧
        hankelSection μ (k + 1) *ᵥ coefficientVector (k + 1) (π k) =
          terminalVector k (h k)) →
    let D : Polynomial ℝ := reverseAt n (π n)
    let A : Polynomial ℝ := padeNumerator n D F
    (D.coeff 0 = 1 ∧
      (∀ m : ℕ, n < m → D.coeff m = 0) ∧
      ((∀ k : ℕ, k < n →
          productCoefficient D F (n + k) = 0) ∧
          productCoefficient D F (2 * n) = h n ↔
        hankelSection μ (n + 1) *ᵥ coefficientVector (n + 1) (π n) =
          terminalVector n (h n)) ∧
      ordinaryPadeApproximant n F D A (h n) ∧
      D.coeff 1 = (π n).coeff (n - 1))

end

end MathlibPlus.Open.Analysis.Claim15197
