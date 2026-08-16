import Mathlib

noncomputable section
open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization

/-- The coefficient convention for the bilateral Toeplitz matrix attached to a
power series.  Negative indices are zero. -/
def bilateralCoefficient (f : ℕ → ℝ) (n : ℤ) : ℝ :=
  if 0 ≤ n then f n.toNat else 0

/-- A finite Toeplitz minor of the coefficient sequence. -/
def toeplitzMinorMatrix {r : ℕ} (f : ℕ → ℝ)
    (rows cols : Fin r → ℕ) : Matrix (Fin r) (Fin r) ℝ :=
  fun i j =>
    bilateralCoefficient f ((cols j : ℤ) - (rows i : ℤ))

/-- The order-three Pólya-frequency condition, written as the nonnegativity of
all Toeplitz minors of orders at most three. -/
def PF3Sequence (f : ℕ → ℝ) : Prop :=
  ∀ (r : ℕ), r ≤ 3 →
    ∀ (rows cols : Fin r → ℕ), StrictMono rows → StrictMono cols →
      0 ≤ Matrix.det (toeplitzMinorMatrix f rows cols)

/-- Entirety of the ordinary generating function of a real sequence. -/
def EntireCoefficientSeries (f : ℕ → ℝ) : Prop :=
  ∀ z : ℂ, Summable (fun n : ℕ => (f n : ℂ) * z ^ n)

/-- A coefficient sequence is eventually zero exactly when its generating
function is a polynomial. -/
def EventuallyZeroCoefficients (f : ℕ → ℝ) : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n → f n = 0

/-- Strict adjacent order-two Toeplitz minors. -/
def StrictAdjacentPF2 (f : ℕ → ℝ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → f n ^ 2 > f (n - 1) * f (n + 1)

/-- The source-column index set in the deleted-row expansion: the first
`r - 1` columns are fixed and the last one is the future column. -/
def endpointSourceIndex (r k ell j : ℕ) : ℕ :=
  if j + 1 < r then k + 1 + j else k + r + ell

/-- Delete row `m` from the rows numbered `0,...,r`. -/
def endpointDeletedRowIndex (m i : ℕ) : ℕ :=
  if i < m then i else i + 1

/-- The exact source determinant occurring in the deleted-row cofactor
expansion. -/
def endpointSourceMatrix (f : ℕ → ℝ) (r k : ℕ) (m : Fin (r + 1))
    (ell : ℕ) : Matrix (Fin r) (Fin r) ℝ :=
  fun i j =>
    bilateralCoefficient f
      ((endpointSourceIndex r k ell j.1 : ℤ) -
        (endpointDeletedRowIndex m.1 i.1 : ℤ))

/-- Deleted-row endpoint cofactor, with the `1/4` endpoint parameter used by
the rank-three counterexample. -/
def endpointCofactor (f : ℕ → ℝ) (r k : ℕ) (m : Fin (r + 1)) : ℝ :=
  ∑' ell : ℕ,
    ((1 : ℝ) / 4) ^ ell * Matrix.det (endpointSourceMatrix f r k m ell)

/-- A source column of the fixed-row source block. -/
def endpointSourceColumn (f : ℕ → ℝ) (r k ell : ℕ) (j : Fin r) : Fin r → ℝ :=
  fun i =>
    bilateralCoefficient f
      ((endpointSourceIndex r k ell j.1 : ℤ) - (i.1 : ℤ))

/-- An eventual constant-coefficient recurrence. -/
def EventuallyConstantRecurrence (f : ℕ → ℝ) : Prop :=
  ∃ (d n₀ : ℕ) (c : Fin d → ℝ),
    0 < d ∧
      ∀ n : ℕ, n₀ ≤ n →
        f (n + d) = ∑ i : Fin d, c i * f (n + i)

/-- The boundary polynomial from the two-parameter PF₃ family. -/
def boundaryPolynomial (t : ℝ) (z : ℂ) : ℂ :=
  ((1 : ℂ) + 2 * (t : ℂ) * z + 2 * (t : ℂ) ^ 2 * z ^ 2) *
    ((1 : ℂ) + ((t : ℂ) ^ 3 / 8) * z)

/-- Its exact real Taylor coefficients. -/
def boundaryCoefficient (t : ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => 2 * t + t ^ 3 / 8
  | 2 => 2 * t ^ 2 + t ^ 4 / 4
  | 3 => t ^ 5 / 4
  | _ => 0

/-- The strictified entire function `exp (ε z) P_t(z)`. -/
def strictifiedFunction (t eps : ℝ) (z : ℂ) : ℂ :=
  Complex.exp ((eps : ℂ) * z) * boundaryPolynomial t z

/-- The exact coefficient convolution for `exp (ε z) P_t(z)`. -/
def strictifiedCoefficient (t eps : ℝ) (n : ℕ) : ℝ :=
  Finset.sum (Finset.range (n + 1)) (fun m =>
    boundaryCoefficient t m * eps ^ (n - m) /
      (Nat.factorial (n - m) : ℝ))

/-- The real value of the strictified family on the real axis. -/
def strictifiedRealValue (t eps x : ℝ) : ℝ :=
  Real.exp (eps * x) *
    ((1 + 2 * t * x + 2 * t ^ 2 * x ^ 2) * (1 + t ^ 3 * x / 8))

/-- The coefficient series is the displayed strictified entire function. -/
def StrictifiedEntire (t eps : ℝ) : Prop :=
  ∀ z : ℂ,
    HasSum
      (fun n : ℕ => (strictifiedCoefficient t eps n : ℂ) * z ^ n)
      (strictifiedFunction t eps z)

/-- Normalization, positivity, nonpolynomiality, entirety, and PF₃ for the
explicit strictified family. -/
def NormalizedPositiveNonpolynomialEntirePF3 (t eps : ℝ) : Prop :=
  strictifiedCoefficient t eps 0 = 1 ∧
    (∀ n : ℕ, 0 < strictifiedCoefficient t eps n) ∧
    ¬ EventuallyZeroCoefficients (strictifiedCoefficient t eps) ∧
    StrictifiedEntire t eps ∧
    PF3Sequence (strictifiedCoefficient t eps)

/-- Rank-three, shift-one deleted-row cofactors for the explicit family. -/
def strictifiedDelta (t eps : ℝ) (m : Fin 4) : ℝ :=
  endpointCofactor (strictifiedCoefficient t eps) 3 1 m

/-- The rank-three, shift-one endpoint gap. -/
def strictifiedEndpointGap (t eps : ℝ) : ℝ :=
  strictifiedDelta t eps 0 - ((1 : ℝ) / 4) * strictifiedDelta t eps 1

/-- The factorial-strength ultra-Turán inequalities used in the counterexample. -/
def StrictFactorialUltraTuran (t eps : ℝ) : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    strictifiedCoefficient t eps n ^ 2 >
      (((n + 1 : ℕ) : ℝ) / (n : ℝ)) *
        strictifiedCoefficient t eps (n - 1) *
        strictifiedCoefficient t eps (n + 1)

/-- The endpoint mass `δ = (1/4) a₁`. -/
def strictifiedEndpointMass (t eps : ℝ) : ℝ :=
  ((1 : ℝ) / 4) * strictifiedCoefficient t eps 1

/-- Continuity and sign persistence of the exact rank-three endpoint
cofactors under exponential strictification. -/
def Claim13086 : Prop :=
  ∀ t : ℝ, 0 < t →
    ContinuousAt (fun eps : ℝ => strictifiedEndpointGap t eps) 0 ∧
      (∀ m : Fin 4,
        ContinuousAt (fun eps : ℝ => strictifiedDelta t eps m) 0) ∧
      strictifiedEndpointGap t 0 < 0 ∧
      (∀ m : Fin 4, 0 < strictifiedDelta t 0 m) ∧
      (∃ η : ℝ, 0 < η ∧
        ∀ eps : ℝ, 0 < eps → eps < η →
          strictifiedEndpointGap t eps < 0 ∧
            (∀ m : Fin 4, 0 < strictifiedDelta t eps m))

/-- The explicit two-parameter family disproves rank-three endpoint
 dominance under the listed PF₃, ultra-Turán, and scalar-smallness premises. -/
def Claim13089 : Prop :=
  ∀ η : ℝ, 0 < η →
    ∃ t eps : ℝ,
      0 < t ∧ 0 < eps ∧
      NormalizedPositiveNonpolynomialEntirePF3 t eps ∧
      StrictFactorialUltraTuran t eps ∧
      let delta := strictifiedEndpointMass t eps
      delta = ((boundaryCoefficient t 1 + eps) / 4) ∧
        0 < delta ∧ delta < η ∧
        delta ^ 2 + delta < 1 ∧
        strictifiedRealValue t eps ((1 : ℝ) / 4) < 2 ∧
        strictifiedEndpointGap t eps < 0 ∧
        ¬ (0 < strictifiedEndpointGap t eps)

end MathlibPlus.Open.ResearchFormalization
