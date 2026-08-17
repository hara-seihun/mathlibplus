import Mathlib

namespace MathlibPlus.Open.ResearchFormalizationBatch019ffedd

noncomputable section

/-- The generalized even-monomial kernel from Claim 18525. -/
def generalizedEvenMonomialKernel (y : ℝ) (j : ℕ) : ℝ :=
  y ^ (2 * j) / (Nat.factorial (2 * j) : ℝ)

/-- Claim 18525: the generalized even-monomial kernel is strictly totally positive. -/
def claim18525 : Prop :=
  ∀ (r : ℕ), 0 < r →
    ∀ (y : Fin r → ℝ), (∀ i, 0 < y i) → StrictMono y →
      ∀ (d : Fin r → ℕ), StrictMono d →
        0 < Matrix.det (fun i j => generalizedEvenMonomialKernel (y i) (d j))

/-- Strict total positivity on ordered natural-number rows and columns. -/
def batchStrictTP (K : ℕ → ℕ → ℝ) : Prop :=
  ∀ (r : ℕ), 0 < r →
    ∀ (x d : Fin r → ℕ), StrictMono x → StrictMono d →
      0 < Matrix.det (fun i j => K (x i) (d j))

/-- Strict total positivity on ordered cuts and nonnegative radii. -/
def batchStrictEvaluationTP (K : ℕ → ℝ → ℝ) : Prop :=
  ∀ (r : ℕ), 0 < r →
    ∀ (x : Fin r → ℕ), StrictMono x →
      ∀ (z : Fin r → ℝ), (∀ i, 0 ≤ z i) → StrictMono z →
        0 < Matrix.det (fun i j => K (x i) (z j))

/-- The evaluation kernel in Claim 18528. -/
def batchEvaluationKernel (A : ℕ → ℕ → ℝ) (M : ℕ) (z : ℝ) : ℝ :=
  ∑' j : ℕ, A M j * z ^ (2 * j)

/-- Claim 18528: coefficient strict TP implies evaluation-kernel strict TP. -/
def claim18528 : Prop :=
  ∀ (A : ℕ → ℕ → ℝ), batchStrictTP A →
    batchStrictEvaluationTP (batchEvaluationKernel A)

/-- Claim 18543: the Laplace representation of the Borel-band kernel. -/
def claim18543 : Prop :=
  ∀ (a q u : ℝ), 0 < a → 0 < q → 0 < 1 + q * u →
    let ρ : ℝ := q⁻¹
    (1 + q * u) ^ (-a) =
      (ρ ^ a / Real.Gamma a) *
        ∫ v in Set.Ioi (0 : ℝ),
          v ^ (a - 1) * Real.exp (-ρ * v) * Real.exp (-u * v)

/-- Claim 18544: strict total positivity of the Borel-band kernel. -/
def claim18544 : Prop :=
  ∀ (a : ℝ), 0 < a →
    ∀ (r : ℕ), 0 < r →
      ∀ (q u : Fin r → ℝ),
        (∀ i, 0 < q i) →
        (∀ i j, i < j → q j < q i) →
        (∀ i, 0 < u i) →
        (∀ i j, i < j → u i < u j) →
          0 < Matrix.det (fun i j => (1 + q i * u j) ^ (-a))

/-- The Vandermonde factor used in Claim 18556. -/
def batchVandermonde {r : ℕ} (y : Fin r → ℝ) : ℝ :=
  ∏ i : Fin r, ∏ j : Fin r, if i < j then y j - y i else 1

/-- The elementary symmetric polynomial used in Claim 18556. -/
def batchElementarySymmetric {r : ℕ} (y : Fin r → ℝ) (k : ℕ) : ℝ :=
  ∑ S ∈ (Finset.univ : Finset (Finset (Fin r))).filter (fun S => S.card = k),
    ∏ i ∈ S, y i

/-- The exponents left after omitting s+r-k from the consecutive window. -/
def batchOmittedExponent (r s k : ℕ) (j : Fin r) : ℕ :=
  if j.val < r - k then s + j.val else s + j.val + 1

/-- Claim 18556: the omitted-column alternant identity. -/
def claim18556 : Prop :=
  ∀ (r s k : ℕ), k ≤ r →
    ∀ (y : Fin r → ℝ),
      Matrix.det (fun i j => y i ^ batchOmittedExponent r s k j) =
        batchVandermonde y * (∏ i : Fin r, y i) ^ s *
          batchElementarySymmetric y k

/-- The r-row minor of A used for c_{s,k}(J) in Claim 18557. -/
def batchWindowMinor {r : ℕ} (A : ℕ → Fin r → ℝ) (s k : ℕ) : ℝ :=
  Matrix.det (fun i j => A (batchOmittedExponent r s k i) j)

/-- The consecutive-window Cauchy--Binet circuit block. -/
def batchCircuitBlock {r : ℕ} (A : ℕ → Fin r → ℝ) (y : Fin r → ℝ) (s : ℕ) : ℝ :=
  (Finset.range (r + 1)).sum (fun k =>
    Matrix.det (fun i j => y i ^ batchOmittedExponent r s k j) *
      batchWindowMinor A s k)

/-- Claim 18557: the consecutive-window Cauchy--Binet circuit identity. -/
def claim18557 : Prop :=
  ∀ {r : ℕ} (A : ℕ → Fin r → ℝ) (y : Fin r → ℝ) (s : ℕ),
    batchCircuitBlock A y s =
      batchVandermonde y * (∏ i : Fin r, y i) ^ s *
        (Finset.range (r + 1)).sum (fun k =>
          batchWindowMinor A s k * batchElementarySymmetric y k)

/-- The reciprocal two-sheet point kernel from Claims 18567--18568. -/
def reciprocalTwoSheetKernel (q u : ℝ) : ℝ :=
  Real.exp (-5 * u / 2 - q * Real.exp (-2 * u)) +
    Real.exp (5 * u / 2 - q * Real.exp (2 * u))

/-- The mixed logarithmic derivative of that kernel. -/
def reciprocalMixedLogDerivative (q u : ℝ) : ℝ :=
  deriv (fun q' : ℝ =>
    deriv (fun u' : ℝ => Real.log (reciprocalTwoSheetKernel q' u')) u) q

/-- Claim 18567: positivity of the reciprocal kernel's mixed logarithmic derivative. -/
def claim18567 : Prop :=
  ∀ (q u : ℝ), Real.pi ≤ q → 0 < u →
    0 < reciprocalMixedLogDerivative q u

/-- Claim 18568: global strict TP2 of the reciprocal two-sheet kernel. -/
def claim18568 : Prop :=
  ∀ (q₁ q₂ u₁ u₂ : ℝ),
    Real.pi ≤ q₁ → q₁ < q₂ → 0 ≤ u₁ → u₁ < u₂ →
      0 < reciprocalTwoSheetKernel q₁ u₁ * reciprocalTwoSheetKernel q₂ u₂ -
        reciprocalTwoSheetKernel q₁ u₂ * reciprocalTwoSheetKernel q₂ u₁

/-- The hyperbolic-cosine kernel from Claim 18570. -/
def hyperbolicCosineKernel (u z : ℝ) : ℝ := Real.cosh (u * z)

/-- Its mixed logarithmic derivative. -/
def hyperbolicCosineMixedLogDerivative (u z : ℝ) : ℝ :=
  deriv (fun u' : ℝ =>
    deriv (fun z' : ℝ => Real.log (hyperbolicCosineKernel u' z')) z) u

/-- Claim 18570: strict TP2, its mixed derivative formula, and boundary strictness. -/
def claim18570 : Prop :=
  (∀ (u z : ℝ), 0 < u → 0 < z →
    hyperbolicCosineMixedLogDerivative u z =
        Real.tanh (u * z) + (u * z) / Real.cosh (u * z) ^ 2 ∧
      0 < hyperbolicCosineMixedLogDerivative u z) ∧
  (∀ (u₁ u₂ z₁ z₂ : ℝ),
    0 < u₁ → u₁ < u₂ → 0 < z₁ → z₁ < z₂ →
      0 < hyperbolicCosineKernel u₁ z₁ * hyperbolicCosineKernel u₂ z₂ -
        hyperbolicCosineKernel u₁ z₂ * hyperbolicCosineKernel u₂ z₁) ∧
  (∀ (u₁ u₂ z₂ : ℝ),
    0 < u₁ → u₁ < u₂ → 0 < z₂ →
      0 < hyperbolicCosineKernel u₁ 0 * hyperbolicCosineKernel u₂ z₂ -
        hyperbolicCosineKernel u₁ z₂ * hyperbolicCosineKernel u₂ 0)

end

end MathlibPlus.Open.ResearchFormalizationBatch019ffedd
