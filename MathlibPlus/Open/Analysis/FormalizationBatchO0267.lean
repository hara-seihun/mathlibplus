import MathlibPlus.Open.Analysis.FormalizationBatch

open scoped BigOperators

noncomputable section

namespace MathlibPlus.Open.Analysis.FormalizationBatchO0267

/-- The cardinal-sine coefficient of evaluation at a complex point, with its
removable value retained at an integer sample. -/
noncomputable def pwCardinalSine (z : ℂ) (n : ℤ) : ℂ :=
  if z = (n : ℂ) then 1 else
    Complex.sin (Complex.ofReal Real.pi * (z - (n : ℂ))) /
      (Complex.ofReal Real.pi * (z - (n : ℂ)))

/-- The diagonal of the reproducing kernel in the Shannon-coordinate
normalization: it is the squared norm of the evaluation coefficient vector. -/
noncomputable def pwEvaluationKernelDiagonal (z : ℂ) : ℝ :=
  ∑' n : ℤ, ‖pwCardinalSine z n‖ ^ 2

/-- Claim 15160: the squared norm of complex evaluation has the packet's
continuous normalization. -/
def claim15160_evaluation_norm_identity : Prop :=
  ∀ x y : ℝ,
    pwEvaluationKernelDiagonal (Complex.ofReal x + Complex.ofReal y * Complex.I) =
      FormalizationBatch.normalizedSineDenominator y

/-- The center of the anchored block of samples 0,...,M-1. -/
noncomputable def anchorCenter (M : ℕ) : ℝ :=
  ((M : ℝ) - 1) / 2

/-- An exterior integer sample index for the anchored block. -/
def exteriorInteger (M : ℕ) (n : ℤ) : Prop :=
  n < 0 ∨ (M : ℤ) ≤ n

/-- The order-ell term in the centered exterior denominator expansion. -/
noncomputable def exteriorExpansionSummand (M : ℕ) (z : ℂ) (n : ℤ)
    (ell : ℕ) : ℂ :=
  -((z - (anchorCenter M : ℂ)) ^ ell) /
    ((anchorCenter M : ℂ) - (n : ℂ)) ^ (ell + 1)

/-- The remainder in the centered exterior denominator expansion. -/
noncomputable def exteriorExpansionRemainder (M r : ℕ) (z : ℂ) (n : ℤ) : ℂ :=
  (-(z - (anchorCenter M : ℂ))) ^ r /
    (((anchorCenter M : ℂ) - (n : ℂ)) ^ r * (z - (n : ℂ)))

/-- The displayed denominator expansion, with the necessary exclusion of its
pole made explicit. -/
def claim15163_denominator_expansion : Prop :=
  ∀ (M : ℕ) (n : ℤ), exteriorInteger M n →
    ∀ (r : ℕ) (z : ℂ), z ≠ (n : ℂ) →
      1 / (z - (n : ℂ)) =
        (∑ ell ∈ Finset.range r, exteriorExpansionSummand M z n ell) +
          exteriorExpansionRemainder M r z n

/-- The left exterior tail. -/
def leftExteriorIndex : Type := {n : ℤ // n < 0}

/-- The right exterior tail. -/
def rightExteriorIndex (M : ℕ) : Type := {n : ℤ // (M : ℤ) ≤ n}

/-- The two exterior tails as one column index type. -/
def exteriorIndex (M : ℕ) : Type :=
  leftExteriorIndex ⊕ rightExteriorIndex M

/-- The normalized, order-r exterior Cauchy kernel obtained by truncating the
centered denominator expansion. -/
noncomputable def exteriorTruncationKernel (M r : ℕ) (z : ℂ) (n : ℤ) : ℂ :=
  FormalizationBatch.normalizedRowFactor z / Complex.ofReal Real.pi *
    (∑ ell ∈ Finset.range r, exteriorExpansionSummand M z n ell)

/-- A truncated left-tail column on a finite list of evaluation rows. -/
noncomputable def leftTruncationColumn (M r N : ℕ) (nodes : Fin N → ℂ)
    (n : leftExteriorIndex) : Fin N → ℂ :=
  fun j => exteriorTruncationKernel M r (nodes j) n.1

/-- A truncated right-tail column on a finite list of evaluation rows. -/
noncomputable def rightTruncationColumn (M r N : ℕ) (nodes : Fin N → ℂ)
    (n : rightExteriorIndex M) : Fin N → ℂ :=
  fun j => exteriorTruncationKernel M r (nodes j) n.1

/-- The combined left/right truncated exterior column family. -/
noncomputable def exteriorTruncationColumn (M r N : ℕ) (nodes : Fin N → ℂ)
    (n : exteriorIndex M) : Fin N → ℂ :=
  match n with
  | Sum.inl n => leftTruncationColumn M r N nodes n
  | Sum.inr n => rightTruncationColumn M r N nodes n

/-- Claim 15163's rank assertion for both exterior tails. -/
def claim15163_truncation_rank : Prop :=
  ∀ (M r N : ℕ) (nodes : Fin N → ℂ),
    Module.finrank ℂ
        (Submodule.span ℂ (Set.range (leftTruncationColumn M r N nodes))) ≤ r ∧
      Module.finrank ℂ
        (Submodule.span ℂ (Set.range (rightTruncationColumn M r N nodes))) ≤ r ∧
      Module.finrank ℂ
        (Submodule.span ℂ (Set.range (exteriorTruncationColumn M r N nodes))) ≤ 2 * r

/-- Claim 15163: the centered exterior denominator expansion and the resulting
rank at most 2r after the left and right tails are truncated separately. -/
def claim15163_exterior_expansion_and_rank : Prop :=
  claim15163_denominator_expansion ∧ claim15163_truncation_rank

end MathlibPlus.Open.Analysis.FormalizationBatchO0267
