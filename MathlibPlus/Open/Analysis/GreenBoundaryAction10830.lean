import MathlibPlus.Open.Analysis.PairedBulkFormalization

namespace MathlibPlus.Open.Analysis.GreenBoundaryAction10830

noncomputable section

/-- The two positive Green eigenvalues in the boundary convolution formula. -/
def boundaryAlpha (a : ℝ) : ℝ := a ^ 2 - (1 / 4 : ℝ)
def boundaryBeta (b : ℝ) : ℝ := b ^ 2 - (1 / 4 : ℝ)

/-- The leading term in the `m`-fold Green iterate of the boundary convolution. -/
def boundaryGreenMainTerm (a b : ℝ) (m : ℕ) (u : ℝ) : ℝ :=
  boundaryAlpha a ^ m * pairedBoundaryConvolution a b u

/-- The `j`th displayed summand in the finite Green-iterate formula. -/
def boundaryGreenSummand (a b : ℝ) (m j : ℕ) (u : ℝ) : ℝ :=
  boundaryAlpha a ^ (m - 1 - j) * boundaryBeta b ^ j * sinhKernel b u

/-- Iterated Green action on the exact boundary convolution, including the
positivity of every displayed term and derivative and the commutator action. -/
def iteratedGreenBoundaryAction : Prop :=
  ∀ (a b : ℝ) (u : ℝ) (m : ℕ),
    (1 / 2 : ℝ) < a →
    (1 / 2 : ℝ) < b →
    0 < u →
    greenLIterate m (fun x : ℝ => pairedBoundaryConvolution a b x) u =
        boundaryGreenMainTerm a b m u +
          (∑ j ∈ Finset.range m, boundaryGreenSummand a b m j u) ∧
      0 < greenLIterate m (fun x : ℝ => pairedBoundaryConvolution a b x) u ∧
      0 < deriv (greenLIterate m (fun x : ℝ => pairedBoundaryConvolution a b x)) u ∧
      0 < pairedBoundaryConvolution a b u ∧
      0 < deriv (fun x : ℝ => pairedBoundaryConvolution a b x) u ∧
      0 < sinhKernel b u ∧
      0 < deriv (sinhKernel b) u ∧
      0 < boundaryGreenMainTerm a b m u ∧
      0 < deriv (fun x : ℝ => boundaryGreenMainTerm a b m x) u ∧
      (∀ j : ℕ, j ∈ Finset.range m →
        0 < boundaryGreenSummand a b m j u ∧
        0 < deriv (fun x : ℝ => boundaryGreenSummand a b m j x) u) ∧
      0 < greenLIterate m (fun x : ℝ => x * pairedBoundaryConvolution a b x) u ∧
      (1 ≤ m →
        0 < deriv (greenLIterate (m - 1)
          (fun x : ℝ => pairedBoundaryConvolution a b x)) u ∧
        greenLIterate m (fun x : ℝ => x * pairedBoundaryConvolution a b x) u =
            u * greenLIterate m (fun x : ℝ => pairedBoundaryConvolution a b x) u +
              2 * (m : ℝ) *
                deriv (greenLIterate (m - 1)
                  (fun x : ℝ => pairedBoundaryConvolution a b x)) u)

end

end MathlibPlus.Open.Analysis.GreenBoundaryAction10830
