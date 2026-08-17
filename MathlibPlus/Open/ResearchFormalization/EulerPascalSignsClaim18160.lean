import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.BatchR0131

noncomputable section

/-- The positive subset weight in the Euler--Pascal elementary-symmetric array.
The index set is the explicit list `1/2,1/4,...,1/(2(m-1))`. -/
def eulerPascalSubsetWeight (_m : ℕ) (s : Finset ℕ) : ℝ :=
  ∏ r ∈ s, (1 / (((2 * (r + 1) : ℕ) : ℝ)))

/-- The elementary symmetric sum in the displayed positive Euler entries. -/
def eulerPascalElementarySymmetric (m k : ℕ) : ℝ :=
  ∑ s ∈ (Finset.range (m - 1)).powerset,
    if s.card = k then eulerPascalSubsetWeight m s else 0

/-- The Euler--Pascal factor `E_(m,l)`.  The zero branch records that only
positive `m,l` are meaningful; the elementary-symmetric sum itself vanishes
outside its finite degree range. -/
def eulerPascalFactor (m l : ℕ) : ℝ :=
  if 0 < m ∧ 0 < l then
    (1 / (((2 * m : ℕ) : ℝ))) *
      eulerPascalElementarySymmetric m (l - 1)
  else 0

/-- The sparse terminal convolution `C_(l,j) = 2 mu_(2j-l)`. -/
def eulerPascalTerminalConvolution (μ : ℕ → ℝ) (l j : ℕ) : ℝ :=
  if 0 < l ∧ l ≤ 2 * j then 2 * μ (2 * j - l) else 0

/-- The Taylor coefficient array obtained by the Euler--Pascal factor followed
by the sparse terminal convolution. -/
def eulerPascalTaylorArray (μ : ℕ → ℝ) (m j : ℕ) : ℝ :=
  ∑ l ∈ Finset.range (2 * j),
    eulerPascalFactor m (l + 1) *
      eulerPascalTerminalConvolution μ (l + 1) j

/-- Claim 18160: the Euler--Pascal factor has nonnegative entries (with an
explicit positive subset/path-weight representation), and in the exact
factorization `A = E C` all sign-bearing data occur in the terminal `mu`
convolution. -/
def allSignsLocalizedInEulerPascalTerminalConvolution_claim18160 : Prop :=
  ∀ μ : ℕ → ℝ,
    (∀ m l : ℕ, 0 ≤ eulerPascalFactor m l) ∧
      (∀ m : ℕ, ∀ s : Finset ℕ,
        s ⊆ Finset.range (m - 1) →
          0 < eulerPascalSubsetWeight m s) ∧
      (∀ m j : ℕ,
        eulerPascalTaylorArray μ m j =
          ∑ l ∈ Finset.range (2 * j),
            eulerPascalFactor m (l + 1) *
              eulerPascalTerminalConvolution μ (l + 1) j) ∧
      (∀ m j : ℕ,
        eulerPascalTaylorArray μ m j =
          2 * ∑ l ∈ Finset.range (2 * j),
            eulerPascalFactor m (l + 1) * μ (2 * j - (l + 1)))

end

end MathlibPlus.Open.ResearchFormalization.BatchR0131
