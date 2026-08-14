import Mathlib

namespace MathlibPlus.Open.Q0069

open Filter
open scoped Topology

/-- The bilateral Toeplitz matrix of a two-sided real sequence. -/
def bilateralToeplitz (s : ℤ → ℝ) : Matrix ℤ ℤ ℝ :=
  fun i j => s (j - i)

/-- Total nonnegativity of the bilateral Toeplitz matrix. -/
def bilateralToeplitzTN (s : ℤ → ℝ) : Prop :=
  ∀ (n : ℕ) (I J : Fin n → ℤ),
    StrictMono I →
    StrictMono J →
    0 ≤ Matrix.det (fun i j => bilateralToeplitz s (I i) (J j))

/-- Strict total positivity of the bilateral Toeplitz matrix. -/
def bilateralToeplitzTP (s : ℤ → ℝ) : Prop :=
  ∀ (n : ℕ) (I J : Fin n → ℤ),
    StrictMono I →
    StrictMono J →
    0 < Matrix.det (fun i j => bilateralToeplitz s (I i) (J j))

/-- A two-sided Pólya-frequency sequence, expressed by its Toeplitz minors. -/
def twoSidedPF (s : ℤ → ℝ) : Prop :=
  bilateralToeplitzTN s

/-- A strictly totally positive two-sided Pólya-frequency sequence. -/
def strictTwoSidedPF (s : ℤ → ℝ) : Prop :=
  bilateralToeplitzTP s

/-- Claim 16523: every two-sided Pólya-frequency sequence is a pointwise
limit of strictly totally positive Pólya-frequency sequences. -/
def claim_16523 : Prop :=
  ∀ (s : ℤ → ℝ),
    twoSidedPF s →
    ∃ (sₙ : ℕ → ℤ → ℝ),
      (∀ n, strictTwoSidedPF (sₙ n)) ∧
      (∀ k : ℤ, Filter.Tendsto (fun n => sₙ n k) atTop (𝓝 (s k)))

end MathlibPlus.Open.Q0069
