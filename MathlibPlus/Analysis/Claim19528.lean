import Mathlib

namespace MathlibPlus.Analysis.Claim19528

/-- Formalization of admitted claim 19528: the factorial-scaled generalized
Vandermonde determinant is positive at positive, strictly increasing nodes and
strictly increasing natural exponents. -/
def generalizedVandermondePoissonDeterminantPositive_claim19528 : Prop :=
  ∀ (d : ℕ) (hd : 0 < d) (q : Fin d → ℝ) (m : Fin d → ℕ),
    0 < q ⟨0, hd⟩ →
    StrictMono q →
    StrictMono m →
    0 < Matrix.det (fun i k : Fin d =>
      q i ^ (m k) / (Nat.factorial (m k) : ℝ))

end MathlibPlus.Analysis.Claim19528
