import Mathlib

namespace MathlibPlus.Open.Combinatorics.Claim7513

/-- Claim 7513: for every positive load, the fold types `(w, s)` with
`2 * w + s = ell` are counted by `floor (ell / 2) + 1`. -/
def scarweaveLoadResolutionCountClaim7513 : Prop :=
  ∀ ell : ℕ, 0 < ell →
    (Finset.filter (fun p : ℕ × ℕ => 2 * p.1 + p.2 = ell)
      (Finset.product (Finset.range (ell + 1)) (Finset.range (ell + 1)))).card =
      ell / 2 + 1

end MathlibPlus.Open.Combinatorics.Claim7513
