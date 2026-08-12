import Mathlib

namespace MathlibPlus.Combinatorics.Claim5281

/-- Positive ordered two-part decompositions of a natural number. -/
def decomp (n : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 n).product (Finset.Icc 1 n)).filter (fun p => p.1 + p.2 = n)

/-- The support of `(barDelta ⊗ 1) barDelta (e_ell)`. -/
def left (ell : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (decomp ell).biUnion (fun p =>
    (decomp p.1).biUnion (fun q => {(q.1, q.2, p.2)}))

/-- The support of `(1 ⊗ barDelta) barDelta (e_ell)`. -/
def right (ell : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (decomp ell).biUnion (fun p =>
    (decomp p.2).biUnion (fun q => {(p.1, q.1, q.2)}))

/--
The two reduced edge-deconcatenation orders enumerate the same ordered
positive triples, hence have the same support.
-/
theorem coassociative (ell : ℕ) : left ell = right ell := by
  ext x
  rcases x with ⟨i, j, k⟩
  simp [left, right, decomp]
  omega

end MathlibPlus.Combinatorics.Claim5281
