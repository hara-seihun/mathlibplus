import MathlibPlus.Algebra.Claim16416

namespace MathlibPlus.Open.ResearchFormalization.Q0064Wronskian

noncomputable section

open MathlibPlus.Algebra.Claim16416

/-- The target first-shell sequence, using the reviewed exact transform of
`generalizedBell`. -/
def Q (n : ℕ) : Polynomial ℚ :=
  ((2 : ℚ) ^ (n + 1) * (-1 : ℚ) ^ n) • generalizedBell (n + 1)

def W (r : ℕ) : Polynomial ℚ :=
  Matrix.det (fun (i j : Fin r) => Q (2 * (i : ℕ) + (j : ℕ)))

def normalizedWronskian (r : ℕ) : Prop :=
  ∃ P : Polynomial ℚ,
    W r = Polynomial.X ^ (r * (r - 1) / 2) * P

/-- Claim 16419: the determinant of the displayed finite Q-matrix has the
stated power of `y` and a polynomial remainder; no unsupported monicity is
added. -/
def claim16419_wronskianNormalizedPolynomial : Prop :=
  ∀ r : ℕ, 1 ≤ r → normalizedWronskian r

end

end MathlibPlus.Open.ResearchFormalization.Q0064Wronskian
