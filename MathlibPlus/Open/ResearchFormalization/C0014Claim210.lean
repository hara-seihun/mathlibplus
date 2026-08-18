import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.C0014Claim210

/-- The exact order-three confluent negative-Loewner determinant polynomial,
with h₁ through h₅ standing for the five successive derivatives. -/
def claim210 : Prop :=
  ∀ (h1 h2 h3 h4 h5 : ℝ),
    8640 * Matrix.det !![-h1, h2 / 2, -h3 / 6;
                         h2 / 2, -h3 / 6, h4 / 24;
                         -h3 / 6, h4 / 24, -h5 / 120] =
      -12 * h1 * h3 * h5 + 15 * h1 * h4 ^ 2 + 18 * h2 ^ 2 * h5 -
        60 * h2 * h3 * h4 + 40 * h3 ^ 3

end MathlibPlus.Open.ResearchFormalization.C0014Claim210
