import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.ChebyshevBarycentric15445

noncomputable section
open Classical

/-- Claim 15445: the alternating Lagrange interpolant has the stated
barycentric leading-coefficient magnitude, and Chebyshev extremality gives
its sharp interval-scaled lower bound. -/
def chebyshevBarycentricLeadingCoefficientBound : Prop :=
  ∀ (n : ℕ),
    1 ≤ n →
    ∀ (S : ℝ) (t : Fin (n + 1) → ℝ),
      0 < S →
      StrictMono t →
      (∃ a : ℝ, ∀ j : Fin (n + 1), t j ∈ Set.Icc a (a + S)) →
      let s : Finset (Fin (n + 1)) := Finset.univ
      let P : Polynomial ℝ :=
        Lagrange.interpolate s t (fun j : Fin (n + 1) => (-1 : ℝ) ^ j.1)
      let Q : Polynomial ℝ := Lagrange.nodal s t
      P.natDegree ≤ n ∧
        (∀ j : Fin (n + 1), P.eval (t j) = (-1 : ℝ) ^ j.1) ∧
        |P.leadingCoeff| =
          ∑ j : Fin (n + 1),
            1 / |(Polynomial.derivative Q).eval (t j)| ∧
        (∑ j : Fin (n + 1),
            1 / |(Polynomial.derivative Q).eval (t j)|) ≥
          (2 : ℝ) ^ (2 * n - 1) / S ^ n

end

end MathlibPlus.Open.ResearchFormalization.ChebyshevBarycentric15445
