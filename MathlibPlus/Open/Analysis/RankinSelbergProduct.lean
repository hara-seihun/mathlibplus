import Mathlib

namespace MathlibPlus.Open.Analysis

/-- The complementary divisor character used by the global Rankin--Selberg series. -/
noncomputable def complementaryDivisorCharacter (r : ℝ) (n : ℕ) : ℝ :=
  if 0 < n then
    (Finset.sum n.divisors (fun d =>
      Real.rpow ((d : ℝ) / ((n / d : ℕ) : ℝ)) r))
  else 0

/-- The complementary Rankin--Selberg Dirichlet series, indexed by positive naturals. -/
noncomputable def complementaryRankinSelbergSeries (s : ℂ) (r t : ℝ) : ℂ :=
  ∑' n : {n : ℕ // 0 < n},
    (complementaryDivisorCharacter r n.1 : ℂ) *
      (complementaryDivisorCharacter t n.1 : ℂ) *
        Complex.cpow (n.1 : ℂ) (-s)

/-- Global complementary Rankin--Selberg product. -/
def globalComplementaryRankinSelbergProduct : Prop :=
  ∀ (R : ℝ) (s : ℂ) (r t : ℝ),
    0 ≤ R → |r| ≤ R → |t| ≤ R → 1 + 2 * R < s.re →
      complementaryRankinSelbergSeries s r t =
        (riemannZeta (s + (r : ℂ) + (t : ℂ)) *
          riemannZeta (s + (r : ℂ) - (t : ℂ)) *
          riemannZeta (s - (r : ℂ) + (t : ℂ)) *
          riemannZeta (s - (r : ℂ) - (t : ℂ))) /
            riemannZeta (2 * s)

end MathlibPlus.Open.Analysis
