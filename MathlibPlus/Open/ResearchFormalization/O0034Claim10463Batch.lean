import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.O0034Claim10463

noncomputable section

/-- The code-zeta coordinate `T=q^(-s)` on the real line, using the
positive-real power convention. -/
def codeZetaCoordinate_10463 (q : ℕ) (s : ℝ) : ℝ :=
  Real.rpow (q : ℝ) (-s)

/-- The displayed code-zeta denominator `(1-T)(1-qT)`. -/
def codeZetaDenominator_10463 (q : ℕ) (s : ℝ) : ℝ :=
  (1 - codeZetaCoordinate_10463 q s) *
    (1 - (q : ℝ) * codeZetaCoordinate_10463 q s)

/-- The negative-even part `-2,-4,...` of the real-Gamma pole tower. -/
def realGammaNegativeEvenPole_10463 (n : ℕ) : ℝ :=
  -((2 : ℝ) * (n + 1))

/-- Claim 10463: the code denominator stays regular on the negative-even
real-Gamma pole tower, and its displayed q=2, s=-2 specialization is 21
rather than a pole. -/
def codeZetaDenominatorMissesGammaPoleTower_claim10463_batch : Prop :=
  (∀ q : ℕ, 1 < q →
    ∀ n : ℕ,
      codeZetaDenominator_10463 q (realGammaNegativeEvenPole_10463 n) ≠ 0) ∧
  let q : ℕ := 2
  let s : ℝ := -2
  let T : ℝ := codeZetaCoordinate_10463 q s
  T = 4 ∧
    1 - T = -3 ∧
    1 - (q : ℝ) * T = -7 ∧
    codeZetaDenominator_10463 q s = 21 ∧
    codeZetaDenominator_10463 q s ≠ 0

end
end MathlibPlus.Open.ResearchFormalization.O0034Claim10463
