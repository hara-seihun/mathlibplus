import MathlibPlus.Open.ResearchFormalization.R0498
import MathlibPlus.Open.Research.FormalizationBatch

namespace MathlibPlus.Open.ResearchFormalization.R0498

open scoped BigOperators
noncomputable section

open MathlibPlus.Open.Research.FormalizationBatch

/-- The positive-factor ceiling formula used at `ell = 3`. -/
def threeFactorCeilingU (ell N : ℕ) : ℕ :=
  1 +
      ∑ a ∈ Finset.Icc 1 (((ell + 1) / 2) - 1),
        (N + 1 - 2 * a) +
    if Even ell then ((N + 2) / 2 - ell / 2) else 0

/-- The coefficient vector of `q^a + q^b + q^c` on the exact finite domain
`{0, ..., N}`. -/
def threeTermCoefficientVector (N : ℕ) (t : ThreePart N) : Fin (N + 1) → ℚ :=
  fun j => ∑ i : Fin 3, if (t.1 i).val = j.val then 1 else 0

/-- The span of all three-term coefficient vectors of total `N`. -/
def threeTermCoefficientSpan (N : ℕ) :
    Submodule ℚ (Fin (N + 1) → ℚ) :=
  Submodule.span ℚ (Set.range (threeTermCoefficientVector N))

/-- The affine moment functional dual to the three-factor span. -/
def threeTermAffineMoment (N : ℕ) (v : Fin (N + 1) → ℚ) : ℚ :=
  ∑ j : Fin (N + 1), ((j.val : ℚ) - (N : ℚ) / 3) * v j

/-- Claim 29364: exact three-factor attainment together with the
codimension-one affine-moment hyperplane. -/
def exactThreeFactorAttainment : Prop :=
  fixedTotalFactorProductSpanDimension 3 0 = 1 ∧
  ∀ N : ℕ, 1 ≤ N →
    fixedTotalFactorProductSpanDimension 3 N = N ∧
      N = threeFactorCeilingU 3 N ∧
      (∀ v : Fin (N + 1) → ℚ,
        v ∈ threeTermCoefficientSpan N ↔ threeTermAffineMoment N v = 0) ∧
      Module.finrank ℚ (threeTermCoefficientSpan N) = N

end

end MathlibPlus.Open.ResearchFormalization.R0498
