import MathlibPlus.Open.Research.BellCanonicalBatch

namespace MathlibPlus.Open.ResearchFormalization.O0091Claim13484

noncomputable section

abbrev BellBigMatrix := MathlibPlus.Open.Research.BellBigMatrix

def canonicalAtGauge (x g : ℝ) : BellBigMatrix :=
  MathlibPlus.Open.Research.qMatrix x g (MathlibPlus.Open.Research.tStar x g)

/-- The spectrum is asserted for the actual compact partial transpose of the
 canonical Gram matrix at the unique gauge, rather than for a separately
 stipulated diagonal surrogate. -/
def claim13484 : Prop :=
  ∀ x g : ℝ, 0 ≤ x →
    (∀ z : ℂ,
      MathlibPlus.Open.Research.eigenvalue
          (MathlibPlus.Open.Research.compactPartialTranspose
            (canonicalAtGauge x g)) z ↔
        z = (((x +
              |MathlibPlus.Open.Research.rhoOf x g| * (4 + x)) / 4 : ℝ) : ℂ) ∨
        z = (((x -
              |MathlibPlus.Open.Research.rhoOf x g| * (4 + x)) / 4 : ℝ) : ℂ) ∨
        z = ((((4 + x) +
              |MathlibPlus.Open.Research.rhoOf x g| * x) / 4 : ℝ) : ℂ) ∨
        z = ((((4 + x) -
              |MathlibPlus.Open.Research.rhoOf x g| * x) / 4 : ℝ) : ℂ)) ∧
      (∀ h : x ≤ 1,
        MathlibPlus.Open.Research.positiveSemidefiniteComplex
            (MathlibPlus.Open.Research.compactPartialTranspose
              (canonicalAtGauge x g)) ↔
          |MathlibPlus.Open.Research.rhoOf x g| ≤ x / (4 + x))

end

end MathlibPlus.Open.ResearchFormalization.O0091Claim13484
