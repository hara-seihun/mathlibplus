import Mathlib
import MathlibPlus.Analysis.ReciprocalXi

namespace MathlibPlus.Open.ResearchFormalization.C0185

noncomputable section
open scoped BigOperators
open MathlibPlus.Analysis.ReciprocalXi

/-- The exact cutoff-specific model function from Claim 2745. -/
noncomputable def exactCutoffSpecificModelFunction_claim2745
    (P : Polynomial ℝ) (t : ℂ) : ℂ :=
  xi ((1 / 2 : ℂ) + Complex.I * t) /
      (2 * (Real.pi : ℂ)) * Complex.exp
        (-(0.015169226266280162 : ℂ) * t ^ 4) *
      (Polynomial.map (algebraMap ℝ ℂ) P).eval
        (t ^ 2 / (Real.sqrt 40 : ℂ)) -
    (690.225171612913413810019847006 : ℂ) /
      (2 * Complex.exp (100 : ℂ)) *
      (t * Complex.sin (40 * t) - (1 / 2 : ℂ) * Complex.cos (40 * t)) /
        (t ^ 2 + 1 / 4)

/-- The baseline quadratic profile. -/
def baselineProfile : Polynomial ℝ :=
  1 + Polynomial.C (-0.8824739608624199 : ℝ) * Polynomial.X +
    Polynomial.C 2.816598275979663 * Polynomial.X ^ 2

/-- The degree-twelve repaired profile, independently recorded from its exact
coefficient table. -/
def repairedProfile : Polynomial ℝ :=
  1 + Polynomial.C (-0.8824739608624199 : ℝ) * Polynomial.X +
    Polynomial.C 2.816598275979663 * Polynomial.X ^ 2 +
    Polynomial.C (-0.291823441775511462704736925086 : ℝ) * Polynomial.X ^ 7 +
    Polynomial.C (0.123027643379614215971149239916 : ℝ) * Polynomial.X ^ 8 +
    Polynomial.C (-0.0207839545323778109243242278602 : ℝ) * Polynomial.X ^ 9 +
    Polynomial.C (0.00175879823818437519844298958496 : ℝ) * Polynomial.X ^ 10 +
    Polynomial.C (-0.0000745504928632908194611477445219 : ℝ) * Polynomial.X ^ 11 +
    Polynomial.C (0.00000126611934386230650140945434773 : ℝ) * Polynomial.X ^ 12

/-- The degree-seven-through-twelve correction coefficient table. -/
def repairCoefficient : Fin 6 → ℝ :=
  ![-0.291823441775511462704736925086,
    0.123027643379614215971149239916,
    -0.0207839545323778109243242278602,
    0.00175879823818437519844298958496,
    -0.0000745504928632908194611477445219,
    0.00000126611934386230650140945434773]

def repairDegree (j : Fin 6) : ℕ := j.1 + 7

/-- The coefficient-root envelope used in the C-0185 certificate. -/
def coefficientRootSet (P : Polynomial ℝ) : Set ℝ :=
  {r | ∃ j ∈ P.support, 0 < j ∧
    r = Real.rpow |P.coeff j| (1 / (j : ℝ))}

noncomputable def coefficientRootBound (P : Polynomial ℝ) : ℝ :=
  max 1 (sSup (coefficientRootSet P))

/-- Claim 2746: the repaired profile has degree twelve and is the baseline
profile plus the displayed correction beginning at degree seven. -/
def lowModePreservingDegreeTwelveProfile_claim2746 : Prop :=
  repairedProfile.natDegree = 12 ∧
    repairedProfile =
      baselineProfile +
        Polynomial.C (-0.291823441775511462704736925086 : ℝ) * Polynomial.X ^ 7 +
        Polynomial.C (0.123027643379614215971149239916 : ℝ) * Polynomial.X ^ 8 +
        Polynomial.C (-0.0207839545323778109243242278602 : ℝ) * Polynomial.X ^ 9 +
        Polynomial.C (0.00175879823818437519844298958496 : ℝ) * Polynomial.X ^ 10 +
        Polynomial.C (-0.0000745504928632908194611477445219 : ℝ) * Polynomial.X ^ 11 +
        Polynomial.C (0.00000126611934386230650140945434773 : ℝ) * Polynomial.X ^ 12

/-- Claim 2749: the repair preserves the exact coefficient-root bound and
all six added coefficient roots lie below 0.839. -/
def repairIntroducesNoCoefficientRootGrowth_claim2749 : Prop :=
  coefficientRootBound repairedProfile = coefficientRootBound baselineProfile ∧
    coefficientRootBound baselineProfile = Real.sqrt 2.816598275979663 ∧
    ∀ j : Fin 6,
      Real.rpow |repairCoefficient j|
          (1 / (repairDegree j : ℝ)) < 0.839

end
end MathlibPlus.Open.ResearchFormalization.C0185
