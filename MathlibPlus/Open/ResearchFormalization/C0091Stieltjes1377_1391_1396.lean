import Mathlib
import MathlibPlus.Open.Analysis.Stieltjes1378
import MathlibPlus.Open.Analysis.Stieltjes1390

noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.C0091

open Filter Topology
open MathlibPlus.Open.Analysis

/-- Claim 1377: the authoritative Stieltjes Laurent convention, the
pole-cancelled derivative, and the alpha normalization. -/
def stieltjesConventionAndPoleCancelledDerivative : Prop :=
  stieltjesContext ∧
    (∀ t : ℝ, 0 < t →
      stieltjesZ t =
        (deriv riemannZeta (1 + (t : ℂ))).re + 1 / t ^ 2) ∧
    stieltjesAlpha = -stieltjesConstants 1

/-- The lower fixed-template predicate with the source's `s-1` coordinate. -/
def lowerTemplateAdmissible (C : ℝ) : Prop :=
  ∀ s : ℝ, 1 < s → C / s ^ 2 < stieltjesZ (s - 1)

/-- Claim 1391: the lower-template numerator has supremum alpha, with the
full sufficiently-near-one failure for every larger numerator. -/
def lowerTemplateNumeratorSharpness : Prop :=
  differentiatedStieltjesLaurentSeries ∧
    sSup {C : ℝ | lowerTemplateAdmissible C} = stieltjesAlpha ∧
      lowerTemplateAdmissible stieltjesAlpha ∧
        ∀ C : ℝ, stieltjesAlpha < C →
          ∃ ε : ℝ, 0 < ε ∧
            ∀ t : ℝ, 0 < t → t < ε →
              ¬ (C / (1 + t) ^ 2 < stieltjesZ t)

/-- The exact gamma-ratio parameters for the stronger Stieltjes rational
envelopes. -/
def stieltjesBeta : ℝ :=
  stieltjesConstants 2 / stieltjesConstants 1

def stieltjesDelta : ℝ :=
  stieltjesBeta ^ 2 - stieltjesConstants 3 / (2 * stieltjesConstants 1)

/-- The named stronger lower and upper rational envelopes. -/
def strongerRationalEnvelope (t : ℝ) : Prop :=
  stieltjesAlpha /
        (1 + stieltjesBeta * t + stieltjesAlpha * t ^ 2) <
      stieltjesZ t ∧
    stieltjesZ t <
      stieltjesAlpha /
        (1 + stieltjesBeta * t + stieltjesDelta * t ^ 2)

/-- The two displayed positive-denominator comparisons, including their
source polynomial identities. -/
def strongerEnvelopeDenominatorComparisons (t : ℝ) : Prop :=
  ((1 + t) ^ 2 -
      (1 + stieltjesBeta * t + stieltjesAlpha * t ^ 2) =
    (2 - stieltjesBeta) * t + (1 - stieltjesAlpha) * t ^ 2) ∧
    (151 * (1 + stieltjesBeta * t + stieltjesDelta * t ^ 2) -
        (151 + t ^ 2) =
      151 * stieltjesBeta * t +
        (151 * stieltjesDelta - 1) * t ^ 2) ∧
    0 < (1 + t) ^ 2 -
      (1 + stieltjesBeta * t + stieltjesAlpha * t ^ 2) ∧
    0 < 151 * (1 + stieltjesBeta * t + stieltjesDelta * t ^ 2) -
      (151 + t ^ 2)

/-- The fixed-template inequalities in the positive `t=s-1` coordinate. -/
def fixedTemplateAtPositiveT (t : ℝ) : Prop :=
  stieltjesAlpha / (1 + t) ^ 2 < stieltjesZ t ∧
    stieltjesZ t < 151 * stieltjesAlpha / (151 + t ^ 2)

/-- Claim 1396: the concrete stronger rational envelopes and their strict
positive-denominator comparison give the fixed-template bounds and are
strictly tighter than those fixed-template bounds for every positive t. -/
def strongerEnvelopesImplyFixedTemplateBounds : Prop :=
  stieltjesContext ∧
    stieltjesAlpha > 0 ∧
      2 - stieltjesBeta > 0 ∧
        1 - stieltjesAlpha > 0 ∧
          stieltjesBeta > 0 ∧
            151 * stieltjesDelta - 1 > 0 ∧
              (∀ t : ℝ, 0 < t → strongerRationalEnvelope t) ∧
                (∀ t : ℝ, 0 < t →
                  strongerEnvelopeDenominatorComparisons t) ∧
                  (∀ t : ℝ, 0 < t →
                    stieltjesAlpha / (1 + t) ^ 2 <
                        stieltjesAlpha /
                          (1 + stieltjesBeta * t +
                            stieltjesAlpha * t ^ 2) ∧
                      stieltjesAlpha /
                          (1 + stieltjesBeta * t +
                            stieltjesAlpha * t ^ 2) < stieltjesZ t ∧
                        stieltjesZ t <
                          stieltjesAlpha /
                            (1 + stieltjesBeta * t +
                              stieltjesDelta * t ^ 2) ∧
                          stieltjesAlpha /
                              (1 + stieltjesBeta * t +
                                stieltjesDelta * t ^ 2) <
                            151 * stieltjesAlpha /
                              (151 + t ^ 2)) ∧
                    (∀ t : ℝ, 0 < t → fixedTemplateAtPositiveT t) ∧
                      ∀ s : ℝ, 1 < s →
                        stieltjesAlpha / s ^ 2 <
                            stieltjesZ (s - 1) ∧
                          stieltjesZ (s - 1) <
                            151 * stieltjesAlpha /
                              (151 + (s - 1) ^ 2)

end MathlibPlus.Open.ResearchFormalization.C0091
