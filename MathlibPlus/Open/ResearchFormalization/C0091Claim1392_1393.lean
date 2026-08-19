import MathlibPlus.Open.ResearchFormalization.C0091Stieltjes1377_1391_1396
import MathlibPlus.Open.Analysis.Stieltjes1390

namespace MathlibPlus.Open.ResearchFormalization.C0091Claim1392_1393

noncomputable section

open MathlibPlus.Open.Analysis

/-- The upper fixed-template admissibility predicate with the source's
`s-1` Stieltjes coordinate. -/
def upperTemplateAdmissible1392 (D : ℝ) : Prop :=
  ∀ s : ℝ, 1 < s →
    stieltjesZ (s - 1) < D / (151 + (s - 1) ^ 2)

/-- Claim 1392: the sharp upper-template numerator is `151 α`, including
sufficiently-near-one failure for every smaller numerator. -/
def claim1392 : Prop :=
  stieltjesContext ∧
    sInf {D : ℝ | upperTemplateAdmissible1392 D} =
      151 * stieltjesAlpha ∧
    upperTemplateAdmissible1392 (151 * stieltjesAlpha) ∧
    (∀ D : ℝ, D < 151 * stieltjesAlpha →
      ∃ ε : ℝ, 0 < ε ∧
        ∀ t : ℝ, 0 < t → t < ε →
          ¬ (stieltjesZ t < D / (151 + t ^ 2)))

/-- Claim 1393: the certified terminating decimals strictly improve both
fixed-template numerators on the identical positive-`s-1` denominators. -/
def claim1393 : Prop :=
  stieltjesContext ∧
    (1 / 14 : ℝ) < 0.0728158 ∧
    (0.0728158 : ℝ) < stieltjesAlpha ∧
    151 * stieltjesAlpha < 10.995193 ∧
    (10.995193 : ℝ) < 11 ∧
    (∀ s : ℝ, 1 < s →
      (1 / 14 : ℝ) / s ^ 2 < stieltjesZ (s - 1) ∧
        stieltjesZ (s - 1) < 11 / (151 + (s - 1) ^ 2) ∧
        (0.0728158 : ℝ) / s ^ 2 < stieltjesZ (s - 1) ∧
        stieltjesZ (s - 1) <
          (10.995193 : ℝ) / (151 + (s - 1) ^ 2))

end

end MathlibPlus.Open.ResearchFormalization.C0091Claim1392_1393
