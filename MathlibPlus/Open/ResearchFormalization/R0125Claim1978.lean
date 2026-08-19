import Mathlib
import MathlibPlus.Open.NewResearch2.C0117Concrete

namespace MathlibPlus.Open.ResearchFormalization.R0125Claim1978

noncomputable section

open MathlibPlus.Open.NewResearch2.C0117Concrete

private def componentwiseImproves (improved parent : ℝ × ℝ) : Prop :=
  improved.1 < parent.1 ∧ improved.2 < parent.2

private def vkRegion (first second : ℝ) (q : ℕ)
    (_character : DirichletCharacter ℂ q) : Set (ℝ × ℝ) :=
  {point : ℝ × ℝ |
    10 ≤ |point.1| ∧
      1 - 1 /
          (first * Real.log (q : ℝ) + second * V |point.1|) ≤ point.2}

/-- Claim 1978: the improved coefficient pair is componentwise smaller by
exactly the two displayed gaps, and the two improvements are on the same
q/character/height domain as the parent and published pairs. -/
def componentwiseImprovement_claim1978 : Prop :=
  let improved : ℝ × ℝ := (10.30, 61.273)
  let parent : ℝ × ℝ := (10.5, 61.29647)
  let published : ℝ × ℝ := (10.5, 61.5)
  componentwiseImproves improved parent ∧
    componentwiseImproves improved published ∧
    (parent.1 - improved.1, parent.2 - improved.2) = (0.20, 0.02347) ∧
    (published.1 - improved.1, published.2 - improved.2) = (0.20, 0.227) ∧
    (∀ (q : ℕ), 3 ≤ q →
      ∀ character : DirichletCharacter ℂ q,
        vkRegion improved.1 improved.2 q character ⊃
            vkRegion parent.1 parent.2 q character ∧
          vkRegion improved.1 improved.2 q character ⊃
            vkRegion published.1 published.2 q character)

end

end MathlibPlus.Open.ResearchFormalization.R0125Claim1978
