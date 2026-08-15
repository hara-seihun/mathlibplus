import Mathlib

namespace MathlibPlus.Open.Analysis.TwoCopyPendantMoments

noncomputable section

/-- A decreasing list of positive natural parts is an integer partition. -/
def IsIntegerPartition (τ : List ℕ) : Prop :=
  τ.Pairwise (· ≥ ·) ∧ ∀ b ∈ τ, 0 < b

/-- The polynomial ring carrying the two formal copies. -/
abbrev MomentPolynomial := MvPolynomial (Fin 2) ℤ

/-- The elementary pendant moment attached to a finite list of parts. -/
def elementaryMoment (τ : List ℕ) (t : MomentPolynomial) : MomentPolynomial :=
  (τ.map (fun b => 1 + (b : MomentPolynomial) * t)).prod

/-- The two-copy pendant moment is the product of two elementary moments. -/
def twoCopyMoment (τ : List ℕ) (t u : MomentPolynomial) : MomentPolynomial :=
  elementaryMoment τ t * elementaryMoment τ u

/-- The elementary and two-copy pendant-moment definitions for every integer partition. -/
def elementaryAndTwoCopyPendantMoments : Prop :=
  ∀ (τ : List ℕ), IsIntegerPartition τ →
    ∀ (t u : MomentPolynomial),
      elementaryMoment τ t = (τ.map (fun b => 1 + (b : MomentPolynomial) * t)).prod ∧
        twoCopyMoment τ t u = elementaryMoment τ t * elementaryMoment τ u

/-- Raw finitely supported signed distributions indexed by profiles. -/
abbrev SignedComponentEdgeDistribution := Finsupp (List ℕ) ℤ

/-- A signed distribution supported on integer partitions of total six. -/
def IsTotalSixDistribution (μ : SignedComponentEdgeDistribution) : Prop :=
  ∀ τ, μ τ ≠ 0 → IsIntegerPartition τ ∧ τ.sum = 6

/-- Two-copy specialization of a signed component-edge distribution. -/
def twoCopySpecialization (μ : SignedComponentEdgeDistribution) : MomentPolynomial :=
  μ.support.sum (fun τ =>
    (μ τ : MomentPolynomial) *
      twoCopyMoment τ (MvPolynomial.X (0 : Fin 2)) (MvPolynomial.X (1 : Fin 2)))

/-- The explicit signed distribution -[6]+6[5,1]-15[4,2]+10[3,3]. -/
def kernelDistribution : SignedComponentEdgeDistribution :=
  Finsupp.single [6] (-1) +
    Finsupp.single [5, 1] 6 -
    Finsupp.single [4, 2] 15 +
    Finsupp.single [3, 3] 10

/-- Injectivity of the two-copy specialization on total-six distributions. -/
def TwoCopySpecializationInjective : Prop :=
  ∀ μ ν : SignedComponentEdgeDistribution,
    IsTotalSixDistribution μ → IsTotalSixDistribution ν →
      twoCopySpecialization μ = twoCopySpecialization ν →
        μ = ν

/-- The explicit nonzero kernel element and the resulting failure of injectivity. -/
def twoCopySpecializationIsNotInjective : Prop :=
  IsTotalSixDistribution kernelDistribution ∧
    kernelDistribution ≠ 0 ∧
      twoCopySpecialization kernelDistribution = 0 ∧
        ¬ TwoCopySpecializationInjective

/-- Sort a profile into decreasing order. -/
def sortProfile (ρ : List ℕ) : List ℕ :=
  ρ.mergeSort (· ≥ ·)

/-- Remove one occurrence of a split-off part and add its successor. -/
def splitOffOneEdge (ρ : List ℕ) (a : ℕ) : List ℕ × List ℕ :=
  (sortProfile (1 :: ρ), sortProfile ((a + 1) :: ρ.erase a))

/-- A finitely supported integer-valued profile flow. -/
abbrev ProfileFlow := Finsupp (List ℕ × ℕ) ℤ

/-- A profile of selected depth five, with a split-off part occurring in it. -/
def IsDepthFiveProfile (ρ : List ℕ) : Prop :=
  IsIntegerPartition ρ ∧ ρ.sum = 5

/-- Support of a depth-five profile flow lies on split-off pairs from depth five. -/
def IsDepthFiveProfileFlow (α : ProfileFlow) : Prop :=
  ∀ ρ a, α (ρ, a) ≠ 0 → IsDepthFiveProfile ρ ∧ a ∈ ρ

/-- The selected depth-five profile flow, zero away from the five displayed pairs. -/
def depthFiveProfileFlow : ProfileFlow :=
  Finsupp.single ([5], 5) (-1) +
    Finsupp.single ([4, 1], 4) 5 -
    Finsupp.single ([4, 1], 1) 5 -
    Finsupp.single ([3, 2], 3) 10 +
    Finsupp.single ([3, 2], 2) 10

/-- The displayed depth-five profile-flow witness and its split-off-one edge rule. -/
def depthFiveProfileFlowWitness : Prop :=
  IsDepthFiveProfileFlow depthFiveProfileFlow ∧
    depthFiveProfileFlow ([5], 5) = -1 ∧
      depthFiveProfileFlow ([4, 1], 4) = 5 ∧
        depthFiveProfileFlow ([4, 1], 1) = -5 ∧
          depthFiveProfileFlow ([3, 2], 3) = -10 ∧
            depthFiveProfileFlow ([3, 2], 2) = 10 ∧
              (∀ ρ a, (ρ, a) ∉ ({([5], 5), ([4, 1], 4), ([4, 1], 1), ([3, 2], 3), ([3, 2], 2)} : Finset (List ℕ × ℕ)) →
                depthFiveProfileFlow (ρ, a) = 0) ∧
                (∀ ρ a, splitOffOneEdge ρ a =
                  (sortProfile (1 :: ρ), sortProfile ((a + 1) :: ρ.erase a)))

/-- Divergence sends a weighted directed edge to target minus source. -/
def profileDivergence (α : ProfileFlow) : SignedComponentEdgeDistribution :=
  α.support.sum (fun edge =>
    α edge •
      (Finsupp.single (splitOffOneEdge edge.1 edge.2).2 1 -
        Finsupp.single (splitOffOneEdge edge.1 edge.2).1 1))

/-- The profile divergence is the stated kernel, with the two intermediate profiles canceled. -/
def profileDivergenceEqualsKernel : Prop :=
  profileDivergence depthFiveProfileFlow = kernelDistribution ∧
    profileDivergence depthFiveProfileFlow [4, 1, 1] = 0 ∧
      profileDivergence depthFiveProfileFlow [3, 2, 1] = 0 ∧
        profileDivergence depthFiveProfileFlow ≠ 0 ∧
          twoCopySpecialization (profileDivergence depthFiveProfileFlow) = 0

end

end MathlibPlus.Open.Analysis.TwoCopyPendantMoments
