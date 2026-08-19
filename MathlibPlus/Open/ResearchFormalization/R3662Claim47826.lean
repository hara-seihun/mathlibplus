import MathlibPlus.Open.ResearchFormalization.BatchQ0134Claim16879
import MathlibPlus.Open.ResearchFormalization.Q0134GoodBad

namespace MathlibPlus.Open.ResearchFormalization.R3662Claim47826

open MathlibPlus.Open.ResearchFormalization.BatchQ0134Claim16879
open MathlibPlus.Open.ResearchFormalization.Q0134GoodBad

noncomputable section

/-- The finite set of positive radii represented by pairs in a point set. -/
noncomputable def radiusValues47826 (P : Finset Plane) (v : Plane) : Finset ℝ :=
  (P.erase v).image (fun w => dist v w)

/-- The incidences contributed by radius classes of size at least four. -/
noncomputable def largeIsoscelesIncidences47826
    (P : Finset Plane) (v : Plane) : ℕ :=
  ∑ r ∈ (radiusValues47826 P v).filter
      (fun r => 4 ≤ (radiusClass P v r).card),
    Nat.choose (radiusClass P v r).card 2

/-- The unique-four profile used for each of the eight ordinary centres. -/
def uniqueFourCentre47826 (P : Finset Plane) (v : Plane) : Prop :=
  ∃ r : ℝ, 0 < r ∧ (radiusClass P v r).card = 4 ∧
    ∀ s : ℝ, 0 < s → 4 ≤ (radiusClass P v s).card → s = r

/-- A robust centre is not a unique-four centre. -/
def robustCentre47826 (P : Finset Plane) (v : Plane) : Prop :=
  ¬ uniqueFourCentre47826 P v

/-- Claim 47826: on the strict-convex nine-point carrier with exactly one
    robust centre and eight unique-four centres, the eight ordinary centres
    contribute their size-at-least-four incidences as `8 * C(4,2)`, leaving
    capacity at most `63 - 8 * C(4,2)` at the robust centre. -/
def oneRobustNinePointCapacity_claim47826 : Prop :=
  ∀ P : Finset Plane,
    Q0134GoodBad.badConfiguration P →
      P.card = 9 →
        ∀ c : Plane, c ∈ P → robustCentre47826 P c →
          (∀ v ∈ P, v ≠ c → uniqueFourCentre47826 P v) →
            (∑ v ∈ P.erase c, largeIsoscelesIncidences47826 P v) =
                8 * Nat.choose 4 2 ∧
              9 * (9 - 2) = 63 ∧
                largeIsoscelesIncidences47826 P c ≤
                  63 - 8 * Nat.choose 4 2

end

end MathlibPlus.Open.ResearchFormalization.R3662Claim47826
