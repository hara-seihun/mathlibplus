import Mathlib

namespace MathlibPlus.Open.Combinatorics

abbrev SupportThreeFiber := ZMod 7
abbrev SupportThreeBase := alternatingGroup (Fin 4)
abbrev SupportThreeAffineChart := (ZMod 7)ˣ × ZMod 7

/-- The identity affine chart on the prime fiber. -/
def supportThreeIdentityChart : SupportThreeAffineChart := (1, 0)

/-- Evaluation of a fiberwise affine chart. -/
def supportThreeAffineChartValue
    (c : SupportThreeAffineChart) (r : SupportThreeFiber) : SupportThreeFiber :=
  (c.1 : SupportThreeFiber) * r + c.2

/-- The fiberwise affine lift over a base map. -/
def supportThreeAffineLift
    (q : SupportThreeBase → SupportThreeBase)
    (profile : SupportThreeBase → SupportThreeAffineChart) :
    SupportThreeFiber × SupportThreeBase → SupportThreeFiber × SupportThreeBase :=
  fun x =>
    (supportThreeAffineChartValue (profile x.2) x.1, q x.2)

/-- The nonidentity base support of an affine profile. -/
def supportThreeNonidentitySupport
    (profile : SupportThreeBase → SupportThreeAffineChart) : Set SupportThreeBase :=
  {h | h ≠ 1 ∧ profile h ≠ supportThreeIdentityChart}

/-- Identity-normalized profiles with support exactly three. -/
def supportThreeNormalizedProfile
    (profile : SupportThreeBase → SupportThreeAffineChart) : Prop :=
  profile 1 = supportThreeIdentityChart ∧
    Set.ncard (supportThreeNonidentitySupport profile) = 3

/-- Claim 29088: the exact support-three affine-lift parameter count for the
C₇ fiber over the twelve-point A₄ base. -/
def supportThreeAffineLiftCount_claim29088 : Prop :=
  Set.ncard {profile : SupportThreeBase → SupportThreeAffineChart |
      supportThreeNormalizedProfile profile} =
      Nat.choose 11 3 * (7 * 6 - 1) ^ 3 ∧
    Nat.choose 11 3 * (7 * 6 - 1) ^ 3 = 11371965

end MathlibPlus.Open.Combinatorics
