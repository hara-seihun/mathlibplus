import MathlibPlus.Open.Algebra.PathSwitchM0

namespace MathlibPlus.Open.ResearchFormalization.R1863Claim34347

open MathlibPlus.Open.Algebra.PathSwitchM0

noncomputable section

/-- The rooted pendant-path extension operator used by the abstract switch. -/
def rootedPathExtension (p : PathRing) : PathRing :=
  A p + zVar * p

/-- The one-step scalar extension value used in the parent boundary. -/
def oneStepExtension : PathRing :=
  rootedPathExtension 1

/-- The exact same-host path-switch carrier: both rootings have the same
unrooted value, their rooted extensions attach to the same scalar extensions,
and opposite-end path reversal holds at every formal length. -/
structure SameHostPathSwitch where
  left : PathRing
  right : PathRing
  hostValue : PathRing
  left_host : A left = hostValue
  right_host : A right = hostValue
  left_attachment : ∀ k : ℕ,
    A (rootedPathExtension^[k] left) =
      A ((rootedPathExtension^[k] (1 : PathRing)) * left)
  right_attachment : ∀ k : ℕ,
    A (rootedPathExtension^[k] right) =
      A ((rootedPathExtension^[k] (1 : PathRing)) * right)
  path_reversal : ∀ k : ℕ,
    A (left * rootedPathExtension^[k] right) =
      A (right * rootedPathExtension^[k] left)

/-- The formal parent boundary of a same-host switch at length k. -/
def parentBoundary (S : SameHostPathSwitch) (k : ℕ) : PathRing :=
  A (oneStepExtension *
    (S.left * rootedPathExtension^[k] S.right -
      S.right * rootedPathExtension^[k] S.left))

/-- The positive smaller boundary at length k. -/
def smallerPositiveBoundary (S : SameHostPathSwitch) (k : ℕ) : PathRing :=
  A ((rootedPathExtension^[k] (1 : PathRing)) * S.left)

/-- The negative smaller boundary at length k. -/
def smallerNegativeBoundary (S : SameHostPathSwitch) (k : ℕ) : PathRing :=
  A ((rootedPathExtension^[k] (1 : PathRing)) * S.right)

/-- Claim 34347: every formal same-host path switch factors at every natural
length through its common host value and the difference of the two smaller
boundaries.  No geometric k≥1 restriction is added to this abstract carrier. -/
def abstractSameHostPathSwitchFactorization_34347 : Prop :=
  ∀ S : SameHostPathSwitch, ∀ k : ℕ,
    parentBoundary S k =
      S.hostValue * (smallerPositiveBoundary S k -
        smallerNegativeBoundary S k)

end

end MathlibPlus.Open.ResearchFormalization.R1863Claim34347
