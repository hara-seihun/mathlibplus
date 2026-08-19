import MathlibPlus.Open.ResearchFormalization.R1386Claims38478_38480

namespace MathlibPlus.Open.ResearchFormalization.R1386Claim38473

noncomputable section

/-- Claim 38473: the exact whole-period triangular-affine presentation datum
with the quaternion carriers, prime ordering, normalized triangular form,
affine four-layer base action, and transformed scalar profile of whole-base
left period. -/
def claim38473 (p q : ℕ)
    (P : MathlibPlus.Open.ResearchFormalization.R1386Claims38478_38480.TriangularPresentation p q) : Prop :=
  Nat.Prime p ∧
    Nat.Prime q ∧
    Odd p ∧
    Odd q ∧
    q < p ∧
    MathlibPlus.Open.ResearchFormalization.R1386Claims38478_38480.validTriangularPresentation P ∧
    MathlibPlus.Open.ResearchFormalization.R1386Claims38478_38480.wholeBaseLeftPeriod P

end
end MathlibPlus.Open.ResearchFormalization.R1386Claim38473
