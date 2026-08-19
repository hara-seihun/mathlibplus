import MathlibPlus.Open.Research.Q12PrimeCoverFormalization

namespace MathlibPlus.Open.ResearchFormalization.R1185.Claim41752

open MathlibPlus.Open.Research.Q12PrimeCover

private def oddLayer (i : ZMod 4) : Prop :=
  i.val % 2 = 1

private def q12GroupLaw : Prop :=
  (∀ x y z : Q12Carrier,
      q12Mul (q12Mul x y) z = q12Mul x (q12Mul y z)) ∧
    (∀ x : Q12Carrier,
      q12Mul q12One x = x ∧ q12Mul x q12One = x) ∧
    (∀ x : Q12Carrier,
      q12Mul (q12Inv x) x = q12One ∧
        q12Mul x (q12Inv x) = q12One)

private def primeCoverGroupLaw (p : ℕ) : Prop :=
  (∀ x y z : PrimeCoverCarrier p,
      primeCoverMul p (primeCoverMul p x y) z =
        primeCoverMul p x (primeCoverMul p y z)) ∧
    (∀ x : PrimeCoverCarrier p,
      primeCoverMul p (primeCoverOne p) x = x ∧
        primeCoverMul p x (primeCoverOne p) = x) ∧
    (∀ x : PrimeCoverCarrier p,
      primeCoverMul p (primeCoverInv p x) x = primeCoverOne p ∧
        primeCoverMul p x (primeCoverInv p x) = primeCoverOne p)

private def displayedSwitch : Equiv.Perm Q12Carrier :=
  q12Cycle3 (1, 1) (1, 3) (2, 2) *
    q12Cycle3 (2, 1) (1, 2) (2, 3)

/-- The explicit semidirect carriers, odd-layer inversion action, and the
nontrivial order-three switch used by the exceptional prime-cover group. -/
def claim41752 : Prop :=
  ∀ p : ℕ, Nat.Prime p → 3 < p →
    Nat.card Q12Carrier = 12 ∧
      Nat.card (PrimeCoverCarrier p) = 12 * p ∧
      q12GroupLaw ∧
      primeCoverGroupLaw p ∧
      (∀ i : ZMod 4, oddLayer i →
        q12Parity i = (-1 : ZMod 3) ∧
          primeParity p i = (-1 : ZMod p)) ∧
      q12Switch = displayedSwitch ∧
      q12Switch ^ 3 = 1 ∧
      q12Switch ≠ 1

end MathlibPlus.Open.ResearchFormalization.R1185.Claim41752
