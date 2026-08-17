import MathlibPlus.Open.Research.Q12PrimeCoverFormalization

namespace MathlibPlus.Open.ResearchFormalization.R1182AffineLiftClaim41703

open MathlibPlus.Open.Research.Q12PrimeCover

abbrev Q12 := Q12Carrier
abbrev GpCarrier (p : ℕ) := PrimeCoverCarrier p
abbrev Q12p (p : ℕ) := QuaternionGroup (3 * p)

/-- The displayed multiplication on the `F_p^+ ⋊_χ Q₁₂` coordinate carrier. -/
def primeBlockGroupPresentation (p : ℕ) : Prop :=
  ∃ e : GpCarrier p ≃ Q12p p,
    e (primeCoverOne p) = 1 ∧
      ∀ x y : GpCarrier p,
        e (primeCoverMul p x y) = e x * e y

def normalizedAffineFunctions {p : ℕ}
    (lam : Q12 → (ZMod p)ˣ) (tau : Q12 → ZMod p) : Prop :=
  lam q12One = 1 ∧ tau q12One = 0

/-- An affine lift is an actual permutation of the prime blocks and has the
fixed exceptional cubic quotient switch in its second coordinate. -/
def normalizedAffineBlockLift (p : ℕ)
    (lam : Q12 → (ZMod p)ˣ) (tau : Q12 → ZMod p)
    (f : GpCarrier p → GpCarrier p) : Prop :=
  Function.Bijective f ∧
    ∀ (x : ZMod p) (h : Q12),
      f (x, h) =
        ((lam h : ZMod p) * x + tau h, q12Switch h)

/-- Claim 41703: for every prime `p > 3`, the explicit prime-block carrier is
`G_p ≅ Q_{12p}`, and every normalized unit-valued multiplier and translation
table has the displayed lift of the fixed exceptional quotient switch. -/
def normalizedAffinePrimeBlockLifts_claim41703 : Prop :=
  ∀ (p : ℕ), Nat.Prime p → 3 < p →
    primeBlockGroupPresentation p ∧
      ∀ (lam : Q12 → (ZMod p)ˣ) (tau : Q12 → ZMod p),
        normalizedAffineFunctions lam tau →
          ∃! f : GpCarrier p → GpCarrier p,
            normalizedAffineBlockLift p lam tau f

end MathlibPlus.Open.ResearchFormalization.R1182AffineLiftClaim41703
