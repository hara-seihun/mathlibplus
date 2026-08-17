import Mathlib

namespace MathlibPlus.Open.FormalizationBatch.R0104Claim17976

private abbrev DivisorIndex (k : ℕ) := {m : ℕ // m ∈ Nat.divisors k}

/-- The canonical relative logarithmic divisor coordinate from the ordered
positive-divisor fibre. -/
private noncomputable def relativeLogCoordinate
    (k : ℕ) (m : DivisorIndex k) : ℝ :=
  (1 / 2 : ℝ) * Real.log ((k : ℝ) / (m.1 : ℝ) ^ 2)

private abbrev DivisorHilbert (k : ℕ) :=
  EuclideanSpace ℝ (DivisorIndex k)

/-- The odd hyperbolic vector on the actual finite `ℓ²` fibre. -/
private noncomputable def oddFiberVector
    (k : ℕ) (q : ℝ) : DivisorHilbert k :=
  WithLp.toLp 2
    (fun m => Real.sinh (q * relativeLogCoordinate k m))

/-- Claim 17976: the componentwise derivative at zero of the odd fibre
vector is the full relative logarithmic coordinate. -/
def claim17976_firstOddDerivative : Prop :=
  ∀ k : ℕ, 0 < k →
    ∀ m : DivisorIndex k,
      HasDerivAt (fun q : ℝ => oddFiberVector k q m)
        (relativeLogCoordinate k m) 0

end MathlibPlus.Open.FormalizationBatch.R0104Claim17976
