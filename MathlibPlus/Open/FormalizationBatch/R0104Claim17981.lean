import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.FormalizationBatch.R0104Claim17981

private abbrev DivisorIndex (k : ℕ) := {m : ℕ // m ∈ Nat.divisors k}
private abbrev DivisorHilbert (k : ℕ) :=
  EuclideanSpace ℝ (DivisorIndex k)

private noncomputable def relativeLogCoordinate
    (k : ℕ) (m : DivisorIndex k) : ℝ :=
  (1 / 2 : ℝ) * Real.log ((k : ℝ) / (m.1 : ℝ) ^ 2)

private noncomputable def oddFiberVector
    (k : ℕ) (q : ℝ) : DivisorHilbert k :=
  WithLp.toLp 2
    (fun m => Real.sinh (q * relativeLogCoordinate k m))

private noncomputable def firstOddJet (k : ℕ) : DivisorHilbert k :=
  WithLp.toLp 2 (fun m => relativeLogCoordinate k m)

private def scalarDivisorSummation (k : ℕ) (v : DivisorHilbert k) : ℝ :=
  ∑ m : DivisorIndex k, v m

/-- The exchange action on the retained ordered fibre, for an explicitly
specified complementary-divisor equivalence. -/
private noncomputable def exchangeVector (k : ℕ)
    (J : DivisorIndex k ≃ DivisorIndex k) (v : DivisorHilbert k) :
    DivisorHilbert k :=
  WithLp.toLp 2 (fun m => v (J m))

/-- Claim 17981: the scalar odd-channel annihilation is a consequence of
applying the scalar map, not a first-jet obstruction to the ordered bundle. -/
def claim17981_prematureScalarNoGo : Prop :=
  (∀ k : ℕ, 0 < k →
    (∃ J : DivisorIndex k ≃ DivisorIndex k,
      (∀ m : DivisorIndex k, J (J m) = m) ∧
      (∀ m : DivisorIndex k, (J m).1 = k / m.1) ∧
      (∀ m : DivisorIndex k,
        relativeLogCoordinate k (J m) = -relativeLogCoordinate k m) ∧
      (∀ v : DivisorHilbert k,
        exchangeVector k J (exchangeVector k J v) = v)) ∧
    scalarDivisorSummation k (firstOddJet k) = 0 ∧
      ∀ m : DivisorIndex k,
        HasDerivAt (fun q : ℝ => oddFiberVector k q m)
          (relativeLogCoordinate k m) 0) ∧
  ¬ (∀ k : ℕ, 0 < k →
    scalarDivisorSummation k (firstOddJet k) = 0 →
      firstOddJet k = 0)

end MathlibPlus.Open.FormalizationBatch.R0104Claim17981
