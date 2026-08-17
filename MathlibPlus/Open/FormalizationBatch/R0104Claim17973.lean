import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.FormalizationBatch.R0104Claim17973

/-- The ordered positive-divisor index used by the finite divisor fibre. -/
private abbrev DivisorIndex (k : ℕ) := {m : ℕ // m ∈ Nat.divisors k}

/-- The finite `ℓ²` fibre, realized as the canonical finite `PiLp 2` space. -/
private abbrev DivisorHilbert (k : ℕ) :=
  EuclideanSpace ℝ (DivisorIndex k)

/-- The coordinate map keeps every ordered divisor coordinate. -/
private def orderedCoordinateMap (k : ℕ) :
    DivisorHilbert k → (DivisorIndex k → ℝ) :=
  fun v m => v m

/-- Scalar divisor summation is a map applied to a retained fibre vector. -/
private def scalarDivisorSummation (k : ℕ) (v : DivisorHilbert k) : ℝ :=
  ∑ m : DivisorIndex k, v m

/-- Claim 17973: retain the complete ordered positive-divisor `ℓ²` fibre rather
than replacing it by its scalar divisor sum. -/
def claim17973_orderedDivisorBundle : Prop :=
  ∀ k : ℕ, 0 < k →
    (∀ v : DivisorHilbert k,
      ‖v‖ ^ 2 = ∑ m : DivisorIndex k, ‖v m‖ ^ 2) ∧
    Function.Injective (orderedCoordinateMap k) ∧
    ∀ v : DivisorHilbert k,
      scalarDivisorSummation k v = ∑ m : DivisorIndex k, v m

end MathlibPlus.Open.FormalizationBatch.R0104Claim17973
