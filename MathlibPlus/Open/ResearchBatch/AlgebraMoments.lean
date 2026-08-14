import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchBatch

noncomputable section

/-- The positive power sum of a finite integer-weighted family of values. -/
def signedPowerSum {R : Type*} [CommRing R] (ι : Type*) [Fintype ι]
    (v : ι → R) (w : ι → ℤ) (k : ℕ) : R :=
  ∑ i, (w i : R) * v i ^ k

/-- The signed weight in the fibre of a value. -/
def groupedSignedWeight {ι R : Type*} [AddCommGroup R] [Fintype ι]
    (v : ι → R) (w : ι → ℤ) (a : R) : ℤ := by
  classical
  exact ∑ i ∈ Finset.univ.filter (fun i => v i = a), w i

/-- Claim 4092: Vandermonde cancellation for a finite signed multiset. -/
def claim_4092 : Prop := by
  classical
  exact ∀ (R : Type*) [CommRing R] [IsDomain R] [CharZero R]
    (ι : Type*) [Fintype ι] (v : ι → R) (w : ι → ℤ),
    ((∀ i, v i ≠ 0) →
      ((∀ k : ℕ, 0 < k → signedPowerSum ι v w k = 0) ↔
        (∀ a : R, groupedSignedWeight v w a = 0))) ∧
    (∀ k : ℕ, 0 < k →
      ∑ i ∈ Finset.univ.filter (fun i => v i = 0),
        (w i : R) * v i ^ k = 0)

end

end MathlibPlus.Open.ResearchBatch
