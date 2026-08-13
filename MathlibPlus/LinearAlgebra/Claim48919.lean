import Mathlib.LinearAlgebra.Projectivization.Cardinality

namespace MathlibPlus.LinearAlgebra.Claim48919

open scoped LinearAlgebra.Projectivization

/-- A two-dimensional vector space over a finite field has `q + 1` projective
lines when the field has cardinality `q`, as in admitted claim 48919. -/
theorem projectiveLineCount_claim48919
    (K V : Type*) [Field K] [AddCommGroup V] [Module K V]
    [Finite K] [FiniteDimensional K V]
    (q : ℕ) (hq : Nat.card K = q) (_hq2 : 2 ≤ q)
    (hV : Module.finrank K V = 2) :
    Nat.card (Projectivization K V) = q + 1 := by
  rw [Projectivization.card_of_finrank_two K V hV, hq]

end MathlibPlus.LinearAlgebra.Claim48919
