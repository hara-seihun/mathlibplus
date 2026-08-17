import Mathlib

namespace MathlibPlus.Open.Algebra.Claim54393

/-- Claim 54393: nonzero multiplication is cancellative under the stated
no-zero-divisor hypothesis, applied to the difference `a - b`. -/
def rankOneExtraction : Prop :=
  ∀ {R : Type*} [CommRing R] [NoZeroDivisors R]
    {m a b : R},
    m ≠ 0 →
      m * (a - b) = 0 →
        a = b

end MathlibPlus.Open.Algebra.Claim54393
