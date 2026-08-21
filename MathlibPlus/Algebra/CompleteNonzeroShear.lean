-- UNVERIFIED (native-decide): submitted but not kernel-verified, so it is a root of the Unverified library rather than of MathlibPlus and no build here depends on it. See unverified.txt.
import Mathlib

namespace MathlibPlus.Algebra

/-- Claim 39809: the complete normalized square-top, nonzero-shear family is
parameterized by the eight free entries of a ternary carry table. -/
theorem completeNormalizedNonzeroShear_claim39809 :
    (Fintype.card {q : (ZMod 3 × ZMod 3) → ZMod 3 // q (0, 0) = 0} = 3 ^ 8) ∧
      3 ^ 8 = 6561 ∧
      (∀ (q : (ZMod 3 × ZMod 3) → ZMod 3), q (0, 0) = 0 →
        ∀ (x u v w : ZMod 3),
          let hq : ZMod 3 → ZMod 3 → ZMod 3 → ZMod 3 →
              ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3 :=
            fun x u v w => (x + v ^ 2, u + q (v, w), v + w, w)
          hq x u v w = (x + v ^ 2, u + q (v, w), v + w, w)) := by
  constructor
  · native_decide
  constructor
  · norm_num
  · intro q hq x u v w
    rfl

end MathlibPlus.Algebra
