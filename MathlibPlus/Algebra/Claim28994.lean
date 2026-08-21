-- UNVERIFIED (native-decide): submitted but not kernel-verified, so it is a root of the Unverified library rather than of MathlibPlus and no build here depends on it. See unverified.txt.
import Mathlib

namespace MathlibPlus.Algebra

private def chiralFiberSet_claim28994 : Finset (ZMod 7) := {0, 1, 3}

/-- The three-point fiber `{0,1,3}` in `F₇` has no additive translate equal
to its negation. -/
theorem noAdditiveTranslateChiralFiber_claim28994 :
    ¬ ∃ a : ZMod 7,
      (chiralFiberSet_claim28994.image (fun x => a + x)) =
        (chiralFiberSet_claim28994.image Neg.neg) := by
  native_decide

end MathlibPlus.Algebra
