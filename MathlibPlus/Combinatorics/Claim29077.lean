-- UNVERIFIED (native-decide): submitted but not kernel-verified, so it is not built and MathlibPlus.lean does not import it. See unverified.txt.
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace MathlibPlus.Combinatorics

/-- Claim 29077.  The literal three-point reflection anchor in the
centralized `C₃²` factor is not inverse closed, so it cannot itself be an
undirected connection set for a partial-inversion construction. -/
theorem claim29077_reflectionAnchor_not_inverseClosed :
    ¬ (∀ x : ZMod 3 × ZMod 3,
      x ∈ ({(0, 0), (1, 0), (0, 1)} : Finset (ZMod 3 × ZMod 3)) ↔
        -x ∈ ({(0, 0), (1, 0), (0, 1)} : Finset (ZMod 3 × ZMod 3))) := by
  native_decide

end MathlibPlus.Combinatorics
