-- UNVERIFIED (native-decide): submitted but not kernel-verified, so it is a root of the Unverified library rather than of MathlibPlus and no build here depends on it. See unverified.txt.
import Mathlib.GroupTheory.SpecificGroups.Dihedral

namespace MathlibPlus.GroupTheory

/-- Claim 24192: the three displayed connection sets in the order-six
DihedralGroup model are inverse-closed, omit the identity, and have valency
four. Here `r` is the standard generator `DihedralGroup.r 1` and `s` is the
reflection `DihedralGroup.sr 0`, making the presentation convention explicit. -/
theorem threeInverseClosedValencyFourConnectionSets :
    let G := DihedralGroup 6
    let r : G := DihedralGroup.r 1
    let s : G := DihedralGroup.sr 0
    let S₀ : Finset G := {r, r ^ 3, r ^ 5, s}
    let S₁ : Finset G := {r ^ 3, s, r ^ 2 * s, r ^ 4 * s}
    let S₂ : Finset G := {s, r * s, r ^ 2 * s, r ^ 4 * s}
    (∀ S ∈ ({S₀, S₁, S₂} : Finset (Finset G)),
        (∀ a ∈ S, a⁻¹ ∈ S) ∧ 1 ∉ S ∧ S.card = 4) := by
  native_decide

end MathlibPlus.GroupTheory
