import Mathlib.Tactic.Ring

namespace MathlibPlus.Combinatorics.Claim22459

/-!
Formalization of the exact `P₃` rooting-message identities from claim 22459.
The local messages follow the packet's recursion
`p_B = a * ρ_B + (q - a) * ∏ (p_D - ρ_D)` and
`ρ_B = ∏ p_D`: `pCenter` has two leaf branches, while `pLeafRoot`
has the unary branch arising from the leaf-rooting.
-/

/-- Exact center- and leaf-rooting messages for `P₃`, together with their
common `ν = p - ρ` message. -/
theorem exactP3RootingMessages {R : Type*} [CommRing R] (a q : R) :
    let pLeaf : R := q
    let rhoLeaf : R := 1
    let pUnary : R := a * pLeaf + (q - a) * (pLeaf - rhoLeaf)
    let rhoUnary : R := pLeaf
    let pCenter : R := a * (pLeaf * pLeaf) +
      (q - a) * ((pLeaf - rhoLeaf) * (pLeaf - rhoLeaf))
    let rhoCenter : R := pLeaf * pLeaf
    let pLeafRoot : R := a * pUnary + (q - a) * (pUnary - rhoUnary)
    let rhoLeafRoot : R := pUnary
    pCenter = 2 * a * q - a + q ^ 3 - 2 * q ^ 2 + q ∧
      pLeafRoot = q * (2 * a + q ^ 2 - 2 * q) ∧
      pCenter - rhoCenter = 2 * a * q - a + q ^ 3 - 3 * q ^ 2 + q ∧
      pLeafRoot - rhoLeafRoot = 2 * a * q - a + q ^ 3 - 3 * q ^ 2 + q := by
  dsimp
  constructor
  · ring
  constructor
  · ring
  constructor <;> ring

end MathlibPlus.Combinatorics.Claim22459
