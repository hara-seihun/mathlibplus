-- UNVERIFIED (too-heavy): submitted but not kernel-verified, so it is not built and MathlibPlus.lean does not import it. See unverified.txt.
import Mathlib.GroupTheory.SpecificGroups.Quaternion
import Mathlib.Tactic

namespace MathlibPlus.GroupTheory.Claim43656

theorem q220_inverseAtomDecomposition_and_raw_counts :
    let G := QuaternionGroup 55
    let A := {x : G // x ≠ 1}
    let inv : A → A := fun x =>
      ⟨x⁻¹, by simpa using inv_ne_one.mpr x.2⟩
    let atom : A → Finset A := fun x => {x, inv x}
    let atoms : Finset (Finset A) := Finset.univ.image atom
    Fintype.card G = 220 ∧
      Fintype.card A = 219 ∧
      (∀ s ∈ atoms, s.card = 1 ∨ s.card = 2) ∧
      (atoms.filter (fun s => s.card = 1)).card = 1 ∧
      (atoms.filter (fun s => s.card = 2)).card = 109 ∧
      Nat.choose 109 3 = 209934 ∧
      Nat.choose 109 4 = 5563251 := by
  native_decide

end MathlibPlus.GroupTheory.Claim43656
