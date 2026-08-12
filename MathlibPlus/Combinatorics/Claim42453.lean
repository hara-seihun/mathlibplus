import Mathlib

namespace MathlibPlus.Combinatorics.Claim42453

/-- Claim 42453: nonzero vectors in `𝔽₇²` split into 24 inverse pairs, and
inverse-closed zero-free finite sets are unions of those pairs. -/
theorem inverse_atoms_and_inverse_closed_unions :
    let atom : (ZMod 7 × ZMod 7) → Finset (ZMod 7 × ZMod 7) :=
      fun v => {v, -v}
    let atoms : Finset (Finset (ZMod 7 × ZMod 7)) :=
      (Finset.univ.image atom).filter (fun A => (0, 0) ∉ A)
    atoms.card = 24 ∧
      ∀ S : Finset (ZMod 7 × ZMod 7),
        (0, 0) ∉ S →
          ((∀ v, v ∈ S → -v ∈ S) ↔ S.biUnion atom = S) := by
  dsimp
  constructor
  · native_decide
  · intro S hzero
    constructor
    · intro hclosed
      ext v
      constructor
      · intro hv
        rcases Finset.mem_biUnion.mp hv with ⟨u, hu, huv⟩
        rcases (by simpa using huv : v = u ∨ v = -u) with h | h
        · simpa [h] using hu
        · have hneg : -u ∈ S := hclosed u hu
          simpa [h] using hneg
      · intro hv
        apply Finset.mem_biUnion.mpr
        exact ⟨v, hv, by simp⟩
    · intro hcover v hv
      have hneg' : -v ∈ S.biUnion (fun u => {u, -u}) := by
        apply Finset.mem_biUnion.mpr
        exact ⟨v, hv, by simp⟩
      rw [hcover] at hneg'
      exact hneg'

end MathlibPlus.Combinatorics.Claim42453
