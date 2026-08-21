-- UNVERIFIED (native-decide): submitted but not kernel-verified, so it is not built and MathlibPlus.lean does not import it. See unverified.txt.
import MathlibPlus.Basic

namespace MathlibPlus.LinearAlgebra.Claim6020

/-- The exact candidate-count arithmetic in the two degree-27 replay
fixtures, with `GL(2,3)` represented by Mathlib's concrete matrix group. -/
theorem restrictedCandidateCardinality :
    let GL₂₃ := Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)
    let Candidate := GL₂₃ × (Fin 4 → Fin 3)
    Fintype.card GL₂₃ = 48 ∧
      Fintype.card Candidate = 3888 := by
  dsimp
  constructor
  · native_decide
  · native_decide

end MathlibPlus.LinearAlgebra.Claim6020
