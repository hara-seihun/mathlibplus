import Mathlib
import Mathlib.Probability.UniformOn

namespace MathlibPlus.Probability.Claim50390

open MeasureTheory

/-- The 36 independent-bit sample space used by the recursive tribes
construction: three root branches, six middle branches per root, and two
bits at each bottom gate. -/
abbrev recursiveTribesSample := Fin 3 → Fin 6 → Fin 2 → Bool

instance : MeasurableSpace recursiveTribesSample := ⊤

/-- The uniform probability measure on all assignments of the 36 bits. -/
noncomputable def recursiveTribesMeasure : Measure recursiveTribesSample :=
  ProbabilityTheory.uniformOn (Set.univ : Set recursiveTribesSample)

/-- The bottom `OR₂` gate. -/
def bottomOr (ω : recursiveTribesSample) (a : Fin 3) (b : Fin 6) : Prop :=
  ∃ d : Fin 2, ω a b d = true

/-- The middle `AND₆` gate at root branch `a`. -/
def middleAnd (ω : recursiveTribesSample) (a : Fin 3) : Prop :=
  ∀ b : Fin 6, bottomOr ω a b

/-- The root `OR₃(AND₆(OR₂))` formula. -/
def recursiveTribesFormula (ω : recursiveTribesSample) : Prop :=
  ∃ a : Fin 3, middleAnd ω a

/-- The sign-valued output: `+1` exactly when the Boolean formula is true,
and `-1` otherwise. -/
noncomputable def recursiveTribesOutput (ω : recursiveTribesSample) : ℤ := by
  classical
  exact if recursiveTribesFormula ω then 1 else -1

end MathlibPlus.Probability.Claim50390
