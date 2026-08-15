import Mathlib

open scoped BigOperators
open scoped Topology
open MeasureTheory
open Set
open Filter

namespace MathlibPlus.Open.ResearchFormalizationLargeBatch
def claim6954_metricCompatibility : Prop := by
  exact ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
    (B U C : Matrix ι ι ℂ),
    B.conjTranspose = B → Matrix.det B ≠ 0 →
    U.conjTranspose * B * U = B →
    C * C = 1 → C.conjTranspose * B = B * C →
    let P := B * C
    P.conjTranspose = P ∧
      (U.conjTranspose * P * U = P ↔ U * C = C * U)

end MathlibPlus.Open.ResearchFormalizationLargeBatch
