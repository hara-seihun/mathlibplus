import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.BatchR0602

/-- Claim 23194: privacy of a mixed coordinate in the transpose of the mixed
matrix, restricted to the extension fiber. -/
def privateMixedCoordinate
    {Host K P : Type*} [DecidableEq Host]
    (extensionFiber : Finset Host)
    (mixedMatrix : Matrix (K × P) Host ℕ)
    (host : Host) (coordinate : K × P) : Prop :=
  host ∈ extensionFiber ∧
    mixedMatrix.transpose host coordinate ≠ 0 ∧
      ∀ other : Host, other ∈ extensionFiber → other ≠ host →
        mixedMatrix.transpose other coordinate = 0

end MathlibPlus.Open.ResearchFormalization.BatchR0602
