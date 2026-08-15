import Mathlib

open scoped BigOperators
open scoped Topology
open MeasureTheory
open Set
open Filter

namespace MathlibPlus.Open.ResearchFormalizationLargeBatch
def claim19905_fixedVertexGraphAlgebra : Prop := by
  exact ∀ (n : ℕ),
    let V := SimpleGraph (Fin n) →₀ ℂ
    let b : Module.Basis (SimpleGraph (Fin n)) ℂ V := Finsupp.basisSingleOne
    (∀ G, b G = Finsupp.single G 1) ∧
      Module.finrank ℂ V = 2 ^ (n.choose 2)

end MathlibPlus.Open.ResearchFormalizationLargeBatch
