import MathlibPlus.Open.GraphTheory.R1168UnresolvedSpace

open scoped BigOperators

namespace MathlibPlus.Open.GraphTheory.R1168

noncomputable section

private def profileEvaluation (z : Base) : Profile →ₗ[ZMod 7] ZMod 7 :=
  LinearMap.proj z

private def profileAverageMap : Profile →ₗ[ZMod 7] ZMod 7 :=
  (Fintype.card Base : ZMod 7)⁻¹ •
    ∑ z : Base, profileEvaluation z

private def unresolvedEquationMap (z : Base) (w : List (Fin 6)) :
    Profile →ₗ[ZMod 7] ZMod 7 :=
  let inverseAction := baseWordValue (inverseWord w)
  profileEvaluation (inverseAction z) -
      paritySign z • profileEvaluation (inverseAction baseRoot) +
        (paritySign z - 1) • profileAverageMap

private def unresolvedSolutionSpace (z : Base) :
    Submodule (ZMod 7) Profile :=
  LinearMap.ker (profileEvaluation baseRoot) ⊓
    ⨅ w : List (Fin 6), LinearMap.ker (unresolvedEquationMap z w)

private def unresolvedDimension (z : Base) : ℕ :=
  Module.finrank (ZMod 7) (unresolvedSolutionSpace z)

/-- Claim 31787: the exact solution spaces of the unresolved profile
criterion have dimensions `1^8, 3^4, 5^20, 7^4, 9^2, 19^1` over the
translation field `ZMod 7`, across the 39 non-root fibers. -/
def claim31787 : Prop :=
  (∀ z : Base, z ≠ baseRoot →
    unresolvedDimension z = 1 ∨
    unresolvedDimension z = 3 ∨
    unresolvedDimension z = 5 ∨
    unresolvedDimension z = 7 ∨
    unresolvedDimension z = 9 ∨
    unresolvedDimension z = 19) ∧
  Nat.card {z : Base // z ≠ baseRoot ∧ unresolvedDimension z = 1} = 8 ∧
  Nat.card {z : Base // z ≠ baseRoot ∧ unresolvedDimension z = 3} = 4 ∧
  Nat.card {z : Base // z ≠ baseRoot ∧ unresolvedDimension z = 5} = 20 ∧
  Nat.card {z : Base // z ≠ baseRoot ∧ unresolvedDimension z = 7} = 4 ∧
  Nat.card {z : Base // z ≠ baseRoot ∧ unresolvedDimension z = 9} = 2 ∧
  Nat.card {z : Base // z ≠ baseRoot ∧ unresolvedDimension z = 19} = 1

end
end MathlibPlus.Open.GraphTheory.R1168
