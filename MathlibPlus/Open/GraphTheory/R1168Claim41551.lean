import MathlibPlus.Open.GraphTheory.R1168UnresolvedSpace

open scoped BigOperators

namespace MathlibPlus.Open.GraphTheory.R1168Claim41551

noncomputable section

open MathlibPlus.Open.GraphTheory.R1168

/-- Point evaluation on the exact profile carrier. -/
def profileEvaluation_41551 (z : Base) : Profile →ₗ[ZMod 7] ZMod 7 :=
  LinearMap.proj z

/-- The exact normalized average equation map. -/
def profileAverageMap_41551 : Profile →ₗ[ZMod 7] ZMod 7 :=
  (Fintype.card Base : ZMod 7)⁻¹ •
    ∑ z : Base, profileEvaluation_41551 z

/-- The exact unresolved equation at a non-root fiber and word. -/
def unresolvedEquationMap_41551 (z : Base) (w : List (Fin 6)) :
    Profile →ₗ[ZMod 7] ZMod 7 :=
  let inverseAction := baseWordValue (inverseWord w)
  profileEvaluation_41551 (inverseAction z) -
      paritySign z • profileEvaluation_41551 (inverseAction baseRoot) +
        (paritySign z - 1) • profileAverageMap_41551

/-- The unresolved profile solution space is the root-kernel intersection
    with all exact unresolved equation kernels. -/
def unresolvedSolutionSpace_41551 (z : Base) :
    Submodule (ZMod 7) Profile :=
  LinearMap.ker (profileEvaluation_41551 baseRoot) ⊓
    ⨅ w : List (Fin 6), LinearMap.ker (unresolvedEquationMap_41551 z w)

/-- The dimension of the exact unresolved profile solution space. -/
def unresolvedDimension_41551 (z : Base) : ℕ :=
  Module.finrank (ZMod 7) (unresolvedSolutionSpace_41551 z)

/-- Claim 41551: across the 39 non-root fibers, the exact unresolved
    profile solution spaces have dimensions `1` for 8 fibers, `3` for 4,
    `5` for 20, `7` for 4, `9` for 2, and `19` for 1. -/
def claim41551 : Prop :=
  (∀ z : Base, z ≠ baseRoot →
    unresolvedDimension_41551 z = 1 ∨
    unresolvedDimension_41551 z = 3 ∨
    unresolvedDimension_41551 z = 5 ∨
    unresolvedDimension_41551 z = 7 ∨
    unresolvedDimension_41551 z = 9 ∨
    unresolvedDimension_41551 z = 19) ∧
  Nat.card {z : Base // z ≠ baseRoot ∧ unresolvedDimension_41551 z = 1} = 8 ∧
  Nat.card {z : Base // z ≠ baseRoot ∧ unresolvedDimension_41551 z = 3} = 4 ∧
  Nat.card {z : Base // z ≠ baseRoot ∧ unresolvedDimension_41551 z = 5} = 20 ∧
  Nat.card {z : Base // z ≠ baseRoot ∧ unresolvedDimension_41551 z = 7} = 4 ∧
  Nat.card {z : Base // z ≠ baseRoot ∧ unresolvedDimension_41551 z = 9} = 2 ∧
  Nat.card {z : Base // z ≠ baseRoot ∧ unresolvedDimension_41551 z = 19} = 1

end

end MathlibPlus.Open.GraphTheory.R1168Claim41551
