import Mathlib
import MathlibPlus.Open.ResearchFormalization.R0335

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R0343DegreeGrafting

open Classical
open MathlibPlus.Open.TreeSpectral
open MathlibPlus.Open.ResearchFormalization.R0335

noncomputable section

/-- The number of leaf occurrences in the chosen representative of an
unlabelled tree class. -/
noncomputable def leafCount_claim20154 {n : ℕ} (T : TreeClass n) : ℕ :=
  ∑ v : Fin n,
    if treeDegree (Quotient.out T).1 v = 1 then 1 else 0

/-- The diagonal leaf-count operator on the unlabelled tree space. -/
noncomputable def leafPotential_claim20154 (n : ℕ) :
    TreeSpace n →ₗ[ℚ] TreeSpace n :=
  linearExtension (fun T =>
    (leafCount_claim20154 T : ℚ) • Finsupp.single T 1)

/-- The degree-weighted leaf deletion/grafting commutator on the unlabelled
finite-tree space.  `G₁` is the literal degree-weighted grafting channel. -/
noncomputable def degreeWeightedCommutator_claim20154 (n : ℕ) :
    TreeSpace n →ₗ[ℚ] TreeSpace n :=
  (transportTreeSpace (Nat.succ_sub_one n)).comp
      (((leafDeletion (n + 1)).comp (G₁ (n + 1))).comp
        (transportTreeSpace (Nat.succ_sub_one n).symm)) -
    (G₁ n).comp (leafDeletion n)

/-- The degree-weighted grafting commutator is the scalar degree potential plus
 the diagonal leaf-count potential. -/
def claim20154 : Prop :=
  ∀ (n : ℕ), 1 ≤ n →
    degreeWeightedCommutator_claim20154 n =
      (2 * (n : ℚ) - 2) •
          (LinearMap.id : TreeSpace n →ₗ[ℚ] TreeSpace n) +
        leafPotential_claim20154 n

end
end MathlibPlus.Open.ResearchFormalization.R0343DegreeGrafting
