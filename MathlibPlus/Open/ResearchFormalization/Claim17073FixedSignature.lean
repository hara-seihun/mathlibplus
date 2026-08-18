import Mathlib
import MathlibPlus.Open.ResearchFormalization.Claim17072

namespace MathlibPlus.Open.ResearchFormalization

open MathlibPlus.Open.FormalizationBatch
open MathlibPlus.Open.Algebra.FormalizationBatch

/-- The five side-swap-fixed projections in the order-eight witness. -/
def fixedComponentProjection : Fin 5 → E8 → Prop :=
  ![fixed02Projection, fixed13Projection, outsideCompleteProjection,
    evenOutsideProjection, oddOutsideProjection]

/-- The degree of a vertex in one of the five fixed component projections. -/
noncomputable def fixedComponentDegree (k : Fin 5) (u : V8) : ℕ :=
  Nat.card {e : E8 // fixedComponentProjection k e ∧ u ∈ e.1}

/-- The complete fixed-component/star signature D of a vertex. -/
noncomputable def fixedComponentStarSignature (u : V8) : Fin 5 → ℕ :=
  fun k => fixedComponentDegree k u

/-- Preservation of D by a vertex permutation. -/
def preservesFixedComponentStarSignature (σ : Equiv.Perm V8) : Prop :=
  ∀ u : V8,
    fixedComponentStarSignature (σ u) = fixedComponentStarSignature u

/-- Claim 17073: in the exact order-eight witness, each prescribed map glues
exactly when it preserves the complete fixed-component/star signature, and all
prescribed maps preserve that signature while lying outside their transport
subgroups. -/
def claim17073_fixedSignatureCriterion : Prop :=
  ∃ π : PointedLocalPermutations V8,
    involutiveFixedIndexCocycle π ∧
      tableFamily π ∧
        exactAlternatingSquareRegime π ∧
          (∀ j : V8,
            globalPairing π (π.1 j) ↔
              preservesFixedComponentStarSignature (π.1 j)) ∧
            ∀ j : V8,
              preservesFixedComponentStarSignature (π.1 j) ∧
                π.1 j ∉ prescribedTransportSubgroup π.1 j

end MathlibPlus.Open.ResearchFormalization
