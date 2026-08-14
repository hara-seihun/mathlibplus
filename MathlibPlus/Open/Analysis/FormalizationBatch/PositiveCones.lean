import Mathlib

open scoped InnerProductSpace

namespace MathlibPlus.Open.Analysis.FormalizationBatch

/-- Claim 12361: the nonnegative cone has empty interior in the product topology
on an infinite coordinate index set. -/
def productTopologyNonnegativeConeEmptyInterior : Prop :=
  ∀ (ι : Type*) (_ : Infinite ι),
    interior {x : ι → ℝ | ∀ i, 0 ≤ x i} = (∅ : Set (ι → ℝ))

abbrev SelfAdjointOperator (𝕜 : Type*) (E : Type*) [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] :=
  {A : (E →L[𝕜] E) // ∀ x y : E, ⟪A x, y⟫_𝕜 = ⟪x, A y⟫_𝕜}

/-- Claim 12365: operator-norm interior positivity is uniform coercivity,
expressed on the subtype of bounded self-adjoint operators. -/
def operatorNormPositiveInteriorEqualsCoercivity : Prop :=
  ∀ (𝕜 : Type*) [RCLike 𝕜] (E : Type*)
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E],
    let positive : Set (SelfAdjointOperator 𝕜 E) :=
      {A | ∀ x : E, 0 ≤ RCLike.re ⟪(A.1) x, x⟫_𝕜}
    let coercive : Set (SelfAdjointOperator 𝕜 E) :=
      {A | ∃ δ : ℝ, 0 < δ ∧
        ∀ x : E, δ * ‖x‖ ^ 2 ≤ RCLike.re ⟪(A.1) x, x⟫_𝕜}
    interior positive = coercive

/-- Claim 12366: the positive cone has empty interior for the strong and weak
operator topologies on an infinite-dimensional Hilbert space. -/
def strongWeakOperatorPositiveConesEmptyInterior : Prop :=
  ∀ (𝕜 : Type*) [RCLike 𝕜] (E : Type*)
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (_hE : ¬ Module.Finite 𝕜 E),
    let positive : Set (SelfAdjointOperator 𝕜 E) :=
      {A | ∀ x : E, 0 ≤ RCLike.re ⟪(A.1) x, x⟫_𝕜}
    let strong : TopologicalSpace (SelfAdjointOperator 𝕜 E) :=
      ⨆ x : E, TopologicalSpace.induced (fun A => (A.1) x) inferInstance
    let weak : TopologicalSpace (SelfAdjointOperator 𝕜 E) :=
      ⨆ x : E, ⨆ y : E,
        TopologicalSpace.induced (fun A => ⟪(A.1) x, y⟫_𝕜) inferInstance
    @interior _ strong positive = (∅ : Set (SelfAdjointOperator 𝕜 E)) ∧
      @interior _ weak positive = (∅ : Set (SelfAdjointOperator 𝕜 E))

end MathlibPlus.Open.Analysis.FormalizationBatch
