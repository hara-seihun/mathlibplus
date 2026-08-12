import Mathlib.Algebra.Module.Submodule.Union
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace MathlibPlus.LinearAlgebra.FiniteUnionSubspaces

/-- Claim 48844, formalized as the abstract finite-union avoidance lemma. -/
theorem finiteUnionProperSubspacesAvoidance :
    ∀ (V : Type*) [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
      (I : Type*) [Fintype I]
      (K : I → Submodule ℝ V),
      (∀ i, K i ≠ ⊤) →
      ∃ w : V, ∀ i, w ∉ K i := by
  intro V _ _ _ I _ K hK
  exact Submodule.exists_forall_notMem_of_forall_ne_top K hK

end MathlibPlus.LinearAlgebra.FiniteUnionSubspaces
