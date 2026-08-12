import MathlibPlus.Open.Basic
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.LinearAlgebra.TensorProduct.Basic

open scoped TensorProduct

namespace MathlibPlus.Open.Analysis.Claim11591

/--
Claim 11591.  The p-complete/Tate degree-zero state is represented by the
concrete p-adic field and its complexification, rather than by an arbitrary
carrier.  The left tensor presentation is the commuted form of
`ℚ_[p] ⊗[ℚ] ℂ` that carries the displayed `ℂ`-module structure.  The node
asserts the source's nonfinite carrier and complexification claims, and
records the corresponding non-finite range of the identity map; no
unprovided trace-class API is silently added.
-/
def complexificationAfterTateNonfinite : Prop :=
  ∀ (p : ℕ) [Fact p.Prime],
    let V := ℂ ⊗[ℚ] ℚ_[p]
    (¬ Module.Finite ℚ ℚ_[p]) ∧
      ¬ Module.Finite ℂ V ∧
        ¬ Module.Finite ℂ (LinearMap.range (LinearMap.id : V →ₗ[ℂ] V))

end MathlibPlus.Open.Analysis.Claim11591
