import Mathlib

namespace MathlibPlus.LinearAlgebra

/-- Claim 9602: pointwise nonzero scaling of observed rows preserves
injectivity of a transform. -/
theorem nonzero_row_weights_preserve_injective_radon
    {X Y K : Type*} [Field K]
    (R : (X → K) → (Y → K))
    (w : Y → K)
    (hw : ∀ y, w y ≠ 0)
    (hR : Function.Injective R) :
    Function.Injective (fun f y => w y * R f y) := by
  intro f g hfg
  apply hR
  funext y
  apply (mul_left_cancel₀ (hw y))
  exact congrFun hfg y

end MathlibPlus.LinearAlgebra
