import Mathlib

namespace MathlibPlus.Open.Analysis.Claim17989

/--
The scalar theta parity assertion for a specified dilation family `Q` and
quantity `Θ`.  The source does not specify the ambient type of `Q_ξ` or the
scalar codomain of `Θ`, so both remain explicit parameters rather than being
silently chosen.
-/
def scalarThetaParity_claim17989 {X S : Type*}
    (Q : ℝ → X) (Θ : X → S) : Prop :=
  ∀ ξ : ℝ, Θ (Q ξ) = Θ (Q (-ξ))

end MathlibPlus.Open.Analysis.Claim17989
