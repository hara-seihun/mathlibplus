import MathlibPlus.Basic

namespace MathlibPlus.Algebra.Claim8528

/-- A consecutive Jacobi-coefficient block with the prescribed free values. -/
def freeSquaredJacobiBlock :
    (α β : ℕ → ℝ) → (a b : ℕ) → (c : ℝ) → Prop :=
  fun α β a b c =>
    1 ≤ a ∧ a ≤ b ∧ 0 < c ∧
      ∀ k, a ≤ k → k ≤ b → α k = 2 * c ∧ β k = c

end MathlibPlus.Algebra.Claim8528

namespace MathlibPlus.Algebra.Claim28546

/-- Away from the zero parameter, the collision map is involutive and has no
fixed point.  The source packet leaves the parameter and carrier abstract, so
both are explicit interfaces here. -/
def collisionMapFixedPointFree
    {I X : Type*} [Zero I] (θ : I → X → X) : Prop :=
  ∀ x, x ≠ 0 → Function.Involutive (θ x) ∧ ∀ c, θ x c ≠ c

end MathlibPlus.Algebra.Claim28546
