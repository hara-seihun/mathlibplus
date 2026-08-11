import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Prod

namespace MathlibPlus.Algebra.RelativeDerivative

/-- Claim 28831: the relative-derivative identity for the shear
`f(a,u) = (a,u+c(a))`. The graph-isomorphism consequence is not included
because the source does not fix a connection-set/orbit definition. -/
theorem relativeDerivative_shear_identity
    {A U : Type*} [AddCommGroup A] [AddCommGroup U]
    (c : A → U) (a b : A) (u z : U) :
    let f : A × U → A × U := fun x => (x.1, x.2 + c x.1)
    f ((a, u) + (b, z)) - f (a, u) =
      f (b, z + c (a + b) - c a - c b) := by
  dsimp
  ext <;> simp [add_comm, add_left_comm]

end MathlibPlus.Algebra.RelativeDerivative
