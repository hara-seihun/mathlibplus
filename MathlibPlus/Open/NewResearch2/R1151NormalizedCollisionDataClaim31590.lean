import MathlibPlus.Open.NewResearch2.R1151NormalizedCollisionDataClaim41353

namespace MathlibPlus.Open.NewResearch2.R1151NormalizedCollisionData

/-- Claim 31590: in the concrete `C₂³ × C₃²` carrier, the base action is
`(0,1,2,3,4,5,7,6)`, the active nonzero support is `{1,2,3}`, and the
normalized fiber-preserving map has the displayed row form. -/
def claim31590 : Prop :=
  (∀ i : Fin 8,
      rho041353 (baseMasks41353 i) =
        baseMasks41353 (rho0Display i)) ∧
    ∃ (f : Equiv.Perm G41353)
      (q : Base41353 → Equiv.Perm Fiber41353),
      (∀ a : Base41353,
        q a ≠ 1 ↔
          a = baseMasks41353 1 ∨
            a = baseMasks41353 2 ∨
              a = baseMasks41353 3) ∧
      (∀ (a : Base41353) (b : Fiber41353),
        f (a, b) = (rho041353 a, q a b))

end MathlibPlus.Open.NewResearch2.R1151NormalizedCollisionData
