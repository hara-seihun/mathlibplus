import MathlibPlus.Open.NewResearch2.CyclicConnectionProfiles

namespace MathlibPlus.Open.NewResearch2.R1151NormalizedCollisionData

abbrev Base41353 := MathlibPlus.Open.NewResearch2.CyclicProfiles.C2Cube
abbrev Fiber41353 := MathlibPlus.Open.NewResearch2.CyclicProfiles.C3Square
abbrev G41353 := MathlibPlus.Open.NewResearch2.CyclicProfiles.C2CubeC3Square

/-- The eight binary masks in the displayed base-coordinate order. -/
def baseMasks41353 : Fin 8 → Base41353 :=
  ![![0, 0, 0], ![1, 0, 0], ![0, 1, 0], ![1, 1, 0],
    ![0, 0, 1], ![1, 0, 1], ![0, 1, 1], ![1, 1, 1]]

/-- The displayed permutation `(0,1,2,3,4,5,7,6)`. -/
def rho0Display : Fin 8 → Fin 8 := ![0, 1, 2, 3, 4, 5, 7, 6]

def rho041353 : Equiv.Perm Base41353 :=
  Equiv.swap (baseMasks41353 6) (baseMasks41353 7)

/-- Claim 41353: in the concrete `C₂³ × C₃²` carrier, the base action is
`(0,1,2,3,4,5,7,6)`, the active nonzero support is `{1,2,3}`, and the
normalized fiber-preserving map has the displayed row form. -/
def claim41353 : Prop :=
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
