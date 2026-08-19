import Mathlib
import MathlibPlus.Open.Research.OrbitalCriteria

namespace MathlibPlus.Open.ResearchFormalization.R1010Claim28223

open MathlibPlus.Open.Research.OrbitalCriteria

/-- Claim 28223: fixing every point-stabilizer suborbit of the generated
transitive pair places the zero-fixing transporter in the exact 2-closure. -/
def claim28223 : Prop :=
  ∀ (Ω : Type) (T : Subgroup (Equiv.Perm Ω))
    (q : Equiv.Perm Ω) (zero : Ω),
    transitiveSet (T : Set (Equiv.Perm Ω)) →
    q zero = zero →
      let G : Subgroup (Equiv.Perm Ω) :=
        Subgroup.closure
          ((T : Set (Equiv.Perm Ω)) ∪ conjugateSet q (T : Set (Equiv.Perm Ω)))
      fixesStabilizerOrbits q (G : Set (Equiv.Perm Ω)) zero →
        q ∈ twoClosureOf (G : Set (Equiv.Perm Ω))

end MathlibPlus.Open.ResearchFormalization.R1010Claim28223
