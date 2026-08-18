import MathlibPlus.Open.ResearchFormalization.R0982.Claim27885

namespace MathlibPlus.Open.ResearchFormalization.R0982Claim27887

noncomputable section

open MathlibPlus.Open.ResearchFormalization.R0982
open MathlibPlus.Open.Research.OrbitalCriteria

/-- Every normalized odd-prime plane-fibre transporter has a linear correction
    whose corrected transporter fixes the point-stabilizer orbits, lies in the
    exact two-closure of the generated group, and preserves the conjugate
    translation subgroup. -/
def claim27887 : Prop :=
  ∀ (p : ℕ), Nat.Prime p → Odd p →
    ∀ (φ : Plane p → ZMod p), φ 0 = 0 →
      ∃ qφ : Equiv.Perm (Omega p),
        isQPhi p φ qφ ∧
        ∃ ell : Plane p →ₗ[ZMod p] ZMod p,
          ∃ qc : Equiv.Perm (Omega p),
            isQPhi p (fun u => φ u + ell u) qc ∧
            fixesStabilizerOrbits qc
              (planeFiberGroup p qφ : Set (Equiv.Perm (Omega p))) 0 ∧
            qc ∈ twoClosureOf
              (planeFiberGroup p qφ : Set (Equiv.Perm (Omega p))) ∧
            conjugateSet qc
                (translationSet : Set (Equiv.Perm (Omega p))) =
              conjugateSet qφ
                (translationSet : Set (Equiv.Perm (Omega p)))

end

end MathlibPlus.Open.ResearchFormalization.R0982Claim27887
