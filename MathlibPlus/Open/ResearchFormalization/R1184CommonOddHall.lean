import MathlibPlus.Open.Research.R1184Claim41747

namespace MathlibPlus.Open.ResearchFormalization.R1184CommonOddHall

noncomputable section

open MathlibPlus.Open.Research.R1184Formalization_41747

/-- Claim 31980: for odd square-free `m` with `3 ∤ m`, two regular copies
of `E(C_m,8)` can be conjugated inside their generated group so that their
odd-Hall orbit partitions coincide as a normal eight-block system. -/
def claim31980_commonOddHallOrbitBlocks : Prop :=
  ∀ m : ℕ, 1 < m → Odd m → Squarefree m → ¬ 3 ∣ m →
    ∀ (Ω : Type*) [Fintype Ω] [DecidableEq Ω],
      Fintype.card Ω = 8 * m →
      ∀ R T : Subgroup (Equiv.Perm Ω),
        regularECopy m R → regularECopy m T →
          commonOddHallConclusion m R T

end

end MathlibPlus.Open.ResearchFormalization.R1184CommonOddHall
