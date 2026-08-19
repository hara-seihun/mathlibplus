import MathlibPlus.Open.ResearchFormalization.R1148.Claim41321NormalizedCyclicProfile

namespace MathlibPlus.Open.ResearchFormalization.R1148AdjacentSigns

noncomputable section

open MathlibPlus.Open.ResearchFormalization.R1148.Claim41321

/-- Claim 41322: among the three outer signs of an exact cyclic profile,
two agree, so one cyclic adjacent equation has equal successor and
predecessor outer signs. -/
def oneAdjacentEquationHasEqualOuterSigns_claim41322 : Prop :=
  ∀ (ε : Fin 3 → F7),
    (∀ i : Fin 3, ε i = 1 ∨ ε i = -1) →
      ∃ i : Fin 3,
        ε (Fin.ofNat 3 ((i.val + 1) % 3)) =
          ε (Fin.ofNat 3 ((i.val + 2) % 3))

end

end MathlibPlus.Open.ResearchFormalization.R1148AdjacentSigns
