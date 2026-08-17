import MathlibPlus.Open.ResearchFormalizationBlocks

namespace MathlibPlus.Open.ResearchFormalization.D0219Claim6537

open MathlibPlus.Open.ResearchFormalizationBlocks

/-- Centralization of every regular fibre translation by a permutation. -/
private def centralizesRegularFibreTranslations {β : Type*}
    (r : Equiv.Perm (BlockVertex β)) : Prop :=
  ∀ (a : Fibre) (z : BlockVertex β),
    r (fibreTranslation a z) = fibreTranslation a (r z)

/-- Two lifts induce the same displayed permutation on the block quotient. -/
private def inducesSameQuotientPermutation {β : Type*}
    (r t : Equiv.Perm (BlockVertex β)) (u : Equiv.Perm β) : Prop :=
  ∀ (d : Fibre) (B : β),
    (r (d, B)).2 = u B ∧ (t (d, B)).2 = u B

/-- Claim 6537: centralizing lifts with the same quotient permutation differ
by one and only one fibre-valued profile. -/
def sameQuotientLiftDiscrepancy_claim6537 : Prop :=
  ∀ {β : Type*} [Fintype β]
    (r t : Equiv.Perm (BlockVertex β)) (u : Equiv.Perm β),
    centralizesRegularFibreTranslations r →
      centralizesRegularFibreTranslations t →
        inducesSameQuotientPermutation r t u →
          ∃! c : β → Fibre,
            ∀ (d : Fibre) (B : β),
              (t (d, B)).1 = (r (d, B)).1 + c B

end MathlibPlus.Open.ResearchFormalization.D0219Claim6537
