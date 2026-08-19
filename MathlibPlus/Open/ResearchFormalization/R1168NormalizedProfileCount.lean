import MathlibPlus.Open.GraphTheory.R1168UnresolvedSpace

namespace MathlibPlus.Open.ResearchFormalization.R1168NormalizedProfileCount

noncomputable section

open MathlibPlus.Open.GraphTheory.R1168

/-- Claims 31783 and 41547: the exact normalized C7 translation-profile
carrier is the root-zero subtype of `Profile`; its 39 non-root base values
are free and its cardinality is `7^39`. -/
def normalizedC7TranslationProfileCount_claim31783_41547 : Prop :=
  Fintype.card {z : Base // z ≠ baseRoot} = 39 ∧
    Nat.card {t : Profile // t baseRoot = 0} = 7 ^ 39

end

end MathlibPlus.Open.ResearchFormalization.R1168NormalizedProfileCount
