import MathlibPlus.Open.ResearchFormalization.R1156Claim31657_31660

namespace MathlibPlus.Open.ResearchFormalization.R1156.Claim31656

noncomputable section

abbrev F7 := ZMod 7

private def doubling : F7 → F7 :=
  fun w => (2 : F7) * w

/-- Claim 31656: for every nonlinear normalized label from the exact
84-label carrier and every base point, substituting `s = 2w` is a bijective
reparametrization of the full relative-derivative signature. -/
def claim31656 : Prop :=
  Function.Bijective doubling ∧
    ∀ (δ : F7 → F7),
      nonlinearNormalizedLabel δ →
        ∀ r : F7,
          Set.range ((relativeDerivative δ r) ∘ doubling) =
            Set.range (relativeDerivative δ r)

end

end MathlibPlus.Open.ResearchFormalization.R1156.Claim31656
