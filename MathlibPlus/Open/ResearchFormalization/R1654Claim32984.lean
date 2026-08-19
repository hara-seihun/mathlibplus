import MathlibPlus.Open.ResearchFormalization.R1654Claim32991

namespace MathlibPlus.Open.ResearchFormalization.R1654Claim32984

open MathlibPlus.Open.ResearchFormalization.R1654

noncomputable section

def localDerivativeClosures_claim32984 : Prop :=
  (∀ f : Local7,
    affineLocal f →
      f ≠ 1 →
        ((nonzeroTranslation f ∧ localDerivativeClosure f = ⊥) ∨
          (nontrivialMultiplier f ∧
            localDerivativeClosure f = localCyclicSeven))) ∧
    (∀ sigma : Local7,
      psl32Type sigma ↔
        ∀ g : Local7,
          g ∈ localDerivativeClosure sigma ↔ projectiveLinearImage g) ∧
      (∀ tau : Local7,
        a7Type tau ↔
          localDerivativeClosure tau = alternatingGroup (Fin 7))

end

end MathlibPlus.Open.ResearchFormalization.R1654Claim32984
