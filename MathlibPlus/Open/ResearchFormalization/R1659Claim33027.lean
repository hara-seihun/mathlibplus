import MathlibPlus.Open.Research.R1659

namespace MathlibPlus.Open.ResearchFormalization.R1659Claim33027

open MathlibPlus.Open.Research.R1659

/-- Claim 33027: the exact D=C2^2, H=C3^3, G=D×H carrier has the
reported constant-size fiber and permutation census. -/
def exactSevenTranslationOrbits : Prop :=
  ∃ reps : Fin 7 → Finset D,
    (∀ s : Finset D,
      ∃ i : Fin 7, ∃ d : D, translateFinset d (reps i) = s) ∧
    (∀ i j : Fin 7,
      translationEquivalent (reps i) (reps j) → i = j)

def exactConstantSizeFiberCensus_claim33027 : Prop :=
  Fintype.card G = 108 ∧
  Fintype.card D = 4 ∧
  Fintype.card H = 27 ∧
  Fintype.card (Finset D) = 16 ∧
  Fintype.card (Fin 5) = 5 ∧
  exactSevenTranslationOrbits ∧
  Fintype.card (Equiv.Perm D) = 24 ∧
  Fintype.card (D ≃+ D) = 6

end MathlibPlus.Open.ResearchFormalization.R1659Claim33027
