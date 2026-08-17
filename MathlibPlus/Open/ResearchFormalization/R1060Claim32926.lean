import MathlibPlus.Open.Research.QuaternionBatch

namespace MathlibPlus.Open.ResearchFormalization.R1060Claim32926

open MathlibPlus.Open.Research.QuaternionBatch

noncomputable section

def nonautomorphicLayerPermutation : Fin 4 → Fin 4 :=
  ![0, 1, 3, 2]

def quietUnitProfile (p : ℕ) : Fin 4 → (ZMod p)ˣ :=
  ![1, 1, -1, -1]

def fullScalarPeriod (p : ℕ) (L : Fin 4 → (ZMod p)ˣ) : Prop :=
  ∀ h k : Fin 4,
    relativeScalar p L nonautomorphicLayerPermutation
        (addFour h k) =
      relativeScalar p L nonautomorphicLayerPermutation k

/-- Claim 32926: in the normalized representative nonautomorphic branch, the
full scalar-period condition is equivalent to exactly the displayed unit
profile, rather than merely implying its coordinates. -/
def uniqueQuietUnitProfile_claim32926 : Prop :=
  ∀ p : ℕ, (hp : Nat.Prime p) → 2 < p →
    letI : Fact p.Prime := ⟨hp⟩
    ∀ L : Fin 4 → (ZMod p)ˣ,
      L 0 = 1 →
        (fullScalarPeriod p L ↔ L = quietUnitProfile p)

end

end MathlibPlus.Open.ResearchFormalization.R1060Claim32926
