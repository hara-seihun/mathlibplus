import MathlibPlus.Open.ResearchFormalization.R0613Claim23315

namespace MathlibPlus.Open.ResearchFormalization.R0613Claim23320

noncomputable section

open MathlibPlus.Open.ResearchFormalization.R0613Claim23315

abbrev PositiveIndex := MathlibPlus.Open.ResearchFormalization.R0613Claim23315.PositiveIndex
abbrev RootRing := MathlibPlus.Open.ResearchFormalization.R0613Claim23315.RootRing

def scalarS : RootRing :=
  rootZ + rootX (1 : PositiveIndex)

def scalarDelta (a : PositiveIndex) : RootRing :=
  rootX a - rootZ ^ ((a : ℕ) - 1) * rootX (1 : PositiveIndex)

/-- The delta generators are B-eigenvectors with eigenvalue z, including all
x₁ powers, and s is literally B(1)=z+x₁. -/
def claim23320 : Prop :=
  rootClosure (1 : RootRing) = scalarS ∧
    ∀ a : PositiveIndex, 2 ≤ (a : ℕ) →
      rootClosure (scalarDelta a) = rootZ * scalarDelta a ∧
        ∀ b : ℕ,
          rootClosure (rootX (1 : PositiveIndex) ^ b * scalarDelta a) =
            rootZ * (rootX (1 : PositiveIndex) ^ b * scalarDelta a)

end

end MathlibPlus.Open.ResearchFormalization.R0613Claim23320
