import MathlibPlus.Open.ResearchFormalization.R1710Claim33538

namespace MathlibPlus.Open.ResearchFormalization.R1710Claim33537

open MathlibPlus.Open.ResearchFormalization.R1710Claim33538

/-- The zero-core multiplier-period and normalization residues for Claim 33537.

The carriers and zero-core predicate are the reviewed R1710 definitions: the
multiplier-period set is `qL`, and `zeroCore` is the vanishing of the span of
the derivative defects and basepoint-variation translations.
-/
def claim33537 : Prop :=
  ∀ (L : H → GLW) (τ : H → W),
    normalizedAffineProfile L τ →
      (∀ h : H, zeroCore L τ h → h ∈ qL L) ∧
        (∀ k : H, k ∈ qL L → L k = LinearEquiv.refl F7 W)

end MathlibPlus.Open.ResearchFormalization.R1710Claim33537
