import MathlibPlus.Open.Research.R1330Claim41037

namespace MathlibPlus.Open.ResearchFormalization.R1330Claim41034

noncomputable section

open MathlibPlus.Open.Research.R1330Formalization_41037

def rotationRestriction (p : ℕ) (F : Equiv.Perm (Ω p))
    (u : Equiv.Perm (V p)) : Prop :=
  ∃ k : Equiv.Perm (Ω p),
    blockKernel p F k ∧
      ∀ v : V p, ∀ s : S3, rotationLabel s →
        k (v, s) = (u v, s)

def reflectionRestriction (p : ℕ) (F : Equiv.Perm (Ω p))
    (u : Equiv.Perm (V p)) : Prop :=
  ∃ k : Equiv.Perm (Ω p),
    blockKernel p F k ∧
      ∀ v : V p, ∀ s : S3, ¬ rotationLabel s →
        k (v, s) = (u v, s)

/-- Claim 41034: for every odd prime in the actual six-block shear
construction, each coordinate projection of the actual block kernel is exactly
the alternating group on the `p^2` block. -/
def claim41034 : Prop :=
  ∀ (p : ℕ) (hp : Nat.Prime p), Odd p →
    letI : NeZero p := ⟨hp.ne_zero⟩
    ∀ (F : Equiv.Perm (Ω p)),
      (∀ z : Ω p, F z = blockShear p z) →
        (∀ u : Equiv.Perm (V p),
          rotationRestriction p F u ↔ u ∈ alternatingGroup (V p)) ∧
        (∀ u : Equiv.Perm (V p),
          reflectionRestriction p F u ↔ u ∈ alternatingGroup (V p))

end
end MathlibPlus.Open.ResearchFormalization.R1330Claim41034
