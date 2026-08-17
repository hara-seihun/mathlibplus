import MathlibPlus.Open.ResearchFormalization.R1205SupportOne

namespace MathlibPlus.Open.ResearchFormalization.R1205SupportOneClaim42008

noncomputable section

open MathlibPlus.Open.ResearchFormalization.R1205SupportOne
open MathlibPlus.Open.Research

abbrev Cp (p : ℕ) := Multiplicative (ZMod p)
abbrev A4 := alternatingGroup (Fin 4)
abbrev CpA4 (p : ℕ) := Cp p × A4

/-- Claim 42008: every normalized support-one common-coordinate map that is
an ordinary undirected Cayley-graph isomorphism is harmless up to a signed
fiber map and an automorphism of `A₄`. -/
def claim42008 : Prop :=
  ∀ (p : ℕ), Nat.Prime p → 5 ≤ p →
    ∀ (q : Equiv.Perm A4) (σ : A4 → Equiv.Perm (Cp p))
      (f : CpA4 p → CpA4 p),
      normalizedSupportOneData p q σ f →
        ∀ S : Set (CpA4 p),
          inverseClosed S →
            inverseClosed (f '' S) →
              cayleyRelationIso S (f '' S) f →
                ∃ ε : ZMod p, (ε = 1 ∨ ε = -1) ∧
                  ∃ α : A4 ≃* A4,
                    productMapAutomorphism p ε α ∧
                      productMap p ε α '' S = f '' S

end

end MathlibPlus.Open.ResearchFormalization.R1205SupportOneClaim42008
