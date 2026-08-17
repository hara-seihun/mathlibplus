import MathlibPlus.Open.ResearchFormalization.R1182.Claim31941

namespace MathlibPlus.Open.ResearchFormalization.R1182.Repairs

open MathlibPlus.Open.ResearchFormalization.R1182.Claim31941

/-- Claim 41708: on the exact Q₁₂ scalar-profile carrier, full stabilizer
normalization forces lambda(h)=chi(sigma(h))/chi(h), and the only quiet
nonidentity projected families are the axis atom, outer atom, and their union. -/
def fullQ12QuietPatterns_claim41708 : Prop :=
  ∀ p : ℕ, Nat.Prime p → 3 < p →
    ∀ (lam : Q12 → (ZMod p)ˣ) (tau : Q12 → ZMod p),
      normalizedAffineFunctions lam tau →
        scalarStabilizer p lam = Set.univ →
          (∀ h : Q12,
            (lam h : ZMod p) =
              q12Sign p (q12Sigma h) * (q12Sign p h)⁻¹) ∧
          (∀ S : Set Q12,
            quietProjectedFamily p lam S ↔
              S = axisAtom ∨ S = outerAtom ∨
                S = axisAtom ∪ outerAtom)

end MathlibPlus.Open.ResearchFormalization.R1182.Repairs
