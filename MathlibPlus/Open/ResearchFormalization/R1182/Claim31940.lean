import MathlibPlus.Open.ResearchFormalization.R1182.Claim41710

namespace MathlibPlus.Open.ResearchFormalization.R1182.Claim31940

open MathlibPlus.Open.ResearchFormalization.R1182.Claim41710

def claim31940 : Prop :=
  ∀ p : ℕ, Nat.Prime p → 3 < p →
    ∀ (orientation : Bool)
      (lam : Q12 → (ZMod p)ˣ) (tau : Q12 → ZMod p),
      normalizedAffineFunctions lam tau →
      let Q := scalarStabilizer p orientation lam
      Q = c4Carrier →
        (∀ T : Set Q12,
          completeProjectedAtom T →
          T ≠ ({q12One} : Set Q12) →
          (∀ h : Q12, h ∈ T →
            ∀ k : Q12,
              relativeCoefficient p orientation lam h k = 0) →
          T = axisAtom) ∧
        (quietVoltageSolution p orientation lam tau axisAtom c4Carrier →
          ∃ c : ZMod p,
            affineAtomShadow p orientation lam tau c c4Carrier)

end MathlibPlus.Open.ResearchFormalization.R1182.Claim31940
