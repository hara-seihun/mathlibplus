import MathlibPlus.Open.ResearchFormalization.R1182.Claim41710

namespace MathlibPlus.Open.ResearchFormalization.R1182.Claim31943

open MathlibPlus.Open.ResearchFormalization.R1182.Claim41710

noncomputable section

def claim31943 : Prop :=
  ∀ p : ℕ, Nat.Prime p → 3 < p →
    ∀ (orientation : Bool)
      (lam : Q12 → (ZMod p)ˣ) (tau : Q12 → ZMod p),
      normalizedAffineFunctions lam tau →
      let Q := scalarStabilizer p orientation lam
      (Q ≠ c4Carrier → Q ≠ (Set.univ : Set Q12) →
        affineAtomShadow p orientation lam tau 0 (∅ : Set Q12)) ∧
      (Q = c4Carrier →
        quietVoltageSolution p orientation lam tau axisAtom c4Carrier →
          ∃ c : ZMod p,
            affineAtomShadow p orientation lam tau c c4Carrier) ∧
      (Q = (Set.univ : Set Q12) →
        ∀ J : Finset (Fin 3),
          (∀ i : Fin 3, i ∈ J →
            quietVoltageSolution p orientation lam tau
              (quietFamily i) (Set.univ : Set Q12)) →
          ∃ c : ZMod p,
            ∀ i : Fin 3, i ∈ J →
              affineAtomShadow p orientation lam tau c
                (Set.univ : Set Q12))

end
end MathlibPlus.Open.ResearchFormalization.R1182.Claim31943
