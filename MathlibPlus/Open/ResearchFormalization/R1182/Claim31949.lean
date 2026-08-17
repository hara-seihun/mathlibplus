import MathlibPlus.Open.ResearchFormalization.R1182.Claim41711

namespace MathlibPlus.Open.ResearchFormalization.R1182.Claim31949

open MathlibPlus.Open.ResearchFormalization.R1182.Claim41711

/-- Claim 31949: one group automorphism carries every relation in a finite
labeled tuple through the same normalized affine prime-block lift. -/
def claim31949 : Prop :=
  ∀ p : ℕ, Nat.Prime p → 3 < p →
    ∀ (orientation : Bool)
      (lam : Q12 → (ZMod p)ˣ) (tau : Q12 → ZMod p),
      normalizedAffineFunctions lam tau →
      ∀ n : ℕ,
        ∀ S : Fin n → Set (PrimeBlock p),
          (∀ i : Fin n,
            inverseClosed p (S i) ∧
              derivativeInvariant p orientation lam tau (S i)) →
            ∃ α : PrimeBlock p → PrimeBlock p,
              isGroupAutomorphism p α ∧
                ∀ i : Fin n,
                  Set.image α (S i) =
                    Set.image (affineLiftMap p orientation lam tau) (S i)

end MathlibPlus.Open.ResearchFormalization.R1182.Claim31949
