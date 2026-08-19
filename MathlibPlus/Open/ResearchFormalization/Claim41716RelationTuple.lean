import MathlibPlus.Open.ResearchFormalization.R1182.Claim41711

namespace MathlibPlus.Open.ResearchFormalization.Claim41716

open MathlibPlus.Open.ResearchFormalization.R1182.Claim41711

noncomputable section

/-- Claim 41716: under the exact Record-10 affine prime-block carrier, one
common group automorphism carries every relation in a finite labeled tuple
through the same normalized affine lift. -/
def claim41716 : Prop :=
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

end

end MathlibPlus.Open.ResearchFormalization.Claim41716
