import MathlibPlus.Open.Combinatorics.TraceAndCayleyBatch

namespace MathlibPlus.Open.Combinatorics.Claim3369

open MathlibPlus.Open.Combinatorics.Claim3374

/-- Minimum-counterexample deletion inequality with the actual finite-family carrier. -/
def claim3369 : Prop :=
  ∀ (n : ℕ) (F D : Finset (Finset (Fin n))),
    minimumFranklCounterexample F →
      D.Nonempty →
        (∀ A, A ∈ D → removable F A) →
          ∃ x : Fin n,
            x ∈ ground F ∧
              (F.card - 2 * frequency F x) +
                  2 * (D.filter (fun A => x ∈ A)).card ≤ D.card

end MathlibPlus.Open.Combinatorics.Claim3369
