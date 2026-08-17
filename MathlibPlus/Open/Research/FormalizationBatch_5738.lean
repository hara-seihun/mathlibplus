import MathlibPlus.Open.Research.FormalizationBatch_01a003d5

namespace MathlibPlus.Open.Research.FormalizationBatch_5738

universe uK

open MathlibPlus.Open.Research.FormalizationBatch_01a003d5

/-- Claim 5738: an irreducible triad of coordinate images spans a two-dimensional
plane and cannot be made monomial by any choice of basis. -/
def irreducibleTriadQuotientNotMonomialClaim
    {F S Q : Type*} [Field F] [AddCommGroup Q] [Module F Q]
    [DecidableEq S] (π : (S → F) →ₗ[F] Q) : Prop :=
  Function.Surjective π →
    ∀ i j k : S,
      irreducibleTriadClaim (F := F) (I := S) (V := Q)
        (fun s => π (coordinateVector (F := F) (S := S) s)) i j k →
      Module.finrank F
          (Submodule.span F
            ({π (coordinateVector (F := F) (S := S) i),
              π (coordinateVector (F := F) (S := S) j),
              π (coordinateVector (F := F) (S := S) k)} : Set Q)) = 2 ∧
        (∀ (K : Type uK) (E : Module.Basis K F Q),
          ¬ ∀ t : Fin 3,
            ∃ (η : F) (κ : K),
              η ≠ 0 ∧
                π (coordinateVector (F := F) (S := S) (![i, j, k] t)) = η • E κ) ∧
        (∀ (K : Type uK) (E : Module.Basis K F Q),
          ¬ MonomialCoordinatePresentation π E)

end MathlibPlus.Open.Research.FormalizationBatch_5738
