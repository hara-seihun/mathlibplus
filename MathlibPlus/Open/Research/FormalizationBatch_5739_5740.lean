import MathlibPlus.Open.Research.FormalizationBatch_01a003d5

namespace MathlibPlus.Open.Research.FormalizationBatch_5739_5740

open scoped BigOperators
open MathlibPlus.Open.Research.FormalizationBatch_01a003d5

universe uK

/-- A full-support minimal relation among `m` indexed vectors. -/
def higherArityIrreducibleRelation
    {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    (m : ℕ) (E : Fin m → V) (a : Fin m → F) : Prop :=
  3 ≤ m ∧
    (∀ ℓ : Fin m, a ℓ ≠ 0) ∧
      (∑ ℓ : Fin m, a ℓ • E ℓ = 0) ∧
        (∀ (J : Finset (Fin m)),
          J ⊂ (Finset.univ : Finset (Fin m)) →
            ∀ b : Fin m → F,
              (∀ ℓ : Fin m, ℓ ∉ J → b ℓ = 0) →
                (∑ ℓ : Fin m, b ℓ • E ℓ = 0) →
                  ∀ ℓ : Fin m, b ℓ = 0)

/-- Claim 5739: every arbitrary irreducible higher-arity relation among
coordinate images has the stated rank and basis-independent obstruction. -/
def higherArityIrreducibleRelationsNotMonomialClaim
    {F Q : Type*} [Field F] [AddCommGroup Q] [Module F Q] : Prop :=
  ∀ (m : ℕ) (π : (Fin m → F) →ₗ[F] Q) (a : Fin m → F),
    Function.Surjective π →
      let E : Fin m → Q :=
        fun ℓ => π (coordinateVector (F := F) (S := Fin m) ℓ)
      higherArityIrreducibleRelation m E a →
        (∀ ℓ : Fin m, E ℓ ≠ 0) ∧
          (∀ ℓ r : Fin m, ℓ ≠ r →
            ¬ ∃ η : F, η ≠ 0 ∧ E ℓ = η • E r) ∧
            Module.finrank F (Submodule.span F (Set.range E)) = m - 1 ∧
              (∀ (K : Type uK) (B : Module.Basis K F Q),
                ¬ ∀ t : Fin m,
                  ∃ (η : F) (κ : K),
                    η ≠ 0 ∧ E t = η • B κ) ∧
                (∀ (K : Type uK) (B : Module.Basis K F Q),
                  ¬ MonomialCoordinatePresentation π B)

/-- Claim 5740: support at most two is precisely the monomial-preserving
boundary, while arbitrary irreducible support at least three has the
higher-arity obstruction. -/
def supportTwoIsMaximalMonomialClosureArityClaim : Prop :=
  (∀ (F S Q K : Type*) [Field F] [AddCommGroup Q] [Module F Q]
      [DecidableEq S],
      ∀ (π : (S → F) →ₗ[F] Q) (E : Module.Basis K F Q),
        MonomialCoordinatePresentation π E →
          ∀ (s : S) (a : F), a ≠ 0 →
            ∀ (Q' : Type*) [AddCommGroup Q'] [Module F Q']
              (q : Q →ₗ[F] Q'),
              Function.Surjective q →
                LinearMap.ker q =
                    Submodule.span F
                      ({π (a • coordinateVector (F := F) (S := S) s)} : Set Q) →
                  ∃ (K' : Type uK) (E' : Module.Basis K' F Q'),
                    MonomialCoordinatePresentation (q.comp π) E') ∧
    (∀ (F S Q K : Type*) [Field F] [AddCommGroup Q] [Module F Q]
      [DecidableEq S],
      ∀ (π : (S → F) →ₗ[F] Q) (E : Module.Basis K F Q),
        MonomialCoordinatePresentation π E →
          ∀ (s t : S), s ≠ t →
            ∀ (a b : F), a ≠ 0 → b ≠ 0 →
              ∀ (Q' : Type*) [AddCommGroup Q'] [Module F Q']
                (q : Q →ₗ[F] Q'),
                Function.Surjective q →
                  LinearMap.ker q =
                      Submodule.span F
                        ({π (a • coordinateVector (F := F) (S := S) s +
                            b • coordinateVector (F := F) (S := S) t)} : Set Q) →
                    ∃ (K' : Type uK) (E' : Module.Basis K' F Q'),
                      MonomialCoordinatePresentation (q.comp π) E') ∧
      (∀ (F Q : Type*) [Field F] [AddCommGroup Q] [Module F Q],
        ∀ (m : ℕ) (π : (Fin m → F) →ₗ[F] Q) (a : Fin m → F),
          Function.Surjective π →
            let E : Fin m → Q :=
              fun ℓ => π (coordinateVector (F := F) (S := Fin m) ℓ)
            higherArityIrreducibleRelation m E a →
              (∀ ℓ : Fin m, E ℓ ≠ 0) ∧
                (∀ ℓ r : Fin m, ℓ ≠ r →
                  ¬ ∃ η : F, η ≠ 0 ∧ E ℓ = η • E r) ∧
                  Module.finrank F (Submodule.span F (Set.range E)) = m - 1 ∧
                    (∀ (K : Type uK) (B : Module.Basis K F Q),
                      ¬ ∀ t : Fin m,
                        ∃ (η : F) (κ : K),
                          η ≠ 0 ∧ E t = η • B κ) ∧
                    (∀ (K : Type uK) (B : Module.Basis K F Q),
                      ¬ MonomialCoordinatePresentation π B))

end MathlibPlus.Open.Research.FormalizationBatch_5739_5740
