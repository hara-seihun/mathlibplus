import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.C61030

noncomputable section

abbrev F5 := ZMod 5

/-- The labelled-difference image set from the repaired linear-shear claim. -/
def lambdaSet {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    [Module F5 A] [Module F5 B]
    (d : Fin 8 → B) (u : Fin 8 → (A →ₗ[F5] F5)) :
    Set (Fin 8 → F5) :=
  {lambda | ∃ s : B → A, ∀ i x,
    u i (s (x + d i) - s x) = lambda i}

/-- The displayed slope map, with its exact coordinate formula. -/
def phi {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    [Module F5 A] [Module F5 B]
    (d : Fin 8 → B) (u : Fin 8 → (A →ₗ[F5] F5)) :
    (B →ₗ[F5] A) → (Fin 8 → F5) :=
  fun L i => u i (L (d i))

/-- Claim 61030: typed covectors on `A` give constant labelled differences
for linear shears, and the resulting image is contained in `lambdaSet`. -/
def linearShearSlopeInclusion_claim61030 : Prop :=
  ∀ [Fact (Nat.Prime 5)] (A B : Type*)
    [AddCommGroup A] [AddCommGroup B]
    [Module F5 A] [Module F5 B]
    [FiniteDimensional F5 A] [FiniteDimensional F5 B],
    Module.finrank F5 A = 3 →
    Module.finrank F5 B = 3 →
    ∀ (d : Fin 8 → B) (u : Fin 8 → (A →ₗ[F5] F5)),
      (∀ i, d i ≠ 0) →
      (∀ i, u i ≠ 0) →
      (∀ L : B →ₗ[F5] A, ∀ i x,
        u i (L (x + d i) - L x) = phi d u L i) ∧
      Set.range (phi d u) ⊆ lambdaSet d u

end

end MathlibPlus.Open.ResearchFormalization.C61030
