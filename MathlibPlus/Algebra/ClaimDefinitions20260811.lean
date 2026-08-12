import MathlibPlus.Basic

namespace MathlibPlus.Algebra.Claim26547

/-- The scalar root-closure expression `B(s) = s² + e₂`. -/
def firstScalarRootClosure {R : Type*} [Semiring R] (e₂ s : R) : R :=
  s ^ 2 + e₂

end MathlibPlus.Algebra.Claim26547

namespace MathlibPlus.Algebra.Claim6215

/-- The source's `q`-coordinate substitution, recorded as `A = W q`. -/
def qCoordinateSubstitution {R : Type*} [Semiring R]
    (A W q : R) : Prop := A = W * q

end MathlibPlus.Algebra.Claim6215

namespace MathlibPlus.Algebra.Claim14550

/-- An explicit additive model of the family `C₂^r × C₉` for `0 ≤ r ≤ 5`.
The rank parameter is a `Fin 6`, so the range is part of the type. -/
def a6Group (r : Fin 6) : Type :=
  (Fin (r : ℕ) → ZMod 2) × ZMod 9

end MathlibPlus.Algebra.Claim14550

namespace MathlibPlus.Algebra.Claim13325

/-- The first completed Casoratian coefficient. -/
def firstCompletedCasoratianCoefficient {R : Type*} [CommRing R]
    (σ α π : R) : R :=
  σ + α * σ ^ 2 - α * π + α ^ 2 * π * σ

end MathlibPlus.Algebra.Claim13325

namespace MathlibPlus.Algebra.Claim21766

/-- The trace-shape product `H ⊙ K = {S ∪ U : S ∈ H, U ∈ K}`. -/
def traceShapeProduct {α : Type*} [DecidableEq α]
    (H K : Set (Finset α)) : Set (Finset α) :=
  {V | ∃ S ∈ H, ∃ U ∈ K, V = S ∪ U}

end MathlibPlus.Algebra.Claim21766

namespace MathlibPlus.Algebra.Claim5865

/-- The fiber shear `F_n(x) = x + n (λ(x)) w`, with scalar multiplication
made explicit over a semiring module. -/
def fiberPermutation {R M : Type*} [Semiring R] [AddCommMonoid M]
    [Module R M] (n : ℕ) (lambda : M → R) (w : M) : M → M :=
  fun x => x + ((n : R) * lambda x) • w

end MathlibPlus.Algebra.Claim5865
