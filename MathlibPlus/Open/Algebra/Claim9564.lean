import MathlibPlus.Algebra.Claim9564

namespace MathlibPlus.Open.Algebra.Claim9564

open MathlibPlus.Algebra.Claim9564

def cyclicPresentationByMultiplication : Prop :=
  I = Ideal.span ({f} : Set R)

def hermitian : Prop :=
  ∀ x y : M, lambda x y = barQ (lambda y x)

def nonsingular : Prop :=
  (∀ x : M, ∃! φ : M →ₗ[R] Q, ∀ y : M, φ y = lambda y x) ∧
    (∀ φ : M →ₗ[R] Q, ∃! x : M, ∀ y : M, φ y = lambda y x)

def hermitianAndNonsingularCharacterOfCyclicLinkingForm : Prop :=
  hermitian ∧ nonsingular ∧ f ≠ 0 ∧ cyclicPresentationByMultiplication

end MathlibPlus.Open.Algebra.Claim9564
