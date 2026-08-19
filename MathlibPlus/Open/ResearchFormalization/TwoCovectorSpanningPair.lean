import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.TwoCovectorSpanningPair

abbrev Scalar (p : ℕ) := ZMod p
abbrev Covector (p : ℕ) (A : Type*) [Field (Scalar p)]
    [AddCommGroup A] [Module (Scalar p) A] :=
  A →ₗ[Scalar p] Scalar p

/-- The projective proportionality class of a nonzero labelled covector. -/
def covectorClass {p : ℕ} {A I : Type*} [Field (Scalar p)]
    [AddCommGroup A] [Module (Scalar p) A]
    (u : I → Covector p A) (i : I) : Set I :=
  {j | ∃ c : Scalar p, c ≠ 0 ∧ u j = c • u i}

def covectorClasses {p : ℕ} {A I : Type*} [Field (Scalar p)]
    [AddCommGroup A] [Module (Scalar p) A]
    (u : I → Covector p A) : Set (Set I) :=
  {C | ∃ i : I, C = covectorClass u i}

def classDirectionSpan {p : ℕ} {B I : Type*}
    [Field (Scalar p)] [AddCommGroup B] [Module (Scalar p) B]
    (d : I → B) (C : Set I) : Submodule (Scalar p) B :=
  Submodule.span (Scalar p) (d '' C)

def covectorSpan {p : ℕ} {A I : Type*} [Field (Scalar p)]
    [AddCommGroup A] [Module (Scalar p) A]
    (u : I → Covector p A) : Submodule (Scalar p) (Covector p A) :=
  Submodule.span (Scalar p) (Set.range u)

def functionSlopeRealization {p : ℕ} {A B I : Type*}
    [Field (Scalar p)] [AddCommGroup A] [Module (Scalar p) A]
    [AddCommGroup B] [Module (Scalar p) B]
    (d : I → B) (u : I → Covector p A) (lambda : I → Scalar p) : Prop :=
  ∃ s : B → A, ∀ i x,
    u i (s (x + d i) - s x) = lambda i

def linearSlopeRealization {p : ℕ} {A B I : Type*}
    [Field (Scalar p)] [AddCommGroup A] [Module (Scalar p) A]
    [AddCommGroup B] [Module (Scalar p) B]
    (d : I → B) (u : I → Covector p A) (lambda : I → Scalar p) : Prop :=
  ∃ L : B →ₗ[Scalar p] A, ∀ i,
    u i (L (d i)) = lambda i

def functionSlopeSet {p : ℕ} {A B I : Type*}
    [Field (Scalar p)] [AddCommGroup A] [Module (Scalar p) A]
    [AddCommGroup B] [Module (Scalar p) B]
    (d : I → B) (u : I → Covector p A) : Set (I → Scalar p) :=
  {lambda | functionSlopeRealization d u lambda}

def linearSlopeSet {p : ℕ} {A B I : Type*}
    [Field (Scalar p)] [AddCommGroup A] [Module (Scalar p) A]
    [AddCommGroup B] [Module (Scalar p) B]
    (d : I → B) (u : I → Covector p A) : Set (I → Scalar p) :=
  {lambda | linearSlopeRealization d u lambda}

def twoCovectorProfileCondition {p : ℕ} {A B I : Type*}
    [Field (Scalar p)] [AddCommGroup A] [Module (Scalar p) A]
    [AddCommGroup B] [Module (Scalar p) B]
    [FiniteDimensional (Scalar p) A] [FiniteDimensional (Scalar p) B]
    [Fintype I] (d : I → B) (u : I → Covector p A) : Prop :=
  Module.finrank (Scalar p) (covectorSpan u) ≤ 2 ∧
    (Set.ncard (covectorClasses u) ≤ 2 ∨
      ∃ C₀ C₁ : Set I,
        C₀ ∈ covectorClasses u ∧
          C₁ ∈ covectorClasses u ∧
            C₀ ≠ C₁ ∧
              classDirectionSpan (p := p) d C₀ ⊔
                  classDirectionSpan (p := p) d C₁ = ⊤)

/-- The arbitrary-function slope collapse, its slope-space form, and its exact
contrapositive defect obstruction. -/
def claim61443 : Prop :=
  (∀ (p : ℕ) [Fact p.Prime]
    (A B : Type*) [AddCommGroup A] [Module (Scalar p) A]
    [AddCommGroup B] [Module (Scalar p) B]
    [FiniteDimensional (Scalar p) A] [FiniteDimensional (Scalar p) B]
    (I : Type*) [Fintype I]
    (d : I → B) (u : I → Covector p A),
    (∀ i, u i ≠ 0) →
      twoCovectorProfileCondition d u →
        functionSlopeSet d u = linearSlopeSet d u ∧
          ∀ lambda : I → Scalar p,
            functionSlopeRealization d u lambda →
              linearSlopeRealization d u lambda) ∧
  (∀ (p : ℕ) [Fact p.Prime]
    (A B : Type*) [AddCommGroup A] [Module (Scalar p) A]
    [AddCommGroup B] [Module (Scalar p) B]
    [FiniteDimensional (Scalar p) A] [FiniteDimensional (Scalar p) B]
    (I : Type*) [Fintype I]
    (d : I → B) (u : I → Covector p A),
    (∀ i, u i ≠ 0) →
      Module.finrank (Scalar p) (covectorSpan u) ≤ 2 →
        functionSlopeSet d u ≠ linearSlopeSet d u →
          3 ≤ Set.ncard (covectorClasses u) ∧
            ∀ C₀ C₁ : Set I,
              C₀ ∈ covectorClasses u →
                C₁ ∈ covectorClasses u →
                  C₀ ≠ C₁ →
                    classDirectionSpan (p := p) d C₀ ⊔
                        classDirectionSpan (p := p) d C₁ < ⊤)

end MathlibPlus.Open.ResearchFormalization.TwoCovectorSpanningPair
