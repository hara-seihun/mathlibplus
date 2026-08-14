import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1107

section

variable {A : Type*} [NonUnitalSemiring A]

/-- Right multiplication by `a`, as used in the stabilizer identities. -/
def rightMultiplication (a : A) : A → A := fun x => x * a

/-- Pointwise addition of endomorphism-shaped functions. -/
def mapAdd (f g : A → A) : A → A := fun x => f x + g x

/-- The map `I + R_a`. -/
def stabilizerMap (a : A) : A → A := mapAdd id (rightMultiplication a)

/-- Composition of multiplication operators, written as juxtaposition for right actions. -/
def operatorProduct (f g : A → A) : A → A := g ∘ f

/--
The multiplication-stabilizer identities under the ideal identity `A^3 = 0`:
`R_a R_b = R_{ab} = 0` and `gamma_a gamma_b = gamma_{a+b}`.
-/
def multiplicationStabilizerIdentities : Prop :=
  (∀ x y z : A, (x * y) * z = 0) →
    ∀ a b : A,
      operatorProduct (rightMultiplication a) (rightMultiplication b) =
          rightMultiplication (a * b) ∧
        rightMultiplication (a * b) = (fun _ : A => 0) ∧
        operatorProduct (stabilizerMap a) (stabilizerMap b) =
          stabilizerMap (a + b)

end

end MathlibPlus.Open.ResearchFormalization.R1107
