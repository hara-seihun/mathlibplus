import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.Q0043LabeledPortGluing

noncomputable section
open scoped BigOperators

abbrev Port := Fin 5
abbrev LabeledBoundaryPolynomial := MvPolynomial (ℕ × Finset Port) ℚ
abbrev CountBoundaryPolynomial := MvPolynomial (ℕ × ℕ) ℚ
abbrev ContextPolynomial := MvPolynomial (ℕ × Port) ℚ

def labeledStateA (p q : ℕ) : LabeledBoundaryPolynomial :=
  MvPolynomial.X (p, ({1, 2} : Finset Port)) *
    MvPolynomial.X (q, ({3, 4} : Finset Port))
def labeledStateB (p q : ℕ) : LabeledBoundaryPolynomial :=
  MvPolynomial.X (p, ({1, 3} : Finset Port)) *
    MvPolynomial.X (q, ({2, 4} : Finset Port))
def cardinalityQuotient :
    LabeledBoundaryPolynomial →ₐ[ℚ] CountBoundaryPolynomial :=
  MvPolynomial.rename (fun v : ℕ × Finset Port => (v.1, v.2.card))
def portContextSubstitution :
    LabeledBoundaryPolynomial →+* ContextPolynomial :=
  MvPolynomial.eval₂Hom (algebraMap ℚ ContextPolynomial)
    (fun v : ℕ × Finset Port =>
      ∑ i ∈ v.2, MvPolynomial.X (v.1, i))
def claim16111 : Prop :=
  (∀ p q : ℕ,
    cardinalityQuotient (labeledStateA p q) =
      cardinalityQuotient (labeledStateB p q)) ∧
  (∀ p q : ℕ,
    portContextSubstitution (labeledStateA p q) ≠
      portContextSubstitution (labeledStateB p q)) ∧
  (¬ ∃ f : CountBoundaryPolynomial →+* ContextPolynomial,
    ∀ P : LabeledBoundaryPolynomial,
      portContextSubstitution P = f (cardinalityQuotient P))

end
end MathlibPlus.Open.ResearchFormalization.Q0043LabeledPortGluing
