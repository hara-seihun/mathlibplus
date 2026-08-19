import Mathlib
import MathlibPlus.Open.ResearchFormalization.R0849DescentClaim29599

namespace MathlibPlus.Open.ResearchFormalization.R0849Claim29591

open scoped BigOperators

noncomputable section

abbrev SourcePolynomial := MvPolynomial ℕ ℚ
abbrev TargetVariable := Fin 2 ⊕ ℕ
abbrev TargetPolynomial := MvPolynomial TargetVariable ℚ

def targetX : TargetVariable := Sum.inl (0 : Fin 2)
def targetT : TargetVariable := Sum.inl (1 : Fin 2)
def targetZ (k : ℕ) : TargetVariable := Sum.inr k

def substitutionVariable (k : ℕ) : TargetPolynomial :=
  if k = 1 then
    MvPolynomial.X targetX
  else
    MvPolynomial.X targetT * MvPolynomial.X (targetZ k)

def sourceSubstitution : SourcePolynomial →+* TargetPolynomial :=
  MvPolynomial.eval₂Hom (algebraMap ℚ TargetPolynomial) substitutionVariable

def leftInverseVariable : TargetVariable → SourcePolynomial
  | Sum.inl i => if i = 0 then MvPolynomial.X 1 else 1
  | Sum.inr k => MvPolynomial.X k

def sourceLeftInverse : TargetPolynomial →+* SourcePolynomial :=
  MvPolynomial.eval₂Hom (algebraMap ℚ SourcePolynomial) leftInverseVariable

private def forestUPolynomialImage {V : Type*} [Fintype V] [DecidableEq V] :
    Set SourcePolynomial :=
  {u | ∃ F : SimpleGraph V,
      F.IsAcyclic ∧
        MathlibPlus.Open.ResearchFormalization.R0849DescentClaim29599.forestUPolynomial F = u}

/-- Claim 29591: the nonsingleton-component substitution is injective on the
forest U-polynomial carrier, has the stated t=1 left inverse there, and sends
an x₁/non-singleton monomial to the displayed x,t,z monomial. -/
def claim29591 : Prop :=
  (∀ {V : Type*} [Fintype V] [DecidableEq V]
      (u v : SourcePolynomial),
    u ∈ forestUPolynomialImage (V := V) →
      v ∈ forestUPolynomialImage (V := V) →
      sourceSubstitution u = sourceSubstitution v →
        u = v) ∧
  (∀ {V : Type*} [Fintype V] [DecidableEq V]
      (u : SourcePolynomial),
    u ∈ forestUPolynomialImage (V := V) →
      sourceLeftInverse (sourceSubstitution u) = u) ∧
  (∀ (s : ℕ) (r : ℕ →₀ ℕ),
    (∀ k ∈ r.support, 2 ≤ k) →
      sourceSubstitution
          (MvPolynomial.X (1 : ℕ) ^ s *
            ∏ k ∈ r.support, MvPolynomial.X k ^ (r k)) =
        MvPolynomial.X targetX ^ s *
          MvPolynomial.X targetT ^ (r.support.sum (fun k => r k)) *
            ∏ k ∈ r.support, MvPolynomial.X (targetZ k) ^ (r k))

end

end MathlibPlus.Open.ResearchFormalization.R0849Claim29591
