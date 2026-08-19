import MathlibPlus.Algebra.R2111ContextIdeal37141

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R2111.Claim37139

noncomputable section

abbrev ContextCoefficient := MvPolynomial ℕ ℤ
abbrev ContextPolynomial := Polynomial ContextCoefficient

/-- The marker polynomial `C = sum z^i c_i` of context weight `c`. -/
def contextPolynomial (c : ℕ) (coeff : ℕ → ContextCoefficient) : ContextPolynomial :=
  (Finset.range (c + 1)).sum (fun i =>
    Polynomial.C (coeff i) * Polynomial.X ^ i)

def coefficientWeight (m : ℕ →₀ ℕ) : ℕ :=
  m.sum (fun i a => (i + 1) * a)

def contextCoefficientsHaveWeight
    (c : ℕ) (coeff : ℕ → ContextCoefficient) : Prop :=
  ∀ i ∈ Finset.range (c + 1),
    ∀ m ∈ (coeff i).support,
      i + coefficientWeight m = c

/-- The explicit shifted trace formula for the context coefficients. -/
def shiftedContext (c : ℕ) (coeff : ℕ → ContextCoefficient)
    (r : ℕ) : ContextCoefficient :=
  MvPolynomial.X (c + r) +
    (Finset.range c).sum (fun i =>
      MvPolynomial.X (i + r) * coeff i)

def contextIdeal (S₂ S₃ : ContextCoefficient) : Ideal ContextCoefficient :=
  Ideal.span ({S₂, S₃} : Set ContextCoefficient)

def untouchedVariableMonic
    (p : ContextCoefficient) (n : ℕ) : Prop :=
  ∃ q : ContextCoefficient,
    p = MvPolynomial.X n + q ∧
      ∀ m ∈ q.support, m n = 0

/-- Claim 37139: the exact triangular context generators are monic in the
successive variables, their elimination quotient is a polynomial ring and is
prime, and the shifted `S₁` remains nonzero and monic in `x_(c+1)`. -/
def claim37139 : Prop :=
  ∀ (c : ℕ) (coeff : ℕ → ContextCoefficient)
    (C : ContextPolynomial),
    C = contextPolynomial c coeff →
      coeff c = 1 →
        contextCoefficientsHaveWeight c coeff →
          let S₁ := shiftedContext c coeff 1
          let S₂ := shiftedContext c coeff 2
          let S₃ := shiftedContext c coeff 3
          let I := contextIdeal S₂ S₃
          I.IsPrime ∧
            Nonempty
              ((ContextCoefficient ⧸ I) ≃+*
                MvPolynomial
                  {n : ℕ // n ≠ c + 2 ∧ n ≠ c + 3} ℤ) ∧
            untouchedVariableMonic S₂ (c + 2) ∧
            untouchedVariableMonic S₃ (c + 3) ∧
            untouchedVariableMonic S₁ (c + 1) ∧
            S₁ ∉ I ∧
            Ideal.Quotient.mk I S₁ ≠ 0

end

end MathlibPlus.Open.ResearchFormalization.R2111.Claim37139
