import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1230

noncomputable section

abbrev XPoly := Polynomial ℚ
abbrev XYPoly := Polynomial XPoly

def spiderArms (a b : ℕ) : ℕ := a + b

def spiderOrder (a b : ℕ) : ℕ := 1 + a + 2 * b

def spiderL : XPoly := 1 + Polynomial.X

def spiderQ : XPoly := Polynomial.X ^ 2 + Polynomial.X + 1

def spiderH (a b : ℕ) : XPoly :=
  spiderL ^ a * spiderQ ^ b

def spiderA (a b : ℕ) : XPoly :=
  spiderH a b - Polynomial.X ^ (spiderOrder a b - 1) -
    Polynomial.C (spiderArms a b : ℚ) * Polynomial.X ^ (spiderOrder a b - 2)

def spiderB (a b : ℕ) : XPoly :=
  spiderH a b + Polynomial.X ^ spiderOrder a b

/-- The factor is a polynomial in the outer variable y with coefficients in
Q[x], which is the usual Q[x,y] presentation used by the linear-in-y
argument. -/
def spiderFactor (a b : ℕ) : XYPoly :=
  Polynomial.C (spiderB a b) +
    Polynomial.X * Polynomial.C (spiderA a b)

def primitiveOver (f : XYPoly) : Prop :=
  f ≠ 0 ∧ ∀ c : XPoly, (∀ i : ℕ, c ∣ f.coeff i) → IsUnit c

def evalComplex (α : ℂ) (f : XPoly) : ℂ :=
  Polynomial.eval₂ (algebraMap ℚ ℂ) α f

/-- The common-root consequence of B-A = x^(n-2)(x^2+x+d), including all
of the displayed modulus and rearrangement conclusions. -/
def claim30380 : Prop :=
  ∀ a b : ℕ, 3 ≤ spiderOrder a b →
    ∀ α : ℂ,
      (evalComplex α (spiderA a b) = 0 ∧
        evalComplex α (spiderB a b) = 0) →
      α ≠ 0 ∧
      α ^ 2 + α + (spiderArms a b : ℂ) = 0 ∧
      ‖α‖ = Real.sqrt (spiderArms a b : ℝ) ∧
      ‖α + 1‖ = Real.sqrt (spiderArms a b : ℝ) ∧
      α ^ 2 + α + 1 = 1 - (spiderArms a b : ℂ) ∧
      α + (spiderArms a b : ℂ) = -α ^ 2

/-- The all-parameter primitive and irreducibility assertion for the
center-rooted depth-two-spider factor. -/
def claim30382 : Prop :=
  ∀ a b : ℕ, 3 ≤ spiderOrder a b →
    gcd (spiderA a b) (spiderB a b) = 1 ∧
      primitiveOver (spiderFactor a b) ∧
      Irreducible (spiderFactor a b)

def admissibleParameter (p : ℕ × ℕ) : Prop :=
  3 ≤ spiderOrder p.1 p.2

def spiderProduct (s : Multiset (ℕ × ℕ)) : XYPoly :=
  (s.map (fun p => spiderFactor p.1 p.2)).prod

/-- Equality of finite products recovers the complete parameter multiset. -/
def claim30384 : Prop :=
  ∀ s t : Multiset (ℕ × ℕ),
    (∀ p ∈ s, admissibleParameter p) →
    (∀ p ∈ t, admissibleParameter p) →
    spiderProduct s = spiderProduct t →
    s = t

end

end MathlibPlus.Open.ResearchFormalization.R1230
