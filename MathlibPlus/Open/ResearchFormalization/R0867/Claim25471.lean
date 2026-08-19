import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R0867.Claim25471

noncomputable section

abbrev Form := MvPolynomial Unit (RatFunc ℚ)
abbrev ZPolynomial := Polynomial (RatFunc ℚ)

def polynomialEquiv : Form ≃ₐ[RatFunc ℚ] ZPolynomial :=
  MvPolynomial.uniqueAlgEquiv (RatFunc ℚ) Unit

def scalarForm (q : ℚ) : Form :=
  MvPolynomial.C (algebraMap ℚ (RatFunc ℚ) q)

def centeredA (K : Fin 4 → Form) : Form := K 0 - K 2
def centeredB (K : Fin 4 → Form) : Form := K 1 - K 2

def commonGcd (A B : Form) : Form :=
  letI : DecidableEq ZPolynomial := Classical.decEq ZPolynomial
  (polynomialEquiv).symm
    (EuclideanDomain.gcd
      (polynomialEquiv A)
      (polynomialEquiv B))

def homogeneousAllDistinctCrossRatio
    (K : Fin 4 → Form) (lam : ℚ) (h : ℕ) : Prop :=
  (∀ i : Fin 4, K i ≠ 0 ∧ MvPolynomial.IsHomogeneous (K i) h) ∧
    (∀ ⦃i j : Fin 4⦄, i ≠ j → K i ≠ K j) ∧
    lam ≠ 0 ∧ lam ≠ 1 ∧
    (K 0 - K 3) * (K 1 - K 2) =
      scalarForm lam * (K 0 - K 2) * (K 1 - K 3)

/-- Claim 25471: after taking the exact common gcd of the two centered
forms, the coprime core directions and the bridge factor have the stated
coprimality relations. -/
def coprimeCoreAndBridgeFactor_claim25471 : Prop :=
  ∀ (K : Fin 4 → Form) (lam : ℚ) (h : ℕ),
    homogeneousAllDistinctCrossRatio K lam h →
      let A := centeredA K
      let B := centeredB K
      ∃ G X Y : Form,
        G = commonGcd A B ∧
          A = G * X ∧
            B = G * Y ∧
              IsCoprime X Y ∧
                IsCoprime (scalarForm lam * X - Y) X ∧
                  IsCoprime (scalarForm lam * X - Y) Y ∧
                    IsCoprime (scalarForm lam * X - Y) (X * Y)

end
end MathlibPlus.Open.ResearchFormalization.R0867.Claim25471
