import MathlibPlus.Open.Combinatorics.FixedSupportClaim26067

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R0516Claim26062

noncomputable section

open MathlibPlus.Open.Combinatorics.FixedSupportClaim26067

/-- The order-`k` component carrier in one literal spanning edge state. -/
def orderKComponent26062 {V : Type*} [Fintype V]
    (G : SimpleGraph V) (k : ℕ) :=
  {C : G.ConnectedComponent // componentOrder G C = k}

/-- The component profile after one specified component occurrence has been
marked and removed. -/
def residualComponentProfile26062 {V : Type*} [Fintype V]
    (G : SimpleGraph V) (C : G.ConnectedComponent) : ℕ →₀ ℕ :=
  componentProfile G -
    (Finsupp.single (componentOrder G C) 1 : ℕ →₀ ℕ)

/-- The literal signed polynomial term of one marked occurrence. -/
def markedOccurrenceTerm26062 {V : Type*} [Fintype V]
    {G : SimpleGraph V} (A : EdgeState G)
    (C : (stateGraph A).ConnectedComponent) : MvPolynomial ℕ ℤ :=
  ((-1 : ℤ) ^ A.1.card) •
    MvPolynomial.monomial (residualComponentProfile26062 (stateGraph A) C) 1

/-- Claim 26062: in every finite spanning edge state, the generic profile
occurrences of order `k` are in bijection with the literal connected
components of order `k`; the bijection retains the realized support,
residual profile, signed marked coefficient, and exact occurrence count. -/
def graphComponentOccurrencesAreActual_claim26062 : Prop :=
  ∀ {V : Type*} [Fintype V]
    (T : SimpleGraph V) (k : ℕ), 1 ≤ k →
    ∀ A : EdgeState T,
      let G := stateGraph A
      ∃ e : Fin (componentProfile G k) ≃ orderKComponent26062 G k,
        (∀ i : Fin (componentProfile G k),
          componentOrder G (e i).1 = k ∧
            Set.ncard (componentSupport G (e i).1) = k ∧
            residualComponentProfile26062 G (e i).1 =
              componentProfile G -
                (Finsupp.single k 1 : ℕ →₀ ℕ) ∧
            markedOccurrenceTerm26062 A (e i).1 =
              ((-1 : ℤ) ^ A.1.card) •
                MvPolynomial.monomial
                  (componentProfile G -
                    (Finsupp.single k 1 : ℕ →₀ ℕ)) 1) ∧
          componentProfile G k = Nat.card (orderKComponent26062 G k)

end

end MathlibPlus.Open.ResearchFormalization.R0516Claim26062
