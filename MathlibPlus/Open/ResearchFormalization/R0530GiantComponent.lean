import MathlibPlus.Open.ResearchFormalizationBatch019ffedf141b77c7b96e46e312eadae9

namespace MathlibPlus.Open.ResearchFormalization.R0530GiantComponent

noncomputable section

open MathlibPlus.Open.ResearchFormalizationBatch

private def connectedWithin {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) : Prop :=
  S.Nonempty ∧
    ∀ ⦃x : V⦄, x ∈ S → ∀ ⦃y : V⦄, y ∈ S →
      Relation.ReflTransGen
        (fun a b : V => G.Adj a b ∧ a ∈ S ∧ b ∈ S) x y

private noncomputable def connectedSupports {V : Type}
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (K : ℕ) : Finset (Finset V) := by
  classical
  exact Finset.univ.powerset.filter
    (fun S => S.card = K ∧ connectedWithin G S)

private noncomputable def coefficientOfComponentVariable
    (K : ℕ) (P : MvPolynomial ℕ ℚ) : MvPolynomial ℕ ℚ := by
  classical
  exact ∑ d ∈ P.support,
    if d K = 1 then
      MvPolynomial.monomial (d.erase K) (P.coeff d)
    else 0

/-- Claim 26107: on the exact unsigned marked-component polynomial of a
finite forest, the coefficient of the unique possible giant component is the
sum over connected K-vertex supports and their induced deletion complements. -/
def giantComponentCoefficientIdentity_claim26107 : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V),
    G.IsAcyclic →
    ∀ m K : ℕ, Fintype.card V = m → K > m / 2 →
      coefficientOfComponentVariable K
          (markedSingletonPolynomial G) =
        ∑ S ∈ connectedSupports G K,
          markedSingletonPolynomial
            (G.induce {v : V | v ∉ S})

end

end MathlibPlus.Open.ResearchFormalization.R0530GiantComponent
