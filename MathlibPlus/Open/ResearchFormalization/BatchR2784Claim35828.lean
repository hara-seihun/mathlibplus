import MathlibPlus.Open.ResearchFormalization.Lease01a0019fGraphOrbit

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.BatchR2784Claim35828

open MathlibPlus.Open.ResearchFormalization.Batch01

noncomputable section

noncomputable def edgeSetCode35828 {n : ℕ} (F : EdgeSet n) : ℕ :=
  (Fintype.equivFin (EdgeSet n) F).val

def typeCanonical35828 {n : ℕ} (F : EdgeSet n) : Prop :=
  ∀ H : EdgeSet n, sameEdgeType n F H →
    edgeSetCode35828 F ≤ edgeSetCode35828 H

noncomputable def typeRepresentatives35828 (n r : ℕ) : Finset (EdgeSet n) :=
  @Finset.filter (EdgeSet n)
    (fun F => typeCanonical35828 F ∧ F.card = r)
    (fun F => Classical.propDecidable _) (Finset.univ : Finset (EdgeSet n))

def lowerShadowsAgree35828 {n k : ℕ}
    (G H : EdgeSet n) : Prop :=
  ∀ j : ℕ, j < k → ∀ F : EdgeSet n, F.card = j →
    aX n G F = aX n H F

def firstDifference35828 {n : ℕ}
    (G H F : EdgeSet n) : ℤ :=
  (typeCountInGraph n G F : ℤ) - typeCountInGraph n H F

def exactTypeMassEquations35828 {n m : ℕ} (X : EdgeSet n) : Prop :=
  (∀ F : EdgeSet n,
    (labelledTypeCount n F : ℚ) * aX n X F =
      (typeCountInGraph n X F : ℚ) ∧
    0 ≤ (typeCountInGraph n X F : ℤ)) ∧
  (∀ t : ℕ,
    ∑ F ∈ typeRepresentatives35828 n t,
      typeCountInGraph n X F = Nat.choose m t)

/-- Claim 35828: the type multiplicities are integral and the two hosts
    separately satisfy the mass equation, with one summand per unlabelled
    type rather than one summand per labelled representative. -/
def exactTypeMassEquations_claim35828 : Prop :=
  ∀ (n k m : ℕ) (G H : EdgeSet n)
    (p : EdgeSet n → ℤ),
    G.card = m → H.card = m →
      lowerShadowsAgree35828 (k := k) G H →
      (∀ F : EdgeSet n, F.card = k →
        p F = firstDifference35828 G H F) →
      exactTypeMassEquations35828 (m := m) G ∧
      exactTypeMassEquations35828 (m := m) H

end
end MathlibPlus.Open.ResearchFormalization.BatchR2784Claim35828
