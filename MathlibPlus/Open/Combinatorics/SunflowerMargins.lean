import Mathlib

namespace MathlibPlus.Open.Combinatorics

noncomputable def rootNeighborhood5885 {n r : ℕ}
    (G : SimpleGraph (Fin n)) (ρ : Fin r ↪ Fin n) (v : Fin n) : Finset (Fin r) := by
  classical
  exact Finset.univ.filter (fun i => G.Adj (ρ i) v)

noncomputable def outsideVertices5885 {n r : ℕ}
    (ρ : Fin r ↪ Fin n) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun v => v ∉ Set.range ρ)

noncomputable def exactRootNeighborhoodCount5885 {n r : ℕ}
    (G : SimpleGraph (Fin n)) (ρ : Fin r ↪ Fin n)
    (S : Finset (Fin r)) : ℕ :=
  ((outsideVertices5885 ρ).filter
    (fun v => rootNeighborhood5885 G ρ v = S)).card

noncomputable def properCommonNeighborhoodMargin5885 {n r : ℕ}
    (G : SimpleGraph (Fin n)) (ρ : Fin r ↪ Fin n)
    (T : Finset (Fin r)) : ℕ :=
  ((outsideVertices5885 ρ).filter
    (fun v => T ⊆ rootNeighborhood5885 G ρ v)).card

noncomputable def properRootSubsets5885 (r : ℕ) : Finset (Finset (Fin r)) := by
  classical
  exact Finset.univ.filter (fun T => T.Nonempty ∧ T.card < r)

/-- Claim 5885: proper common-neighborhood margins are the sums of exact
root-neighborhood counts over supersets of the root set. -/
def claim5885_proper_intersection_margins : Prop :=
  ∀ (n r : ℕ) (G : SimpleGraph (Fin n)) (ρ : Fin r ↪ Fin n)
    (T : Finset (Fin r)),
    T.Nonempty → T.card < r →
    properCommonNeighborhoodMargin5885 G ρ T =
      Finset.sum (Finset.univ.filter (fun S : Finset (Fin r) => T ⊆ S))
        (fun S => exactRootNeighborhoodCount5885 G ρ S)

noncomputable def onePetalWeight5886 {R : Type*} [CommMonoid R]
    {r : ℕ} (S : Finset (Fin r)) (z : Finset (Fin r) → R) : R :=
  Finset.prod ((properRootSubsets5885 r).filter (fun T => T ⊆ S))
    (fun T => z T)

/-- Claim 5886: multiplying one-petal weights and grouping by exact root
neighborhood gives the stated monomial of proper margins. -/
def claim5886_one_petal_sunflower_weight : Prop :=
  ∀ (n r : ℕ) (G : SimpleGraph (Fin n)) (ρ : Fin r ↪ Fin n)
    {R : Type*} [CommMonoid R] (z : Finset (Fin r) → R),
    Finset.prod (outsideVertices5885 ρ)
      (fun v => onePetalWeight5886 (rootNeighborhood5885 G ρ v) z) =
      Finset.prod (properRootSubsets5885 r)
        (fun T => z T ^ properCommonNeighborhoodMargin5885 G ρ T)

end MathlibPlus.Open.Combinatorics
