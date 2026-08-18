import MathlibPlus.Open.ResearchFormalization.BatchGraphThresholdClaim16868

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.Batch_01a0040167a37f8a848e6f8a61d

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

def monochromaticEdges16866 {V : Type*} [Fintype V]
    (G : SimpleGraph V) (c : V → Bool) : Finset (Sym2 V) :=
  G.edgeSet.toFinite.toFinset |>.filter
    (fun e => (e.toFinset.image c).card = 1)

def bipartizationNumber16866 {V : Type*} [Fintype V]
    (G : SimpleGraph V) : ℕ :=
  sInf {n : ℕ | ∃ c : V → Bool,
    (monochromaticEdges16866 G c).card = n}

def demandOnSide16866 {V : Type*} [Fintype V]
    (G : SimpleGraph V) (A S : Set V) (u v : V) : Prop :=
  u ≠ v ∧
    graphSameSide A u v ∧
      u ∈ S ∧ v ∈ S ∧
        Disjoint (crossingNeighbors G A u) (crossingNeighbors G A v)

def starOrEdgeless16866 {V : Type*}
    (H : V → V → Prop) : Prop :=
  (∀ u v, ¬H u v) ∨
    ∃ z, ∀ u v, H u v → u = z ∨ v = z

def centerCover16866 {V : Type*}
    (H : V → V → Prop) (S Z : Set V) : Prop :=
  (Z = ∅ ∧ ∀ u v, ¬H u v) ∨
    ∃ z, Z = ({z} : Set V) ∧ z ∈ S ∧
      ∀ u v, H u v → u = z ∨ v = z

def crossingDegreeCost16866 {V : Type*} [Fintype V]
    (G : SimpleGraph V) (A Z : Set V) : ℕ :=
  ∑ v ∈ Finset.univ.filter (fun v : V => v ∈ Z),
    crossingDegreeNat G A v

def claim16866_star_edgeless_demand_graphs_settled : Prop :=
  ∀ {V : Type*} [Fintype V]
    (G : SimpleGraph V) (A B : Set V),
    cutHypotheses G A B →
      (starOrEdgeless16866
          (demandOnSide16866 G A A) ∧
        starOrEdgeless16866
          (demandOnSide16866 G A B)) →
        ∃ ZA ZB : Set V,
          centerCover16866 (demandOnSide16866 G A A) A ZA ∧
            centerCover16866 (demandOnSide16866 G A B) B ZB ∧
              ZA ⊆ A ∧ ZB ⊆ B ∧
                let a := A.ncard
                let c := B.ncard
                crossingDegreeCost16866 G A ZA +
                      crossingDegreeCost16866 G A ZB ≤ a + c ∧
                  a + c = Fintype.card V ∧
                    bipartizationNumber16866 G ≤
                      crossingDegreeCost16866 G A ZA +
                        crossingDegreeCost16866 G A ZB ∧
                      bipartizationNumber16866 G ≤ Fintype.card V ∧
                        (25 ≤ Fintype.card V →
                          bipartizationNumber16866 G ≤
                            Fintype.card V ^ 2 / 25)

end

end MathlibPlus.Open.ResearchFormalization.Batch_01a0040167a37f8a848e6f8a61d
