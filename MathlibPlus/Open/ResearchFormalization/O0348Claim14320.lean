import MathlibPlus.Open.Graph.Claim9464
import MathlibPlus.Open.ResearchFormalizationPseudosimilarity

namespace MathlibPlus.Open.ResearchFormalization.O0348

noncomputable section

open scoped BigOperators

abbrev FiniteGraphClass14320 :=
  MathlibPlus.Open.Graph.Claim9464.FiniteGraphClass

noncomputable def edgeStar14320 {V : Type*} [Fintype V]
    (Y : SimpleGraph V) (v : V) : Finset (Sym2 V) :=
  letI : Fintype Y.edgeSet := Fintype.ofFinite _
  letI : DecidableEq V := Classical.decEq V
  @Finset.filter (Sym2 V) (fun e => v ∈ e)
    (fun e => Classical.propDecidable _) Y.edgeFinset

def missesVertex14320 {V : Type*}
    (A : Finset (Sym2 V)) (v : V) : Prop :=
  ∀ e ∈ A, v ∉ e

def pairValid14320 {V : Type*} [Fintype V]
    (Y : SimpleGraph V) (A : Finset (Sym2 V)) : Prop :=
  letI : Fintype Y.edgeSet := Fintype.ofFinite _
  letI : DecidableEq V := Classical.decEq V
  A ⊆ Y.edgeFinset ∧
    (∃ u : V, missesVertex14320 A u) ∧
      ∃ w : V, missesVertex14320 (Y.edgeFinset \ A) w

def distinctStarRepresentative14320 {V : Type*} [Fintype V]
    (Y : SimpleGraph V) (v : V) : Prop :=
  ∀ u : V, edgeStar14320 Y u = edgeStar14320 Y v →
    (Fintype.equivFin V) v ≤ (Fintype.equivFin V) u

noncomputable def maximumDegree14320 {V : Type*} [Fintype V]
    (Y : SimpleGraph V) : ℕ :=
  (Finset.univ : Finset V).sup
    (fun v => MathlibPlus.Open.ResearchFormalizationLargeBatch01a00386.graphDegree Y v)

noncomputable def rho14320 {V : Type*} [Fintype V]
    (Y : SimpleGraph V) : ℕ :=
  (@Finset.filter V
    (fun z => ∃ c : V,
      Y.Adj z c ∧
        MathlibPlus.Open.ResearchFormalizationLargeBatch01a00386.graphDegree Y c = 1)
    (fun z => Classical.propDecidable _) Finset.univ).sup
      (fun z => MathlibPlus.Open.ResearchFormalizationLargeBatch01a00386.graphDegree Y z)

noncomputable def pureSelectedVertices14320 {V : Type*} [Fintype V]
    (Y : SimpleGraph V) (rho : ℕ) : Finset V :=
  @Finset.filter V
    (fun v =>
      distinctStarRepresentative14320 Y v ∧
        pairValid14320 Y (edgeStar14320 Y v) ∧
          (MathlibPlus.Open.ResearchFormalizationLargeBatch01a00386.graphDegree Y v = 1 ∨
            rho ≤ MathlibPlus.Open.ResearchFormalizationLargeBatch01a00386.graphDegree Y v))
    (fun v => Classical.propDecidable _) Finset.univ

noncomputable def highDegreeSelectedVertices14320 {V : Type*} [Fintype V]
    (Y : SimpleGraph V) (rho : ℕ) : Finset V :=
  @Finset.filter V
    (fun v =>
      distinctStarRepresentative14320 Y v ∧
        pairValid14320 Y (edgeStar14320 Y v) ∧
          rho ≤ MathlibPlus.Open.ResearchFormalizationLargeBatch01a00386.graphDegree Y v)
    (fun v => Classical.propDecidable _) Finset.univ

noncomputable def deletedCardType14320 {V : Type*} [Fintype V]
    (Y : SimpleGraph V) (v : V) : FiniteGraphClass14320 :=
  MathlibPlus.Open.Graph.Claim9464.deletedCardType Y v

noncomputable def pureSelection14320 {V : Type*} [Fintype V]
    (Y : SimpleGraph V) (rho : ℕ) :
    Multiset (ℕ × FiniteGraphClass14320) :=
  (pureSelectedVertices14320 Y rho).val.map
    (fun v =>
      (MathlibPlus.Open.ResearchFormalizationLargeBatch01a00386.graphDegree Y v,
        deletedCardType14320 Y v))

noncomputable def highDegreePureSelection14320 {V : Type*} [Fintype V]
    (Y : SimpleGraph V) (rho : ℕ) :
    Multiset (ℕ × FiniteGraphClass14320) :=
  (highDegreeSelectedVertices14320 Y rho).val.map
    (fun v =>
      (MathlibPlus.Open.ResearchFormalizationLargeBatch01a00386.graphDegree Y v,
        deletedCardType14320 Y v))

/-- Claim 14320: when the pseudosimilar base vertices have maximum degree, the
pendant extensions are nonisomorphic while their valid pure selections agree;
the high-degree part of each selection is the one matching attachment card. -/
def claim14320_maximumDegreePureSelectionCollision : Prop :=
  ∀ {V : Type*} [Fintype V]
    (C : SimpleGraph V) (z z' : V) (d : ℕ),
    MathlibPlus.Open.ResearchFormalizationPseudosimilarity.minimumDegreeAtLeastTwo C →
      MathlibPlus.Open.ResearchFormalizationLargeBatch01a00386.claim14314_pseudosimilar C z z' →
        MathlibPlus.Open.ResearchFormalizationLargeBatch01a00386.graphDegree C z = d →
          MathlibPlus.Open.ResearchFormalizationLargeBatch01a00386.graphDegree C z' = d →
            d ≤ Fintype.card V - 2 →
              d = maximumDegree14320 C →
                let G := MathlibPlus.Open.ResearchFormalizationPseudosimilarity.attachPendant C z
                let G' := MathlibPlus.Open.ResearchFormalizationPseudosimilarity.attachPendant C z'
                let rho := d + 1
                (∀ v : V,
                    MathlibPlus.Open.ResearchFormalizationLargeBatch01a00386.graphDegree C v ≠ d + 1) ∧
                  rho14320 G = rho ∧
                    rho14320 G' = rho ∧
                      ¬ Nonempty (SimpleGraph.Iso G G') ∧
                        pairValid14320 G (edgeStar14320 G (some z)) ∧
                          pairValid14320 G' (edgeStar14320 G' (some z')) ∧
                            (∀ v : Option V, v ≠ some z →
                              MathlibPlus.Open.ResearchFormalizationLargeBatch01a00386.graphDegree G v < rho) ∧
                              (∀ v : Option V, v ≠ some z' →
                                MathlibPlus.Open.ResearchFormalizationLargeBatch01a00386.graphDegree G' v < rho) ∧
                                highDegreePureSelection14320 G rho =
                                  {(rho, deletedCardType14320 G (some z))} ∧
                                  highDegreePureSelection14320 G' rho =
                                    {(rho, deletedCardType14320 G' (some z'))} ∧
                                    deletedCardType14320 G (some z) =
                                      deletedCardType14320 G' (some z') ∧
                                      pureSelection14320 G rho =
                                        pureSelection14320 G' rho

end

end MathlibPlus.Open.ResearchFormalization.O0348
