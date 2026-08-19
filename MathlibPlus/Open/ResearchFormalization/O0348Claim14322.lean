import MathlibPlus.Open.ResearchFormalization.O0348Claim14320

namespace MathlibPlus.Open.ResearchFormalization.O0348Claim14322

open scoped BigOperators
open MathlibPlus.Open.ResearchFormalizationLargeBatch01a00386
open MathlibPlus.Open.ResearchFormalization.O0348
open MathlibPlus.Open.ResearchFormalizationPseudosimilarity

noncomputable section

private def joinAdj (j : ℕ)
    (x y : Sum (Fin j) (Fin 8)) : Prop :=
  match x, y with
  | Sum.inl a, Sum.inl b => a ≠ b
  | Sum.inr a, Sum.inr b => eightVertexEdge a b
  | Sum.inl _, Sum.inr _ => True
  | Sum.inr _, Sum.inl _ => True

private def joinGraph (j : ℕ) : SimpleGraph (Sum (Fin j) (Fin 8)) :=
  SimpleGraph.fromRel (joinAdj j)

private def rhoSelectedVertices {V : Type*} [Fintype V]
    (Y : SimpleGraph V) (ρ : ℕ) : Finset V :=
  @Finset.filter V
    (fun v =>
      distinctStarRepresentative14320 Y v ∧
        pairValid14320 Y (edgeStar14320 Y v) ∧
          (MathlibPlus.Open.ResearchFormalizationLargeBatch01a00386.graphDegree Y v = 1 ∨
            MathlibPlus.Open.ResearchFormalizationLargeBatch01a00386.graphDegree Y v = ρ))
    (fun v => Classical.propDecidable _) Finset.univ

private def rhoSelection {V : Type*} [Fintype V]
    (Y : SimpleGraph V) (ρ : ℕ) :
    Multiset (ℕ × FiniteGraphClass14320) :=
  (rhoSelectedVertices Y ρ).val.map
    (fun v =>
      (MathlibPlus.Open.ResearchFormalizationLargeBatch01a00386.graphDegree Y v,
        deletedCardType14320 Y v))

def connectedJoinRhoCollision_claim14322 : Prop :=
  ∀ j : ℕ,
    let C := joinGraph j
    let z := Sum.inr (0 : Fin 8)
    let z' := Sum.inr (6 : Fin 8)
    let G := attachPendant C z
    let G' := attachPendant C z'
    let ρ := 5 + j
    C.Connected ∧
      (∀ v : Sum (Fin j) (Fin 8),
        C.IsUniversal v ↔ ∃ a : Fin j, v = Sum.inl a) ∧
        claim14314_pseudosimilar C z z' ∧
          MathlibPlus.Open.ResearchFormalizationLargeBatch01a00386.graphDegree C z =
            4 + j ∧
            MathlibPlus.Open.ResearchFormalizationLargeBatch01a00386.graphDegree C z' =
              4 + j ∧
            (∀ v : Sum (Fin j) (Fin 8),
              MathlibPlus.Open.ResearchFormalizationLargeBatch01a00386.graphDegree C v ≠
                5 + j) ∧
            Fintype.card (Option (Sum (Fin j) (Fin 8))) = 9 + j ∧
              rho14320 G = ρ ∧
                rho14320 G' = ρ ∧
                  ¬ Nonempty (SimpleGraph.Iso G G') ∧
                    rhoSelection G ρ = rhoSelection G' ρ

end

end MathlibPlus.Open.ResearchFormalization.O0348Claim14322
