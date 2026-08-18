import MathlibPlus.Open.Combinatorics.CubeSwitching

namespace MathlibPlus.Open.ResearchFormalization.R1047Claim29808

open MathlibPlus.Open.Combinatorics.CubeSwitching

noncomputable section

abbrev F2_29808 := F2
abbrev Base_29808 (n : ℕ) := Base n
abbrev Vertex_29808 (n : ℕ) := Vertex n

private def admissibleSubmodule29808 {n : ℕ}
    (P : SimpleGraph (Base_29808 n)) :
    Submodule F2_29808 (Base_29808 n → F2_29808) :=
  Submodule.span F2_29808 {b | constantOnComponents P b}

private def zeroEvaluation29808 {n : ℕ} :
    (Base_29808 n → F2_29808) →ₗ[F2_29808] F2_29808 :=
  LinearMap.proj (R := F2_29808) (φ := fun _ : Base_29808 n => F2_29808)
    (0 : Base_29808 n)

private def normalizedSubmodule29808 {n : ℕ}
    (P : SimpleGraph (Base_29808 n)) :
    Submodule F2_29808 (Base_29808 n → F2_29808) :=
  admissibleSubmodule29808 P ⊓ (zeroEvaluation29808 (n := n)).ker

private abbrev switchingSpace29808 {n : ℕ}
    (P : SimpleGraph (Base_29808 n)) :=
  {b : Base_29808 n → F2_29808 // b ∈ admissibleSubmodule29808 P}

private abbrev normalizedSwitchingSpace29808 {n : ℕ}
    (P : SimpleGraph (Base_29808 n)) :=
  {b : Base_29808 n → F2_29808 // b ∈ normalizedSubmodule29808 P}

/-- Claim 29808: component-wise Boolean layer switches form the exact binary
switching module, preserve the listed literal cube-graph invariants, and the
condition `b(0)=0` removes one module dimension. -/
def claim29808_admissibleSwitchingGroupAndPreservedInvariants : Prop :=
  ∀ {n : ℕ} (G : SimpleGraph (Vertex_29808 n)),
    isSelectedSubgraph G →
    let P := horizontalProjection G
    (∀ b : Base_29808 n → F2_29808,
      b ∈ admissibleSubmodule29808 P ↔ constantOnComponents P b) ∧
    (∀ b c : Base_29808 n → F2_29808,
      constantOnComponents P b → constantOnComponents P c →
        ∀ a : Vertex_29808 n,
          fiberSwitch b (fiberSwitch c a) = fiberSwitch (b + c) a) ∧
    (∀ b : Base_29808 n → F2_29808,
      constantOnComponents P b →
        Function.Bijective (fiberSwitch b) ∧
        (∀ ⦃a c : Vertex_29808 n⦄,
          verticalEdge a c →
            ((fiberSwitch b a = a ∧ fiberSwitch b c = c) ∨
              (fiberSwitch b a = c ∧ fiberSwitch b c = a))) ∧
        (∀ ⦃i : Fin n⦄ ⦃a c : Vertex_29808 n⦄,
          G.Adj a c → horizontalDirection i a c →
            horizontalDirection i (fiberSwitch b a) (fiberSwitch b c)) ∧
        (∀ i : Fin n,
          directionalEdgeCount G i = directionalEdgeCount (switchedGraph G b) i ∧
          directionalDensity G i = directionalDensity (switchedGraph G b) i) ∧
        (∀ a c : Vertex_29808 n,
          G.Adj a c ↔
            (switchedGraph G b).Adj (fiberSwitch b a) (fiberSwitch b c)) ∧
        (c4Free G ↔ c4Free (switchedGraph G b))) ∧
    (∀ b : Base_29808 n → F2_29808,
      b ∈ normalizedSubmodule29808 P ↔
        b ∈ admissibleSubmodule29808 P ∧ b 0 = 0) ∧
    (∃ e : switchingSpace29808 P ≃ₗ[F2_29808]
        (P.ConnectedComponent → F2_29808),
      ∀ (q : switchingSpace29808 P) (x : Base_29808 n),
        e q (P.connectedComponentMk x) = q.1 x) ∧
    Module.finrank F2_29808 (switchingSpace29808 P) =
      Fintype.card P.ConnectedComponent ∧
    Module.finrank F2_29808 (normalizedSwitchingSpace29808 P) =
      Module.finrank F2_29808 (switchingSpace29808 P) - 1

end

end MathlibPlus.Open.ResearchFormalization.R1047Claim29808
