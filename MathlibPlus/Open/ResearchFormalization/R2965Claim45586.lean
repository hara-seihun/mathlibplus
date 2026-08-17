import MathlibPlus.Open.Combinatorics.SubspaceLatticeEdges

namespace MathlibPlus.Open.ResearchFormalization.R2965Claim45586

noncomputable section
open scoped BigOperators

abbrev EdgeFlag (K : Type*) [Field K] [Fintype K] (n : ℕ) :=
  MathlibPlus.Open.Combinatorics.SubspaceLatticeEdges.SubspaceEdge K n

abbrev RankEdge (K : Type*) [Field K] [Fintype K] (n i : ℕ) :=
  {e : EdgeFlag K n //
    e ∈ MathlibPlus.Open.Combinatorics.SubspaceLatticeEdges.edgeRankSet
      (K := K) (n := n) i}

private def subspaceCover {K : Type*} [Field K] [Fintype K] {n : ℕ}
    (L U : Submodule K (Fin n → K)) : Prop :=
  L < U ∧ ∀ M : Submodule K (Fin n → K), L ≤ M → M ≤ U → M = L ∨ M = U

private def simultaneousCover {K : Type*} [Field K] [Fintype K] {n : ℕ}
    (a b : EdgeFlag K n) : Prop :=
  subspaceCover a.1.1 b.1.1 ∧ subspaceCover a.1.2 b.1.2

private def raisingMatrix {K : Type*} [Field K] [Fintype K]
    (n i : ℕ) : Matrix (RankEdge K n i) (RankEdge K n (i + 1)) ℚ :=
  fun e f => @ite ℚ (simultaneousCover e.1 f.1)
    (Classical.propDecidable _) 1 0

private def pathMatrix {K : Type*} [Field K] [Fintype K]
    (n i d : ℕ) : Matrix (RankEdge K n i) (RankEdge K n (i + d)) ℚ :=
  match d with
  | 0 => 1
  | d + 1 =>
      pathMatrix n i d * raisingMatrix n (i + d)

private def complementaryMap {K : Type*} [Field K] [Fintype K]
    (n i : ℕ) :
    (RankEdge K n i → ℚ) →ₗ[ℚ]
      (RankEdge K n (i + (n - 1 - 2 * i)) → ℚ) :=
  (pathMatrix n i (n - 1 - 2 * i)).transpose.mulVecLin

private def unitaryPeck {K : Type*} [Field K] [Fintype K]
    (n : ℕ) : Prop :=
  ∀ i : ℕ, 2 * i ≤ n - 1 →
    Function.Bijective (complementaryMap (K := K) n i)

private def universalUnitaryPeck : Prop :=
  ∀ (q n : ℕ) (K : Type) [Field K] [Fintype K],
    MathlibPlus.Open.Combinatorics.SubspaceLatticeEdges.IsPrimePower q →
      Fintype.card K = q → 0 < n → unitaryPeck (K := K) n

abbrev F2 := ZMod 2
abbrev V := Fin 2 → F2
abbrev EdgeFlag2 := EdgeFlag F2 2
abbrev RankEdge02 := RankEdge F2 2 0
abbrev RankEdge12 := RankEdge F2 2 1

private def v10 : V := ![1, 0]
private def v01 : V := ![0, 1]
private def v11 : V := ![1, 1]

private def lineVector (j : Fin 3) : V :=
  if j = 0 then v10 else if j = 1 then v01 else v11

private def line (j : Fin 3) : Submodule F2 V :=
  if j = 0 then Submodule.span F2 ({v10} : Set V)
  else if j = 1 then Submodule.span F2 ({v01} : Set V)
  else Submodule.span F2 ({v11} : Set V)

private def listedLineDescription : Prop :=
  ∀ j : Fin 3, ∀ x : V,
    x ∈ line j ↔ x = 0 ∨ x = lineVector j

private def lineSet : Set (Submodule F2 V) := {L | Module.finrank F2 L = 1}

private def edgeZero (e : EdgeFlag2) : Prop :=
  e.1.1 = ⊥ ∧ Module.finrank F2 e.1.2 = 1

private def edgeOne (e : EdgeFlag2) : Prop :=
  Module.finrank F2 e.1.1 = 1 ∧ e.1.2 = ⊤

private def edgeZeroSet : Set EdgeFlag2 := {e | edgeZero e}
private def edgeOneSet : Set EdgeFlag2 := {e | edgeOne e}

private def lowerPair (j : Fin 3) : Submodule F2 V × Submodule F2 V :=
  (⊥, line j)

private def upperPair (j : Fin 3) : Submodule F2 V × Submodule F2 V :=
  (line j, ⊤)

private def J3Int : Matrix (Fin 3) (Fin 3) ℤ := fun _ _ => 1
private def J3 : Matrix (Fin 3) (Fin 3) ℚ := J3Int.map (Int.castRingHom ℚ)

private def incidenceMatrix
    (lower : Fin 3 ≃ RankEdge02) (upper : Fin 3 ≃ RankEdge12) :
    Matrix (Fin 3) (Fin 3) ℚ :=
  fun j k => pathMatrix 2 0 1 (lower j) (upper k)

private def j3Certificate : Prop :=
  Matrix.det J3 = 0 ∧
    Matrix.rank J3 = 1 ∧
    1 < 3 ∧
    ¬ Function.Bijective J3.mulVecLin ∧
    ∃ (lower : Fin 3 ≃ RankEdge02) (upper : Fin 3 ≃ RankEdge12),
      (∀ j : Fin 3, (lower j).1.1 = lowerPair j) ∧
      (∀ k : Fin 3, (upper k).1.1 = upperPair k) ∧
      incidenceMatrix lower upper = J3 ∧
      ¬ Function.Bijective (complementaryMap (K := F2) 2 0)

private def lineEnumeration : Prop :=
  listedLineDescription ∧
    Set.Finite lineSet ∧ Set.ncard lineSet = 3 ∧
    (∀ j : Fin 3, Module.finrank F2 (line j) = 1) ∧
    (∀ L : {L : Submodule F2 V // Module.finrank F2 L = 1},
      ∃ j : Fin 3, L.1 = line j) ∧
    (∀ j k : Fin 3, line j = line k → j = k)

private def edgeLevelEnumeration : Prop :=
  Set.Finite edgeZeroSet ∧ Set.ncard edgeZeroSet = 3 ∧
    Set.Finite edgeOneSet ∧ Set.ncard edgeOneSet = 3 ∧
    (∀ j : Fin 3, ∃ e : EdgeFlag2, edgeZero e ∧ e.1 = lowerPair j) ∧
    (∀ e : EdgeFlag2, edgeZero e → ∃ j : Fin 3, e.1 = lowerPair j) ∧
    (∀ j : Fin 3, ∃ e : EdgeFlag2, edgeOne e ∧ e.1 = upperPair j) ∧
    (∀ e : EdgeFlag2, edgeOne e → ∃ j : Fin 3, e.1 = upperPair j)

private def edgePairOrder
    (a b : Submodule F2 V × Submodule F2 V) : Prop :=
  a.1 ≤ b.1 ∧ a.2 ≤ b.2

private def simultaneousCoverPair
    (a b : Submodule F2 V × Submodule F2 V) : Prop :=
  subspaceCover a.1 b.1 ∧ subspaceCover a.2 b.2

private def completeF2CoverBlock : Prop :=
  (∀ j k : Fin 3,
    simultaneousCoverPair (lowerPair j) (upperPair k)) ∧
    (∀ j k : Fin 3,
      edgePairOrder (lowerPair j) (upperPair k))

private def rankWitness : Prop :=
  2 - 1 = 1 ∧ ∀ i : ℕ, 2 * i ≤ 1 ↔ i = 0

/-- Claim 45586: the exact `E(B₂(2))` rational complementary map is the
all-ones `J₃` map and is singular, refuting the all-prime-power universal
unitary-Peck assertion at `(q,n) = (2,2)`. -/
def claim45586 : Prop :=
  Fintype.card V = 4 ∧
    lineEnumeration ∧
    edgeLevelEnumeration ∧
    completeF2CoverBlock ∧
    rankWitness ∧
    j3Certificate ∧
    ¬ unitaryPeck (K := F2) 2 ∧
    MathlibPlus.Open.Combinatorics.SubspaceLatticeEdges.IsPrimePower 2 ∧
    Fintype.card F2 = 2 ∧
    0 < 2 ∧
    ¬ universalUnitaryPeck

end
end MathlibPlus.Open.ResearchFormalization.R2965Claim45586
