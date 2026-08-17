import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R0872

noncomputable section

private abbrev Arm (V : Type*) := V × V

private def touchedBlockCount {V : Type*} [Fintype V] [DecidableEq V]
    (Z : V → Finset (Arm V)) (A : Finset (Arm V)) : ℕ :=
  (Finset.univ.filter (fun v => (A ∩ Z v).Nonempty)).card

private def branchDefect {V : Type*} [Fintype V] [DecidableEq V]
    (Z : V → Finset (Arm V)) (A : Finset (Arm V)) : ℤ :=
  (A.card : ℤ) - (touchedBlockCount Z A : ℤ)

private def graphDegree {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (v : V) : ℕ :=
  Nat.card {w : V // G.Adj v w}

private def reducedSubcubicArmBlocks
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (Z : V → Finset (Arm V)) : Prop :=
  G.IsTree ∧
    (∀ v : V, graphDegree G v ≤ 3) ∧
    (∀ v : V, graphDegree G v ≠ 2) ∧
    (∀ v w : V, v ≠ w → Disjoint (Z v) (Z w)) ∧
    (∀ v : V, ∀ e : Arm V,
      e ∈ Z v ↔
        graphDegree G v = 3 ∧ e.1 = v ∧ G.Adj e.1 e.2 ∧
          graphDegree G e.2 = 1)

/-- Claim 29631: on the actual finite arm carrier of a reduced subcubic
skeleton, zero branch defect is exactly partition independence. -/
def claim29631 : Prop :=
  ∀ (V : Type*) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (Z : V → Finset (Arm V)),
    reducedSubcubicArmBlocks G Z →
      ∀ A : Finset (Arm V),
        A ⊆ (Finset.univ : Finset V).biUnion Z →
          (branchDefect Z A = 0 ↔
            ∀ v : V, (A ∩ Z v).card ≤ 1)

end

end MathlibPlus.Open.ResearchFormalization.R0872
