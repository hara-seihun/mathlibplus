import Mathlib

namespace MathlibPlus.Open.Research.FormalizationBatch1586

open scoped BigOperators
noncomputable section

abbrev ArmLengths := Fin 5 → ℕ
abbrev SpiderVertex (A : ArmLengths) := Option (Σ i : Fin 5, Fin (A i))

/-- Adjacency in the spider with one central vertex and five arms. -/
def spiderAdjacent (A : ArmLengths) : SpiderVertex A → SpiderVertex A → Prop
  | none, some ⟨_, j⟩ => j.val = 0
  | some ⟨_, j⟩, none => j.val = 0
  | some ⟨i, j⟩, some ⟨i', j'⟩ =>
      i = i' ∧ (j.val + 1 = j'.val ∨ j'.val + 1 = j.val)
  | none, none => False

/-- A nonempty vertex set is connected when every two of its vertices are joined
by a walk staying in the set. -/
def spiderConnected (A : ArmLengths) (S : Finset (SpiderVertex A)) : Prop :=
  S.Nonempty ∧
    ∀ u ∈ S, ∀ v ∈ S,
      Relation.ReflTransGen
        (fun x y : SpiderVertex A => x ∈ S ∧ y ∈ S ∧ spiderAdjacent A x y) u v

/-- The connected-subtree size polynomial of the finite spider. -/
def connectedSubtreeSizePolynomial (A : ArmLengths) : Polynomial ℕ := by
  classical
  exact ∑ S : Finset (SpiderVertex A),
    if spiderConnected A S then Polynomial.X ^ S.card else 0

def armF (a : ℕ) : Polynomial ℕ :=
  (Finset.Icc 1 a).sum (fun k => Polynomial.C (a - k + 1) * Polynomial.X ^ k)

def armJ (a : ℕ) : Polynomial ℕ :=
  (Finset.range (a + 1)).sum (fun k => Polynomial.X ^ k)

def fiveArmFormula (A : ArmLengths) : Polynomial ℕ :=
  Finset.univ.sum (fun i : Fin 5 => armF (A i)) +
    Polynomial.X * Finset.univ.prod (fun i : Fin 5 => armJ (A i))

def PositiveArmLengths (A : ArmLengths) : Prop := ∀ i, 0 < A i

/-- Claim 39402: the connected-subtree size polynomial of a five-arm spider. -/
def fiveArmConnectedSubtreePolynomial : Prop :=
  ∀ A : ArmLengths, PositiveArmLengths A →
    connectedSubtreeSizePolynomial A = fiveArmFormula A

end
end MathlibPlus.Open.Research.FormalizationBatch1586
