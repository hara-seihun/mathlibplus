import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalizationBatch01

noncomputable section

inductive RootedTree where
  | node (branches : List RootedTree)

mutual
  def rootedOrderList : List RootedTree → ℕ
    | [] => 0
    | T :: Ts => rootedOrder T + rootedOrderList Ts

  def rootedOrder : RootedTree → ℕ
    | .node branches => 1 + rootedOrderList branches
end

abbrev TreePolynomial := MvPolynomial (Fin 3) ℚ

def uVariable : TreePolynomial := MvPolynomial.X 0
def rhoVariable : TreePolynomial := MvPolynomial.X 1
def wVariable : TreePolynomial := MvPolynomial.X 2

mutual
  def rootedFactors : List RootedTree → TreePolynomial
    | [] => 1
    | T :: Ts => rootedContextFactor T * rootedFactors Ts

  def rootedContextFactor : RootedTree → TreePolynomial
    | .node branches =>
        uVariable * (uVariable + rhoVariable) ^ (rootedOrder (.node branches) - 1) +
          wVariable * rootedFactors branches
end

def treeEvaluation (u rho w : ℚ) (P : TreePolynomial) : ℚ :=
  MvPolynomial.eval
    (fun i => if i = 0 then u else if i = 1 then rho else w) P

/-- The two universal corners of the rooted context-factor recurrence. -/
def claim49682 : Prop :=
  ∀ T : RootedTree,
    (∀ (rho w : ℚ),
      treeEvaluation 0 rho w (rootedContextFactor T) = w ^ rootedOrder T) ∧
    (∀ (u rho : ℚ),
      treeEvaluation u rho rho (rootedContextFactor T) =
        (u + rho) ^ rootedOrder T)

end
end MathlibPlus.Open.ResearchFormalizationBatch01
