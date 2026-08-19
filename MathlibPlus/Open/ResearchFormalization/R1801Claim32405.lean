import Mathlib
import MathlibPlus.Open.ResearchFormalization.R1801

namespace MathlibPlus.Open.ResearchFormalization.R1801Claim32405

noncomputable section

open MathlibPlus.Open.ResearchFormalization.R1801

abbrev Tree := MathlibPlus.Open.ResearchFormalization.R1801.RootedTree
abbrev Poly := MathlibPlus.Open.ResearchFormalization.R1801.Poly

def isSymmetricDifferenceForest (S : List Tree) : Prop :=
  S.Nodup

def exactlyTwoMaximalFactors (S : List Tree) (n : ℕ)
    (B₁ B₂ : Tree) : Prop :=
  isSymmetricDifferenceForest S ∧
    B₁ ∈ S ∧
      B₂ ∈ S ∧
        B₁ ≠ B₂ ∧
          order B₁ = n ∧
            order B₂ = n ∧
              (∀ R ∈ S, order R ≤ n) ∧
                (∀ R ∈ S, order R = n → R = B₁ ∨ R = B₂)

def reverseSignatureCollision (W : ℕ) (B₁ B₂ : Tree) : Prop :=
  ∀ k : ℕ, k < W →
    (Lambda B₁ + Lambda B₂).coeff k = 0

def delayedDegreeCondition (n W : ℕ) (B₁ B₂ : Tree) : Prop :=
  (f B₁ + f B₂).natDegree ≤ 2 * n - W - 1

def pathForest : ℕ → List Tree
  | 0 => []
  | k + 1 =>
      [MathlibPlus.Open.ResearchFormalization.R1801.RootedTree.node (pathForest k)]

def pathChild (k : ℕ) : Tree :=
  MathlibPlus.Open.ResearchFormalization.R1801.RootedTree.node (pathForest k)

def witnessA (n : ℕ) : Tree :=
  MathlibPlus.Open.ResearchFormalization.R1801.RootedTree.node
    [MathlibPlus.Open.ResearchFormalization.R1801.RootedTree.node [],
      pathChild (n - 3)]

def witnessQ (n : ℕ) : Tree :=
  MathlibPlus.Open.ResearchFormalization.R1801.RootedTree.node
    (MathlibPlus.Open.ResearchFormalization.R1801.RootedTree.node [] ::
      if n = 3 then [] else [pathChild (n - 4)])

def witnessB (n : ℕ) : Tree :=
  MathlibPlus.Open.ResearchFormalization.R1801.RootedTree.node [witnessQ n]

def witnessDifference (n : ℕ) : Poly :=
  Polynomial.X * Polynomial.C u * Polynomial.C (s ^ (n - 3)) *
    (Polynomial.X + Polynomial.C (u + s))

def survivingTwoMaximalPacket (n : ℕ) : Prop :=
  exactlyTwoMaximalFactors [witnessA n, witnessB n] n
      (witnessA n) (witnessB n) ∧
    f (witnessA n) + f (witnessB n) = witnessDifference n ∧
      (f (witnessA n) + f (witnessB n)).natDegree = 2 ∧
        delayedDegreeCondition n n (witnessA n) (witnessB n) ∧
          2 ≤ n - 1

/-- Claim 32405: agreement of the lower reverse-signature coefficients in a
symmetric-difference packet with exactly two maximal order-`n` factors forces
the delayed-collar degree bound; the explicit leaf-path packet shows that the
bound alone does not exclude such a residue. -/
def claim32405 : Prop :=
  (∀ (S : List Tree) (W n : ℕ) (B₁ B₂ : Tree),
    exactlyTwoMaximalFactors S n B₁ B₂ →
      reverseSignatureCollision W B₁ B₂ →
        delayedDegreeCondition n W B₁ B₂) ∧
    (∀ n : ℕ, 3 ≤ n → survivingTwoMaximalPacket n)

end

end MathlibPlus.Open.ResearchFormalization.R1801Claim32405
