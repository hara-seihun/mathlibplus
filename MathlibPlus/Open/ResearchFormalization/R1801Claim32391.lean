import MathlibPlus.Open.ResearchFormalization.R1801

namespace MathlibPlus.Open.ResearchFormalization.R1801Claim32391

open MathlibPlus.Open.ResearchFormalization.R1801

abbrev Tree := MathlibPlus.Open.ResearchFormalization.R1801.RootedTree

noncomputable section

/-- The endpoint-rooted path family, with the zero path represented by its
    empty child forest. -/
def leaf : Tree :=
  .node []

def pathTree : ℕ → Tree
  | 0 => leaf
  | k + 1 => .node [pathTree k]

def pathForest : ℕ → List Tree
  | 0 => []
  | k + 1 => [pathTree k]

def aTree (n : ℕ) : Tree :=
  .node (leaf :: pathForest (n - 2))

def qTree (n : ℕ) : Tree :=
  .node (leaf :: pathForest (n - 3))

def bTree (n : ℕ) : Tree :=
  .node [qTree n]

def pairFactorSum (n : ℕ) : Poly :=
  f (aTree n) + f (bTree n)

/-- Claim 32391: the characteristic-two one-exponential specialization has
    the exact quadratic difference at every order `n≥3`. -/
def characteristicTwoQuadraticDifference_claim32391 : Prop :=
  ∀ n : ℕ, 3 ≤ n →
    pairFactorSum n =
      Polynomial.X * Polynomial.C (u * s ^ (n - 3)) *
        (Polynomial.X + Polynomial.C (u + s)) ∧
      (pairFactorSum n).natDegree = 2 ∧
      pairFactorSum n ≠ 0

end

end MathlibPlus.Open.ResearchFormalization.R1801Claim32391
