import Mathlib
import MathlibPlus.Open.ResearchFormalizationBatch_019ffee2

namespace MathlibPlus.Open.Research.R2643TreeComplement42114

noncomputable section

open Polynomial


def qTraceZ : Polynomial ℤ :=
  X ^ 7 - 8 * X ^ 5 + 19 * X ^ 3 - 12 * X + 1

def qTraceQ : Polynomial ℚ :=
  qTraceZ.map (algebraMap ℤ ℚ)

def qTraceComplex : Polynomial ℂ :=
  qTraceZ.map (algebraMap ℤ ℂ)

def treeAdjacencyMatrix (n : ℕ) (G : SimpleGraph (Fin n)) :
    Matrix (Fin n) (Fin n) ℤ :=
  @SimpleGraph.adjMatrix ℤ (Fin n) G (Classical.decRel G.Adj)
    (inferInstance : Zero ℤ) (inferInstance : One ℤ)

def treeCharpolyZ (n : ℕ) (G : SimpleGraph (Fin n)) : Polynomial ℤ :=
  Matrix.charpoly (treeAdjacencyMatrix n G)

def treeCharpolyQ (n : ℕ) (G : SimpleGraph (Fin n)) : Polynomial ℚ :=
  (treeCharpolyZ n G).map (algebraMap ℤ ℚ)

def qRootIsTotallyRealAlgebraicInteger (α : ℂ) : Prop :=
  IsIntegral ℤ α ∧
    IsAlgebraic ℚ α ∧
    ∀ z : ℂ,
      IsRoot ((minpoly ℚ α).map (algebraMap ℚ ℂ)) z → z.im = 0

def rootsInTraceInterval (C : Polynomial ℤ) : Prop :=
  ∀ z : ℂ,
    IsRoot (C.map (algebraMap ℤ ℂ)) z →
      z.im = 0 ∧ -2 ≤ z.re ∧ z.re ≤ 2

def integerSymmetricComplementObstruction : Prop :=
  ¬ ∃ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℤ) (C : Polynomial ℤ),
    M.IsSymm ∧ rootsInTraceInterval C ∧
      Matrix.charpoly M = qTraceZ * C

def treeComplementObstruction : Prop :=
  ¬ ∃ (n : ℕ) (G : SimpleGraph (Fin n)) (C : Polynomial ℤ),
    G.IsTree ∧ rootsInTraceInterval C ∧
      treeCharpolyZ n G = qTraceZ * C

/-- Claim 42114: the exact trace polynomial has a root whose minimal
polynomial is that polynomial, the finite-tree theorem is specialized to
that root and yields a tree whose characteristic polynomial is divisible by
`Q`, while the exact integer-symmetric complement obstruction still rules out
an interval-rooted complementary factor, including for trees. -/
def claim42114_treeRealizationDoesNotControlComplement : Prop :=
  MathlibPlus.Open.claim_42105 ∧
    MathlibPlus.Open.claim_42106 ∧
    MathlibPlus.Open.claim_42110 ∧
    (∃ α : ℂ,
      IsRoot qTraceComplex α ∧
        qRootIsTotallyRealAlgebraicInteger α ∧
        minpoly ℚ α = qTraceQ ∧
        (∃ (n : ℕ) (G : SimpleGraph (Fin n)),
          G.IsTree ∧
            minpoly ℚ α ∣ treeCharpolyQ n G ∧
            qTraceQ ∣ treeCharpolyQ n G)) ∧
    integerSymmetricComplementObstruction ∧
    treeComplementObstruction

end

end MathlibPlus.Open.Research.R2643TreeComplement42114
