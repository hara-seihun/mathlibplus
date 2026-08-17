import Mathlib
import MathlibPlus.Algebra.EdgeOverlap

open scoped BigOperators

namespace MathlibPlus.Open.Algebra.EdgeOverlapCocycle19665

noncomputable section

open MathlibPlus.Algebra.EdgeOverlap

/-- The square-zero fibre of the complete-graph edge-overlap module. -/
abbrev ZeroEdgeModule (n : ℕ) :=
  Finsupp (Finset (CompleteGraphEdge n)) ℚ

/-- Multiplication of square-free edge monomials at `t=0`. -/
def zeroBasisProduct {n : ℕ}
    (A B : Finset (CompleteGraphEdge n)) : ZeroEdgeModule n :=
  if Disjoint A B then
    Finsupp.single (A ∪ B) 1
  else
    0

/-- The bilinear square-zero product. -/
def zeroStar {n : ℕ}
    (f g : ZeroEdgeModule n) : ZeroEdgeModule n :=
  f.sum (fun A a =>
    g.sum (fun B b => (a * b) • zeroBasisProduct A B))

/-- The one-edge collision bracket on square-free edge monomials. -/
def collisionBasis {n : ℕ}
    (A B : Finset (CompleteGraphEdge n)) : ZeroEdgeModule n :=
  if (A ∩ B).card = 1 then
    Finsupp.single (A ∪ B) 1
  else
    0

/-- The bilinear first-overlap collision bracket. -/
def collisionBracket {n : ℕ}
    (f g : ZeroEdgeModule n) : ZeroEdgeModule n :=
  f.sum (fun A a =>
    g.sum (fun B b => (a * b) • collisionBasis A B))

/-- Claim 19665: the first-overlap bracket is a Hochschild cocycle and a
biderivation for the square-zero product. -/
def hochschildCocycleAndBiderivation_claim19665 : Prop :=
  ∀ (n : ℕ) (f g h : ZeroEdgeModule n),
    (zeroStar f (collisionBracket g h) -
        collisionBracket (zeroStar f g) h +
      collisionBracket f (zeroStar g h) -
        zeroStar (collisionBracket f g) h = 0) ∧
      collisionBracket (zeroStar f g) h =
        zeroStar f (collisionBracket g h) +
          zeroStar g (collisionBracket f h) ∧
      collisionBracket f (zeroStar g h) =
        zeroStar g (collisionBracket f h) +
          zeroStar h (collisionBracket f g)

end

end MathlibPlus.Open.Algebra.EdgeOverlapCocycle19665
