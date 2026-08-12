import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Combinatorics.SimpleGraph.Copy

namespace MathlibPlus.Algebra.EdgeOverlap

noncomputable section

/-- The edge type of the complete graph on `Fin n`, i.e. `E(K_n)`. -/
abbrev CompleteGraphEdge (n : ℕ) :=
  SimpleGraph.edgeSet (⊤ : SimpleGraph (Fin n))

/-- The free `ℚ[t]`-module on edge subsets of `K_n`. -/
abbrev EdgeModule (n : ℕ) := Finsupp (Finset (CompleteGraphEdge n)) (Polynomial ℚ)

/-- The basis product from admitted claim 19659. -/
def basisProduct {n : ℕ}
    (A B : Finset (CompleteGraphEdge n)) : EdgeModule n :=
  Finsupp.single (A ∪ B) ((Polynomial.X : Polynomial ℚ) ^ (A ∩ B).card)

/-- The bilinear extension of the edge-overlap basis product. -/
def star {n : ℕ}
    (f g : EdgeModule n) : EdgeModule n :=
  f.sum (fun A a =>
    g.sum (fun B b => (a * b) • basisProduct A B))

/-- On basis vectors, `star` is exactly the displayed overlap formula. -/
theorem star_single_single {n : ℕ}
    (A B : Finset (CompleteGraphEdge n)) :
    star (Finsupp.single A 1) (Finsupp.single B 1) = basisProduct A B := by
  classical
  simp [star, basisProduct]

end

end MathlibPlus.Algebra.EdgeOverlap
