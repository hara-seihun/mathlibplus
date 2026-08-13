import Mathlib

namespace MathlibPlus.Open.GraphTheory

/-- The quadratic and cubic bent supports displayed below give an explicit
ordinary undirected Cayley CI defect on the elementary abelian group of order
64.  Their Cayley graphs are isomorphic, but no additive automorphism carries
one support to the other. -/
def elementaryAbelianSixQuadraticCubicCIDefect : Prop :=
  let V := Fin 6 → ZMod 2
  let fQ : V → ZMod 2 := fun x =>
    x 0 * x 1 + x 2 * x 3 + x 4 * x 5
  let fC : V → ZMod 2 := fun x =>
    x 0 * x 1 * x 2 + x 0 * x 3 + x 1 * x 4 + x 2 * x 5
  let SQ : Set V := {x | fQ x = 1}
  let SC : Set V := {x | fC x = 1}
  Set.ncard SQ = 28 ∧
    Set.ncard SC = 28 ∧
    (∃ q : V ≃ V, q 0 = 0 ∧
      ∀ x y : V, -x + y ∈ SQ ↔ -(q x) + q y ∈ SC) ∧
    ¬ ∃ α : V ≃+ V, α '' SQ = SC

end MathlibPlus.Open.GraphTheory
