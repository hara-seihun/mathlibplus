import Mathlib

namespace MathlibPlus.Open.Combinatorics

/-- The graph carried by the star of `v`, with isolated vertices removed. -/
private def starGraph {V : Type*} (Y : SimpleGraph V) (v : V) :
    SimpleGraph {x // x ∈ ({v} ∪ {u | Y.Adj v u} : Set V)} :=
  SimpleGraph.fromRel (fun x y ↦
    Y.Adj x.1 y.1 ∧ (x.1 = v ∨ y.1 = v))

/-- The graph carried by `star(v) + {a,b}`, with isolated vertices removed. -/
private def starPlusGraph {V : Type*} (Y : SimpleGraph V) (v a b : V) :
    SimpleGraph {x // x ∈ ({v} ∪ {u | Y.Adj v u} ∪ {a, b} : Set V)} :=
  SimpleGraph.fromRel (fun x y ↦
    Y.Adj x.1 y.1 ∧
      ((x.1 = v ∨ y.1 = v) ∨
        ((x.1 = a ∧ y.1 = b) ∨ (x.1 = b ∧ y.1 = a))))

/--
At minimum degree one, a pendant edge can make an attachment term have the
same first-component type as a genuine degree-two card.  Here `pathGraph 3`
is the `P₃ ≅ K₁,₂` type, and the final clause records the resulting overlap
with the degree-two star family.
-/
def pendantCollisionSecondLayer {V : Type*} [Fintype V] : Prop := by
  classical
  exact ∀ (Y : SimpleGraph V),
    Y.minDegree = 1 →
      ∀ (v c : V),
        (Y.degree v = 1 ∧ Y.Adj v c ∧ ∀ u, Y.Adj v u → u = c) →
          ∀ (a b : V),
            a ≠ v → b ≠ v → Y.Adj a b →
              (Nonempty (starPlusGraph Y v a b ≃g SimpleGraph.pathGraph 3) ↔
                  (a = c ∨ b = c)) ∧
                ((a = c ∨ b = c) →
                  ((∃ w : V, Y.degree w = 2) →
                    ∃ w : V, Y.degree w = 2 ∧
                      Nonempty (starPlusGraph Y v a b ≃g starGraph Y w)))

end MathlibPlus.Open.Combinatorics
