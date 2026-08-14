import Mathlib

<<<<<<< ours
open scoped Filter Topology

namespace MathlibPlus.Open.Research

def nonzero_abel_flat_mode : Prop :=
  let f : ℝ → ℝ := fun x =>
    if x < 1 then Real.exp (-(1 + x) / (1 - x)) else 0
  (∃ x : ℝ, f x ≠ 0) ∧
    ContDiffAt ℝ ⊤ f 1 ∧
    ∀ n : ℕ, iteratedDeriv n f 1 = 0

def finite_dirichlet_atoms_no_identity : Prop :=
  ∀ (m : ℕ) (n : Fin m → ℕ) (c : Fin m → ℂ) (E : Set ℂ),
    (∀ j, 0 < n j) →
    Function.Injective n →
    (∃ z : ℂ, AccPt z (𝓟 E)) →
    (∀ s ∈ E, ∑ j : Fin m, c j * Complex.cpow (n j : ℂ) (-s) = 0) →
    ∀ j, c j = 0
=======
namespace MathlibPlus.Open.Research

/--
For a finite simple graph, three distinct vertex-deletion cards collectively retain
 every host edge.  The card obtained by deleting `deleted` retains exactly the
edges whose two endpoints differ from `deleted`.
-/
def claim_23220 : Prop :=
  ∀ {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u v w : V),
    u ≠ v → u ≠ w → v ≠ w →
      ∀ {x y : V}, G.Adj x y →
        ∃ deleted ∈ ({u, v, w} : Finset V),
          x ≠ deleted ∧ y ≠ deleted
>>>>>>> theirs

end MathlibPlus.Open.Research
