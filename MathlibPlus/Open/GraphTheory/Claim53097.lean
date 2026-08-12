import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Algebra.Order.Ring.Rat

namespace MathlibPlus.Open.GraphTheory

/--
Claim 53097.  The endpoint maps `src` and `dst` represent an undirected
multigraph: the edge type is not quotiented, so parallel edges are retained.
An orientation is a Boolean choice of which endpoint is the tail, and the
incidence convention is head inflow minus tail outflow.  The phrase "allowed
off-path repair cells" in the source supplies the available edge set; no
additional, unspecified forbidden-edge predicate is silently introduced.
-/
def rationalFlowComponentCriterionClaim53097 : Prop :=
  ∀ {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (src dst : E → V) (d : V → Rat),
    let F : SimpleGraph V :=
      SimpleGraph.fromRel (fun u v ↦
        ∃ e : E, src e = u ∧ dst e = v)
    let incidence : (E → Bool) → (E → Rat) → V → Rat := fun orient r v ↦
      Finset.univ.sum (fun e : E ↦
        (if (if orient e = true then dst e else src e) = v then r e else 0) -
          (if (if orient e = true then src e else dst e) = v then r e else 0))
    (∃ orient : E → Bool, ∃ r : E → Rat,
        (∀ e : E, 0 ≤ r e) ∧
          ∀ v : V, incidence orient r v = d v) ↔
      ∀ C : F.ConnectedComponent,
        ∑ v : C.supp, d v = 0

end MathlibPlus.Open.GraphTheory
