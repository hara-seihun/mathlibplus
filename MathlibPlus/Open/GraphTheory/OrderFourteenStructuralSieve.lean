import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

open scoped SimpleGraph

namespace MathlibPlus.Open.GraphTheory

/-- Claim 20421: the first order-fourteen vertex-deck counterexample funnel.

The packet's "same full vertex deck" is made literal as equality of the
multiset of vertex-deleted graph isomorphism classes: a permutation of the
vertices matches each deleted card with an isomorphic card. -/
def orderFourteenStructuralSieve_20421 : Prop :=
  ∀ (G H : SimpleGraph (Fin 14)),
    let degreeG : Fin 14 → ℕ := fun v =>
      @Fintype.card {w : Fin 14 // G.Adj v w} (Fintype.ofFinite _)
    let degreeH : Fin 14 → ℕ := fun v =>
      @Fintype.card {w : Fin 14 // H.Adj v w} (Fintype.ofFinite _)
    ¬ Nonempty (SimpleGraph.Iso G H) →
    (∃ e : Equiv.Perm (Fin 14),
      ∀ v : Fin 14,
        Nonempty (SimpleGraph.Iso
          (G.comap (fun x : {x : Fin 14 // x ≠ v} => x.1))
          (H.comap (fun x : {x : Fin 14 // x ≠ e v} => x.1)))) →
    G.Connected ∧ H.Connected ∧
      (Gᶜ).Connected ∧ (Hᶜ).Connected ∧
      (SimpleGraph.cycleGraph 3 ⊑ G) ∧ (SimpleGraph.cycleGraph 3 ⊑ H) ∧
      (SimpleGraph.cycleGraph 4 ⊑ G) ∧ (SimpleGraph.cycleGraph 4 ⊑ H) ∧
      (∃ v : Fin 14, 6 ≤ degreeG v) ∧
      (∃ v : Fin 14, 6 ≤ degreeH v) ∧
      (∃ v : Fin 14, degreeG v ≤ 7) ∧
      (∃ v : Fin 14, degreeH v ≤ 7) ∧
      (∃ e : Equiv.Perm (Fin 14), ∀ v, degreeG v = degreeH (e v)) ∧
      ¬ Set.range degreeG ⊆ ({5, 6} : Set ℕ) ∧
      ¬ Set.range degreeG ⊆ ({6, 7} : Set ℕ) ∧
      ¬ Set.range degreeG ⊆ ({7, 8} : Set ℕ)

end MathlibPlus.Open.GraphTheory
