import Mathlib

noncomputable section
open scoped BigOperators Topology
open MeasureTheory Filter

namespace MathlibPlus.Open.ResearchFormalization.Batch01a00310.BatchDeletion

variable {V : Type*} [DecidableEq V]

def independent (F : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ ⦃u v : V⦄, u ∈ S → v ∈ S → u ≠ v → ¬ F.Adj u v

def deletionMultiplicity (F : SimpleGraph V) (_hF : F.IsAcyclic)
    (R J : Finset V) : ℕ := by
  classical
  exact (J.filter (fun v => independent F (J.erase v) ∧ Disjoint (J.erase v) R)).card

end MathlibPlus.Open.ResearchFormalization.Batch01a00310.BatchDeletion
