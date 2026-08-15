import Mathlib

noncomputable section
open MeasureTheory
open scoped BigOperators Interval

namespace MathlibPlus.Open.ResearchBatch.D0014

variable {V : Type*} [Fintype V] [DecidableEq V]

def SimpleEdge (V : Type*) [DecidableEq V] := {e : Finset V // e.card = 2}

def edgeAction (sigma : Equiv.Perm V) (e : SimpleEdge V) : SimpleEdge V :=
  ⟨e.1.image sigma, by
    simpa [Finset.card_image_of_injective _ sigma.injective] using e.2⟩

structure CardCocycle (V : Type*) [Fintype V] [DecidableEq V] where
  pi : V → Equiv.Perm V
  fixes : ∀ i, pi i i = i

def constraintMultiplicity (cocycle : CardCocycle V) (e f : SimpleEdge V) : ℕ :=
  (by classical
    exact (Finset.univ.filter (fun i : V =>
      i ∉ e.1 ∧ edgeAction (cocycle.pi i) e = f)).card)

def constraintMultiplicity_claim4444 (cocycle : CardCocycle V)
    (e f : SimpleEdge V) : ℕ := by
  classical
  exact (Finset.univ.filter (fun i : V =>
    i ∉ e.1 ∧ edgeAction (cocycle.pi i) e = f)).card

end MathlibPlus.Open.ResearchBatch.D0014
