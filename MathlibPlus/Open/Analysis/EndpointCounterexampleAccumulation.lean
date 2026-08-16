import Mathlib

open scoped Topology

namespace MathlibPlus.Open.Analysis.EndpointCounterexample

def onlyAccumulationPoint : Prop :=
  let E : Set ℝ := {x | ∃ n : ℕ, 1 ≤ n ∧ x = (1 : ℝ) + 1 / (n : ℝ)}
  let derived : Set ℝ :=
    {x | Filter.NeBot (𝓝[≠] x ⊓ Filter.principal E)}
  derived = ({1} : Set ℝ)

def relativeClosed : Prop :=
  let E : Set ℝ := {x | ∃ n : ℕ, 1 ≤ n ∧ x = (1 : ℝ) + 1 / (n : ℝ)}
  IsClosed (Set.preimage (fun x : Set.Ioi (1 : ℝ) => (x : ℝ)) E)

end MathlibPlus.Open.Analysis.EndpointCounterexample
