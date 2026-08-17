import MathlibPlus.Open.VoltageLiftedOrbitFormula6051

namespace MathlibPlus.Open.LiftedOrbit

/-- Claim 6050: every selected spanning-tree path family gives the
path-accumulated voltage potential on its base orbit, with zero value at the
selected basepoint. -/
def spanningTreePotential_claim6050 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime],
    ∀ (B : Type*) [Fintype B] (I : Type*)
      (r : I → Equiv.Perm B) (β : I → B → ZMod p) (b₀ : B)
      (paths : SpanningTreePaths r b₀),
      let O := baseOrbit r b₀
      let t_O := treePotential r β b₀ paths
      b₀ ∈ O ∧
        (∀ b : B, b ∈ O → baseWord r (paths.path b) b₀ = b) ∧
        t_O b₀ = 0 ∧
        ∀ b : B, b ∈ O →
          t_O b = (liftWord r β (paths.path b) (0, b₀)).1

end MathlibPlus.Open.LiftedOrbit
