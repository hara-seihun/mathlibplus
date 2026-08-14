import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.Q0038

noncomputable section

/-- The two-element symmetric group used in the sign example. -/
private abbrev STwo := Equiv.Perm (Fin 2)

/-- The scalar action of `S₂` on its one-dimensional sign representation. -/
private def signScalar {K : Type*} [Field K] (g : STwo) : K :=
  ((Equiv.Perm.sign g : ℤ) : K)

private def signAction {K : Type*} [Field K] (g : STwo) : K →ₗ[K] K :=
  (LinearMap.id : K →ₗ[K] K).smulRight (signScalar g)

/-- Fixed vectors for a specified linear action of `S₂` on a module. -/
private def fixedSubmodule {K : Type*} [Field K] {M : Type*}
    [AddCommGroup M] [Module K M]
    (ρ : STwo → M →ₗ[K] M) : Submodule K M :=
  ⨅ g : STwo, LinearMap.ker (ρ g - LinearMap.id)

/-- The diagonal action on the tensor product of two sign representations. -/
private def tensorSignAction {K : Type*} [Field K] (g : STwo) :
    TensorProduct K K K →ₗ[K] TensorProduct K K K :=
  TensorProduct.map (signAction g) (signAction g)

/--
The concrete `S₂`, `V = W = sgn` counterexample to taking invariants separately:
the tensor product of the two invariant subspaces is zero, whereas the invariant
subspace of the diagonal tensor product is one-dimensional (the trivial line).
The `NeZero (2 : K)` hypothesis is the characteristic-not-two condition.
-/
def invariantTakingNotMonoidal {K : Type*} [Field K] [NeZero (2 : K)] : Prop :=
  Subsingleton
      (TensorProduct K (fixedSubmodule (signAction (K := K)))
        (fixedSubmodule (signAction (K := K)))) ∧
    Nonempty
      ((fixedSubmodule (tensorSignAction (K := K))) ≃ₗ[K] K)

end
end MathlibPlus.Open.ResearchFormalization.Q0038
