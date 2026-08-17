import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1356Claim38166

abbrev FiberSet (X : Type*) := ZMod 5 × X

private def switchingEquiv {X : Type*} (u : X → ZMod 5) : Equiv.Perm (FiberSet X) :=
  let swap : FiberSet X ≃ X × ZMod 5 := Equiv.prodComm (ZMod 5) X
  let sigma : (_x : X) × ZMod 5 ≃ X × ZMod 5 :=
    Equiv.sigmaEquivProd X (ZMod 5)
  let fibre : (_x : X) × ZMod 5 ≃ (_x : X) × ZMod 5 :=
    Equiv.sigmaCongrRight (fun x => Equiv.addRight (u x))
  swap.trans (sigma.symm.trans (fibre.trans (sigma.trans swap.symm)))

private def switchedVoltagePresentation {X : Type*}
    (Γ : SimpleGraph (FiberSet X)) (s : Equiv.Perm (FiberSet X)) :
    SimpleGraph (FiberSet X) :=
  SimpleGraph.fromRel (fun a b => Γ.Adj (s.symm a) (s.symm b))

private def graphIsomorphism {X : Type*}
    (Γ Δ : SimpleGraph (FiberSet X)) (s : Equiv.Perm (FiberSet X)) : Prop :=
  ∀ a b, Γ.Adj a b ↔ Δ.Adj (s a) (s b)

private def graphAutomorphism {X : Type*}
    (Γ : SimpleGraph (FiberSet X)) (f : Equiv.Perm (FiberSet X)) : Prop :=
  ∀ a b, Γ.Adj a b ↔ Γ.Adj (f a) (f b)

private def graphAutomorphismSet {X : Type*}
    (Γ : SimpleGraph (FiberSet X)) : Set (Equiv.Perm (FiberSet X)) :=
  {f | graphAutomorphism Γ f}

private def conjugateSet {X : Type*}
    (s : Equiv.Perm (FiberSet X))
    (R : Set (Equiv.Perm (FiberSet X))) : Set (Equiv.Perm (FiberSet X)) :=
  {g | ∃ r, r ∈ R ∧ g = s * r * s⁻¹}

private def isPermutationSubgroup {X : Type*}
    (R : Set (Equiv.Perm (FiberSet X))) : Prop :=
  1 ∈ R ∧
    (∀ a, a ∈ R → ∀ b, b ∈ R → a * b ∈ R) ∧
    (∀ a, a ∈ R → a⁻¹ ∈ R)

private def isRegularPermutationSubgroup {X : Type*}
    (R : Set (Equiv.Perm (FiberSet X))) : Prop :=
  isPermutationSubgroup R ∧
    ∀ a b : FiberSet X, ∃! r, r ∈ R ∧ r a = b

private def containedInAutomorphisms {X : Type*}
    (Γ : SimpleGraph (FiberSet X))
    (R : Set (Equiv.Perm (FiberSet X))) : Prop :=
  ∀ r, r ∈ R → graphAutomorphism Γ r

private def conjugateInsideAutomorphisms {X : Type*}
    (Γ : SimpleGraph (FiberSet X))
    (R S : Set (Equiv.Perm (FiberSet X))) : Prop :=
  ∃ c, graphAutomorphism Γ c ∧
    ∀ s, s ∈ S ↔ ∃ r, r ∈ R ∧ s = c * r * c⁻¹

/-- Claim 38166: block switching is a graph isomorphism to the switched
voltage presentation, and conjugation by it carries every regular subgroup
and every complete-automorphism conjugacy relation to the switched graph. -/
def switchingIsomorphismPreservesRegularSubgroupConjugacy : Prop :=
  ∀ (X : Type*) [Fintype X]
    (Γ : SimpleGraph (FiberSet X)) (u : X → ZMod 5),
    let s := switchingEquiv u
    let switchedΓ := switchedVoltagePresentation Γ s
    (∀ z : ZMod 5, ∀ x : X, s (z, x) = (z + u x, x)) ∧
    graphIsomorphism Γ switchedΓ s ∧
    (∀ g : Equiv.Perm (FiberSet X),
      graphAutomorphism switchedΓ g ↔ g ∈ conjugateSet s (graphAutomorphismSet Γ)) ∧
    (∀ R : Set (Equiv.Perm (FiberSet X)),
      isRegularPermutationSubgroup R →
      containedInAutomorphisms Γ R →
      isRegularPermutationSubgroup (conjugateSet s R) ∧
      containedInAutomorphisms switchedΓ (conjugateSet s R)) ∧
    (∀ R S : Set (Equiv.Perm (FiberSet X)),
      isRegularPermutationSubgroup R →
      isRegularPermutationSubgroup S →
      containedInAutomorphisms Γ R →
      containedInAutomorphisms Γ S →
      (conjugateInsideAutomorphisms Γ R S ↔
        conjugateInsideAutomorphisms switchedΓ
          (conjugateSet s R) (conjugateSet s S)))

end MathlibPlus.Open.ResearchFormalization.R1356Claim38166
