import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1356Claim38162

abbrev FiberSet (X : Type*) := ZMod 5 × X

private def graphAutomorphism {X : Type*}
    (Γ : SimpleGraph (FiberSet X)) (f : Equiv.Perm (FiberSet X)) : Prop :=
  ∀ a b, Γ.Adj a b ↔ Γ.Adj (f a) (f b)

private def semiregularOnFibers {X : Type*}
    (P : Subgroup (Equiv.Perm (FiberSet X))) : Prop :=
  ∀ p : P, p ≠ 1 → ∀ a : FiberSet X, p.1 a ≠ a

private def graphNormalizer {X : Type*}
    (Γ : SimpleGraph (FiberSet X))
    (P N : Subgroup (Equiv.Perm (FiberSet X))) : Prop :=
  ∀ f : Equiv.Perm (FiberSet X),
    f ∈ N ↔ graphAutomorphism Γ f ∧
      f ∈ Subgroup.normalizer (P : Set (Equiv.Perm (FiberSet X)))

private def pInvariantGraph {X : Type*}
    (Γ : SimpleGraph (FiberSet X))
    (P : Subgroup (Equiv.Perm (FiberSet X))) : Prop :=
  ∀ p : P, ∀ a b, Γ.Adj a b ↔ Γ.Adj (p.1 a) (p.1 b)

private def isSylowFiveIn
    {G : Type*} [Group G] (P : Subgroup G) : Prop :=
  IsPGroup 5 P ∧
    ∀ Q : Subgroup G, IsPGroup 5 Q → P ≤ Q → Q ≤ P

private def affineVoltageCoordinates {X : Type*}
    (N : Subgroup (Equiv.Perm (FiberSet X)))
    (lam : N → (ZMod 5)ˣ) (τ : N → X → ZMod 5)
    (σ : N → Equiv.Perm X) : Prop :=
  ∀ f : N, ∀ z : ZMod 5, ∀ x : X,
    f.1 (z, x) = ((lam f : ZMod 5) * z + τ f x, σ f x)

private def standardFiveCycle {X : Type*}
    (ρ : Equiv.Perm (FiberSet X)) : Prop :=
  ∀ z : ZMod 5, ∀ x : X, ρ (z, x) = (z + 1, x)

private def switchingEquiv {X : Type*} (u : X → ZMod 5) : Equiv.Perm (FiberSet X) :=
  let swap : FiberSet X ≃ X × ZMod 5 := Equiv.prodComm (ZMod 5) X
  let sigma : (_x : X) × ZMod 5 ≃ X × ZMod 5 :=
    Equiv.sigmaEquivProd X (ZMod 5)
  let fibre : (_x : X) × ZMod 5 ≃ (_x : X) × ZMod 5 :=
    Equiv.sigmaCongrRight (fun x => Equiv.addRight (u x))
  swap.trans (sigma.symm.trans (fibre.trans (sigma.trans swap.symm)))

private def isModuloP
    {X : Type*} (P : Subgroup (Equiv.Perm (FiberSet X)))
    (q : Equiv.Perm (FiberSet X)) (lam : (ZMod 5)ˣ) (σ : Equiv.Perm X) : Prop :=
  ∃ p : P, ∀ z : ZMod 5, ∀ x : X,
    q (z, x) = p.1 (((lam : ZMod 5) * z), σ x)

/-- Claim 38162: under the exact semiregular graph-normalizer and one-Sylow
voltage hypotheses, one block-origin function linearizes the whole normalizer. -/
def oneSylowC5NormalizerSimultaneouslySwitchingLinearizable : Prop :=
  ∀ (X : Type*) [Fintype X]
    (Γ : SimpleGraph (FiberSet X))
    (ρ : Equiv.Perm (FiberSet X))
    (P N : Subgroup (Equiv.Perm (FiberSet X)))
    (lam : N → (ZMod 5)ˣ) (τ : N → X → ZMod 5)
    (σ : N → Equiv.Perm X),
    P = Subgroup.zpowers ρ →
    Nonempty (P ≃* Multiplicative (ZMod 5)) →
    semiregularOnFibers P →
    standardFiveCycle ρ →
    pInvariantGraph Γ P →
    graphNormalizer Γ P N →
    P ≤ N →
    isSylowFiveIn (P.subgroupOf N) →
    affineVoltageCoordinates N lam τ σ →
      ∃ u : X → ZMod 5,
        let s := switchingEquiv u
        (∀ z : ZMod 5, ∀ x : X, s (z, x) = (z + u x, x)) ∧
        (∀ f : N, ∃ c : ZMod 5, ∀ z : ZMod 5, ∀ x : X,
          (s * f.1 * s⁻¹) (z, x) =
            (((lam f : ZMod 5) * z + c), σ f x)) ∧
        (∀ f : N, isModuloP P
          (s * f.1 * s⁻¹) (lam f) (σ f))

end MathlibPlus.Open.ResearchFormalization.R1356Claim38162
