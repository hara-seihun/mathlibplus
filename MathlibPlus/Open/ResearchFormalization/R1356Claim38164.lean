import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1356Claim38164

abbrev FiberSet (X : Type*) := ZMod 5 × X
abbrev Potential (X : Type*) := X → ZMod 5

def constantPotentialSubmodule (X : Type*) :
    Submodule (ZMod 5) (Potential X) :=
  Submodule.span (ZMod 5)
    (Set.range (fun c : ZMod 5 => fun _ : X => c))

abbrev GaugeQuotient (X : Type*) :=
  (Potential X) ⧸ constantPotentialSubmodule X

def gaugeClass {X : Type*} (u : Potential X) : GaugeQuotient X :=
  Submodule.Quotient.mk u

private def graphAutomorphism {X : Type*}
    (Γ : SimpleGraph (FiberSet X)) (f : Equiv.Perm (FiberSet X)) : Prop :=
  ∀ a b, Γ.Adj a b ↔ Γ.Adj (f a) (f b)

private def semiregularOnFibers {X : Type*}
    (P : Subgroup (Equiv.Perm (FiberSet X))) : Prop :=
  ∀ p : P, p ≠ 1 → ∀ a : FiberSet X, p.1 a ≠ a

private def pInvariantGraph {X : Type*}
    (Γ : SimpleGraph (FiberSet X))
    (P : Subgroup (Equiv.Perm (FiberSet X))) : Prop :=
  ∀ p : P, ∀ a b, Γ.Adj a b ↔ Γ.Adj (p.1 a) (p.1 b)

private def graphNormalizer {X : Type*}
    (Γ : SimpleGraph (FiberSet X))
    (P N : Subgroup (Equiv.Perm (FiberSet X))) : Prop :=
  ∀ f : Equiv.Perm (FiberSet X),
    f ∈ N ↔ graphAutomorphism Γ f ∧
      f ∈ Subgroup.normalizer (P : Set (Equiv.Perm (FiberSet X)))

private def affineVoltageCoordinates {X : Type*}
    (N : Subgroup (Equiv.Perm (FiberSet X)))
    (lam : N → (ZMod 5)ˣ) (tau : N → Potential X)
    (sig : N → Equiv.Perm X) : Prop :=
  ∀ f : N, ∀ z : ZMod 5, ∀ x : X,
    f.1 (z, x) = ((lam f : ZMod 5) * z + tau f x, sig f x)

private def standardFiveCycle {X : Type*}
    (rho : Equiv.Perm (FiberSet X)) : Prop :=
  ∀ z : ZMod 5, ∀ x : X, rho (z, x) = (z + 1, x)

private def isSylowFiveIn
    {G : Type*} [Group G] (P : Subgroup G) : Prop :=
  IsPGroup 5 P ∧
    ∀ Q : Subgroup G, IsPGroup 5 Q → P ≤ Q → Q ≤ P

private def changedPotential {X : Type*}
    (lam : (ZMod 5)ˣ) (tau : Potential X) (sig : Equiv.Perm X)
    (u : Potential X) : Potential X :=
  fun x => tau x - (lam : ZMod 5) * u x + u (sig x)

private def isConstantPotential {X : Type*} (v : Potential X) : Prop :=
  ∃ c : ZMod 5, v = fun _ : X => c

private def affineGaugeActionData {X : Type*}
    (P N : Subgroup (Equiv.Perm (FiberSet X)))
    (lam : N → (ZMod 5)ˣ) (tau : N → Potential X)
    (sig : N → Equiv.Perm X)
    (a : N →* (GaugeQuotient X ≃ᵃ[ZMod 5] GaugeQuotient X)) : Prop :=
  let Pn := P.subgroupOf N
  Pn.Normal ∧
    (∀ p : Pn, a p = AffineEquiv.refl (ZMod 5) (GaugeQuotient X)) ∧
    (∀ f : N, ∀ u : Potential X,
      a f (gaugeClass u) =
        gaugeClass (fun x =>
          (lam f : ZMod 5) * u ((sig f).symm x) -
            tau f ((sig f).symm x))) ∧
    (∀ u : Potential X,
      ((∀ f : N, a f (gaugeClass u) = gaugeClass u) ↔
        ∀ f : N, isConstantPotential (changedPotential (lam f)
          (tau f) (sig f) u)))

private def affineTranslationCocycleData
    {H k V : Type*} [Group H] [CommRing k]
    [AddCommGroup V] [Module k V]
    (a : H →* (V ≃ᵃ[k] V))
    (L : H →* (V ≃ₗ[k] V)) (b : H → V) : Prop :=
  (∀ h : H, ∀ v : V, a h v = L h v + b h) ∧
    (∀ g h : H, b (g * h) = b g + L g (b h)) ∧
    (∃ s : V, ∀ h : H, b h = s - L h s)

/-- Claim 38164: Sylow-five coprimality gives a fixed point for the exact
normalizer gauge action, and every finite invertible-order affine action has
a coboundary translation part and a fixed point. -/
def coprimeAffineActionsHaveFixedGauge : Prop :=
  (∀ (H k V : Type*) [Fintype H] [Group H] [Field k]
      [AddCommGroup V] [Module k V] [FiniteDimensional k V]
      (a : H →* (V ≃ᵃ[k] V)),
      Nonempty V →
      IsUnit (Fintype.card H : k) →
        ∃ (L : H →* (V ≃ₗ[k] V)) (b : H → V) (s : V),
          affineTranslationCocycleData a L b ∧
          (∀ h : H, a h s = s)) ∧
  (∀ (X : Type*) [Fintype X]
      (Γ : SimpleGraph (FiberSet X))
      (rho : Equiv.Perm (FiberSet X))
      (P N : Subgroup (Equiv.Perm (FiberSet X)))
      (lam : N → (ZMod 5)ˣ) (tau : N → Potential X)
      (sig : N → Equiv.Perm X)
      (a : N →* (GaugeQuotient X ≃ᵃ[ZMod 5] GaugeQuotient X)),
      P = Subgroup.zpowers rho →
      Nonempty (P ≃* Multiplicative (ZMod 5)) →
      semiregularOnFibers P →
      standardFiveCycle rho →
      pInvariantGraph Γ P →
      graphNormalizer Γ P N →
      P ≤ N →
      affineVoltageCoordinates N lam tau sig →
      affineGaugeActionData P N lam tau sig a →
      isSylowFiveIn (P.subgroupOf N) →
        ¬ 5 ∣ (P.subgroupOf N).index ∧
        ∃ (L : N →* (GaugeQuotient X ≃ₗ[ZMod 5] GaugeQuotient X))
          (b : N → GaugeQuotient X) (s : GaugeQuotient X),
          affineTranslationCocycleData (k := ZMod 5) a L b ∧
          (∀ f : N, a f s = s))

end MathlibPlus.Open.ResearchFormalization.R1356Claim38164
