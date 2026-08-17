import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R2888Claim47376

noncomputable section

/-- A genuine additive one-cocycle for the displayed group action. -/
def additiveOneCocycle {K L : Type*} [AddCommGroup K]
    [Group L] [DistribMulAction L K] (d : L → K) : Prop :=
  ∀ l m : L, d (l * m) = d l + l • d m

/-- The averaged coboundary witness. -/
def averagedCoboundary {K L : Type*} [AddCommGroup K]
    [Group L] [Fintype L] [DistribMulAction L K]
    (d : L → K) (a : K) : Prop :=
  (Nat.card L) • a = ∑ l : L, d l ∧
    ∀ l : L, d l = a - l • a

/-- An actual group extension carries the kernel as the exact kernel of its
quotient map. -/
def exactFiniteExtensionKernel
    {K M L : Type*} [AddCommGroup K] [Group M] [Group L]
    (ι : Multiplicative K →* M) (π : M →* L) : Prop :=
  Function.Injective ι ∧
    (∀ x : K, π (ι (Multiplicative.ofAdd x)) = 1) ∧
    (∀ m : M, π m = 1 →
      ∃ x : K, ι (Multiplicative.ofAdd x) = m)

/-- The section/cocycle carrier used for the complement argument. -/
def sectionedCocycleExtension
    {K M L : Type*} [AddCommGroup K] [Group M] [Group L]
    [DistribMulAction L K]
    (ι : Multiplicative K →* M) (π : M →* L)
    (s sV : L →* M) (d : L → K) : Prop :=
  exactFiniteExtensionKernel ι π ∧
    (∀ l : L, π (s l) = l) ∧
    (∀ l : L, π (sV l) = l) ∧
    (∀ l : L, ∀ x : K,
      ι (Multiplicative.ofAdd (l • x)) =
        s l * ι (Multiplicative.ofAdd x) * (s l)⁻¹) ∧
    (∀ l : L,
      sV l = ι (Multiplicative.ofAdd (d l)) * s l) ∧
    additiveOneCocycle d

/-- Claim 47376: in the genuine finite extension, the section difference is a
one-cocycle and coprime averaging gives the displayed coboundary. -/
def claim47376 : Prop :=
  ∀ (K L : Type*) [AddCommGroup K] [Fintype K]
    [Group L] [Fintype L] [DistribMulAction L K],
    Nat.Coprime (Nat.card L) (Nat.card K) →
    Function.Bijective (fun x : K => (Nat.card L) • x) ∧
      (∀ d : L → K,
        additiveOneCocycle d →
          ∃ a : K, averagedCoboundary d a) ∧
      (∀ (M : Type*) [Group M]
        (ι : Multiplicative K →* M) (π : M →* L)
        (s sV : L →* M) (d : L → K),
        sectionedCocycleExtension ι π s sV d →
          ∃ a : K, averagedCoboundary d a)

end
end MathlibPlus.Open.ResearchFormalization.R2888Claim47376
