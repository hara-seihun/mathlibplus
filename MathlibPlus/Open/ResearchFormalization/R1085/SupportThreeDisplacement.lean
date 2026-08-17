import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1085

noncomputable section

abbrev SupportThreeBase := Fin 3 → ZMod 2
abbrev SupportThreeFiber := Fin 2 → ZMod 3
abbrev SupportThreeGroup := SupportThreeBase × SupportThreeFiber

def supportThreeFiberMap
    (σ : Equiv.Perm SupportThreeBase)
    (q : SupportThreeBase → Equiv.Perm SupportThreeFiber) :
    SupportThreeGroup → SupportThreeGroup :=
  fun p => (σ p.1, q p.1 p.2)

def activeFiberSupport
    (q : SupportThreeBase → Equiv.Perm SupportThreeFiber) :
    Finset SupportThreeBase := by
  classical
  exact Finset.univ.filter
    (fun u => u ≠ 0 ∧ q u ≠ Equiv.refl SupportThreeFiber)

def normalizedSupportThreePresentation
    (f : Equiv.Perm SupportThreeGroup)
    (σ : Equiv.Perm SupportThreeBase)
    (q : SupportThreeBase → Equiv.Perm SupportThreeFiber)
    (c d e : SupportThreeBase) : Prop :=
  σ 0 = 0 ∧
    q 0 = Equiv.refl SupportThreeFiber ∧
    (∀ a b, f (a, b) = supportThreeFiberMap σ q (a, b)) ∧
    c ≠ 0 ∧ d ≠ 0 ∧ e ≠ 0 ∧
    c ≠ d ∧ c ≠ e ∧ d ≠ e ∧
    activeFiberSupport q = {c, d, e}

def supportThreeDisplacement
    (q : SupportThreeBase → Equiv.Perm SupportThreeFiber)
    (u : SupportThreeBase) : AddSubgroup SupportThreeFiber :=
  AddSubgroup.closure
    (Set.range (fun t : SupportThreeFiber => t - q u t + q u 0))

/-- Claim 28735: the normalized support-three presentation has the three
proper individual displacement subgroups and full joint span. -/
def claim28735_individualAndJointDisplacementSubgroups
    (f : Equiv.Perm SupportThreeGroup)
    (σ : Equiv.Perm SupportThreeBase)
    (q : SupportThreeBase → Equiv.Perm SupportThreeFiber)
    (c d e : SupportThreeBase) : Prop :=
  normalizedSupportThreePresentation f σ q c d e ∧
    let Wc := supportThreeDisplacement q c
    let Wd := supportThreeDisplacement q d
    let We := supportThreeDisplacement q e
    Wc ≠ ⊤ ∧ Wd ≠ ⊤ ∧ We ≠ ⊤ ∧ Wc ⊔ Wd ⊔ We = ⊤

end

end MathlibPlus.Open.ResearchFormalization.R1085
