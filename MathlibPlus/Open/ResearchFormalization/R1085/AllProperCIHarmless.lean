import Mathlib
import MathlibPlus.Open.ResearchFormalization.FiberProfiles

namespace MathlibPlus.Open.ResearchFormalization.R1085CI

noncomputable section

open MathlibPlus.Open.ResearchFormalization.FiberProfiles

abbrev Base := MathlibPlus.Open.ResearchFormalization.FiberProfiles.Base2
abbrev Fiber := MathlibPlus.Open.ResearchFormalization.FiberProfiles.Fiber3
abbrev Group := MathlibPlus.Open.ResearchFormalization.FiberProfiles.FiberProduct

/-- The four base/support representatives in the R-1085 collision-saturated
atlas. -/
def a0 : Base := ![0, 0, 0]
def a1 : Base := ![1, 0, 0]
def a2 : Base := ![0, 1, 0]
def a3 : Base := ![1, 1, 0]
def a4 : Base := ![0, 0, 1]
def a5 : Base := ![1, 0, 1]
def a6 : Base := ![0, 1, 1]
def a7 : Base := ![1, 1, 1]

def rho0 : Equiv.Perm Base := Equiv.swap a6 a7

def rho1 : Equiv.Perm Base :=
  (Equiv.swap a6 a7).trans (Equiv.swap a5 a6)

def support123 : Finset Base := {a1, a2, a3}
def support234 : Finset Base := {a2, a3, a4}
def support456 : Finset Base := {a4, a5, a6}

def baseRelativeDerivative
    (σ : Equiv.Perm Base) (u : Base) : Equiv.Perm Base :=
  (Equiv.addRight u).trans σ |>.trans (Equiv.addRight (-(σ u))) |>.trans σ.symm

def baseDerivativeGroup (σ : Equiv.Perm Base) : Subgroup (Equiv.Perm Base) :=
  Subgroup.closure (Set.range (baseRelativeDerivative σ))

def baseOrbit (σ : Equiv.Perm Base) (x : Base) : Set Base :=
  {y | ∃ g : baseDerivativeGroup σ, g.1 x = y}

def pairCollisionSet (σ : Equiv.Perm Base) (S : Finset Base) : Finset Base := by
  classical
  exact Finset.univ.filter (fun m =>
    ∃ u ∈ S, ∃ v ∈ S, u ≠ v ∧ m = σ.symm (σ u + σ v))

def activeCollision (σ : Equiv.Perm Base) (S : Finset Base) : Prop :=
  ∃ m, m ∈ pairCollisionSet σ S ∧ m ∈ S

def inactiveCollisionOrbit (σ : Equiv.Perm Base) (S : Finset Base) : Prop :=
  ∃ m, m ∈ pairCollisionSet σ S ∧
    (∀ y, y ∈ baseOrbit σ m → y ∉ S) ∧
    (∀ y, y ∈ baseOrbit σ m → y ∈ pairCollisionSet σ S) ∧
    (∃ y, y ∈ baseOrbit σ m ∧ y ≠ m)

def collisionSaturatedClass
    (σ : Equiv.Perm Base) (S : Finset Base) (supportOrbitSize : ℕ) : Prop :=
  (σ = rho0 ∧ S = support123 ∧ supportOrbitSize = 3 ∧
      activeCollision σ S) ∨
    (σ = rho0 ∧ S = support234 ∧ supportOrbitSize = 12 ∧
      inactiveCollisionOrbit σ S) ∨
    (σ = rho1 ∧ S = support123 ∧ supportOrbitSize = 1 ∧
      activeCollision σ S) ∨
    (σ = rho1 ∧ S = support456 ∧ supportOrbitSize = 4 ∧
      inactiveCollisionOrbit σ S)

def displacementSubgroup
    (q : Base → Equiv.Perm Fiber) (u : Base) : AddSubgroup Fiber :=
  AddSubgroup.closure
    (Set.range (fun t : Fiber => t - q u t + q u 0))

def jointDisplacementSpan
    (q : Base → Equiv.Perm Fiber) (S : Finset Base) : AddSubgroup Fiber := by
  classical
  exact AddSubgroup.closure
    (⋃ u ∈ (S : Set Base), (displacementSubgroup q u : Set Fiber))

/-- Harmlessness for ordinary undirected Cayley CI on the explicit additive
carrier: every connection-set image presented by `f` is product-linearly
 equivalent to the source set. -/
def ordinaryCIHarmless (f : Equiv.Perm Group) : Prop :=
  ∀ S : Finset Group,
    addConnection S →
    addConnection (imageUnder f S) →
    realizesCayleyIsomorphism f S →
    ∃ M : GL3_2, ∃ N : GL2_3,
      productLinearImage M N S = imageUnder f S

/-- Claim 28742: every normalized map in each of the four displayed
collision-saturated classes, with three proper individual displacement
subgroups and full joint span, is ordinary-CI harmless. -/
def claim28742_allProperSupportThreeOrdinaryCI : Prop :=
  ∀ (f : Equiv.Perm Group)
    (σ : Equiv.Perm Base)
    (q : Base → Equiv.Perm Fiber)
    (c d e : Base)
    (supportOrbitSize : ℕ),
    fiberPresentation f σ q ∧
      c ≠ 0 ∧ d ≠ 0 ∧ e ≠ 0 ∧
      c ≠ d ∧ c ≠ e ∧ d ≠ e ∧
      activeFibers q = {c, d, e} →
    collisionSaturatedClass σ (activeFibers q) supportOrbitSize →
    let Wc := displacementSubgroup q c
    let Wd := displacementSubgroup q d
    let We := displacementSubgroup q e
    Wc ≠ ⊤ ∧ Wd ≠ ⊤ ∧ We ≠ ⊤ ∧
      jointDisplacementSpan q (activeFibers q) = ⊤ →
    ordinaryCIHarmless f

end

end MathlibPlus.Open.ResearchFormalization.R1085CI
