import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1022

/-- The relative derivative appearing in the general finite-group criterion. -/
def relativeDerivative {G : Type*} [Group G] (f : Equiv.Perm G) (g : G) : Equiv.Perm G :=
  { toFun := fun x => f.symm (f (x * g) * (f g)⁻¹)
    invFun := fun x => f.symm (f x * f g) * g⁻¹
    left_inv := by
      intro x
      simp [mul_assoc]
    right_inv := by
      intro x
      simp [mul_assoc] }

def cayleyRelation {G : Type*} [Group G] (S : Set G) (x y : G) : Prop :=
  ∃ s, s ∈ S ∧ y = x * s

def inverseClosed {G : Type*} [Group G] (S : Set G) : Prop :=
  ∀ x, x ∈ S ↔ x⁻¹ ∈ S

def transportedBy {G : Type*} [Group G] (f : Equiv.Perm G)
    (S T : Set G) : Prop :=
  ∀ x y, cayleyRelation S x y ↔ cayleyRelation T (f x) (f y)

def sourceInversionInvariant {G : Type*} [Group G] (S : Set G) : Prop :=
  inverseClosed S

def transportedInversionInvariant {G : Type*} [Group G] (f : Equiv.Perm G)
    (S : Set G) : Prop :=
  ∀ x, x ∈ S ↔ f.symm ((f x)⁻¹) ∈ S

def derivativeOrbitUnion {G : Type*} [Group G] (f : Equiv.Perm G) (S : Set G) : Prop :=
  ∀ e ∈ Subgroup.closure (Set.range (relativeDerivative f)), e '' S = S

def transportedCayleyConnection {G : Type*} [Group G]
    (f : Equiv.Perm G) (S : Set G) : Prop :=
  1 ∉ S ∧ inverseClosed S ∧
    ∃ T : Set G, 1 ∉ T ∧ inverseClosed T ∧ transportedBy f S T

/-- Claim 28327: relative-derivative orbits together with both inversion tests. -/
def claim28327 {G : Type*} [Group G] [Fintype G] : Prop :=
  ∀ (f : Equiv.Perm G), f 1 = 1 → ∀ S : Set G,
    (transportedCayleyConnection f S ↔
      1 ∉ S ∧ derivativeOrbitUnion f S ∧
        sourceInversionInvariant S ∧ transportedInversionInvariant f S)

abbrev A7 := ZMod 7 × ZMod 7

def translate (B : Set A7) (c : A7) : Set A7 :=
  {z | ∃ b, b ∈ B ∧ z = b + c}

def pairDerivative (σ τ : Equiv.Perm A7) (y : A7) : Equiv.Perm A7 :=
  { toFun := fun z => σ.symm (σ (z + 2 • y) - 2 • τ y)
    invFun := fun z => σ.symm (σ z + 2 • τ y) - 2 • y
    left_inv := by
      intro z
      simp [sub_eq_add_neg, add_assoc, add_comm]
    right_inv := by
      intro z
      simp [sub_eq_add_neg, add_assoc, add_comm] }

def pairDerivativeGroup (σ τ : Equiv.Perm A7) : Subgroup (Equiv.Perm A7) :=
  Subgroup.closure (Set.range (pairDerivative σ τ))

def invariantUnder (B : Set A7) (e : Equiv.Perm A7) : Prop := e '' B = B

def unionOfPairDerivativeOrbits (σ τ : Equiv.Perm A7) (B : Set A7) : Prop :=
  ∀ e ∈ pairDerivativeGroup σ τ, invariantUnder B e

def sectionEquation (σ τ : Equiv.Perm A7) (B : Set A7) : Prop :=
  ∀ y : A7,
    σ '' translate B (2 • y) = translate (σ '' B) (2 • τ y)

/-- Claim 28328: the section equation and the pair-derivative orbit formulation. -/
def claim28328 : Prop :=
  ∀ (σ τ : Equiv.Perm A7), σ 0 = 0 → τ 0 = 0 → ∀ B : Set A7,
    (sectionEquation σ τ B ↔
      ∀ y : A7, invariantUnder B (pairDerivative σ τ y)) ∧
      ((∀ y : A7, invariantUnder B (pairDerivative σ τ y)) ↔
        unionOfPairDerivativeOrbits σ τ B)

end MathlibPlus.Open.ResearchFormalization.R1022
