import Mathlib
import MathlibPlus.Open.ResearchFormalization.R1203.Claim41970

namespace MathlibPlus.ResearchFormalization.R1203Claim41969

open MathlibPlus.ResearchFormalization.R1203Claim41970

/-- The `p`-primary component relation used for the finite abelian carrier. -/
def pComponentOf {p : ℕ} {A : Type*} [CommGroup A] [Fintype A]
    (V : Sylow p A) (a : A) (v : V) : Prop :=
  ∃ b : A, a = (v : A) * b ∧ Nat.Coprime p (orderOf b)

/-- Scalar linearity on an elementary abelian `p`-group, written using its
multiplicative presentation and the additive target `ZMod p`. -/
def linearFunctional {p : ℕ} (V : Type*) [Group V]
    (phi : V → ZMod p) : Prop :=
  scalarHom V phi ∧
    ∀ (r : ZMod p) (x : V), phi (x ^ r.val) = r * phi x

/-- The scalar cocycle is determined by the `p`-component of every subgroup
 element.  The component relation explicitly retains the carrier `L ∩ V`. -/
def restrictionFactorization {p : ℕ} {A : Type*} [CommGroup A]
    [Fintype A] (V : Sylow p A) (L : Subgroup A) (z : L → ZMod p)
    (phi : V → ZMod p) : Prop :=
  (∀ (x : L) (hx : (x : A) ∈ (V : Set A)),
      z x = phi ⟨(x : A), hx⟩) ∧
    ∀ x : L, ∃! v : V,
      pComponentOf V (x : A) v ∧
        (v : A) ∈ (L : Set A) ∧ z x = phi v

/-- The displayed formula for the global scalar extension. -/
def globalFormula {p : ℕ} {A : Type*} [CommGroup A]
    [Fintype A] {rho : c3 →* MulAut A} (V : Sylow p A)
    (phi : V → ZMod p) (f : eGroup A rho → ZMod p) : Prop :=
  ∀ (a : A) (i : c3), ∃! v : V,
    pComponentOf V a v ∧
      f (SemidirectProduct.mk a i) = phi v

/-- All carriers in the subgroup-to-global scalar extension assertion. -/def scalarCocycleExtension {p : ℕ} {A : Type*} [CommGroup A]
    [Fintype A] {rho : c3 →* MulAut A} {omega : ZMod p}
    (V : Sylow p A) (L : Subgroup A) (z : L → ZMod p)
    (phi : V → ZMod p) (f : eGroup A rho → ZMod p) : Prop :=
  scalarHom L z ∧
    linearFunctional V phi ∧
    restrictionFactorization V L z phi ∧
    matchingScalarCocycle (omega := omega) f ∧
    (∀ x : L,
      f (SemidirectProduct.inl (x : A)) = z x) ∧
    globalFormula V phi f

end MathlibPlus.ResearchFormalization.R1203Claim41969

namespace MathlibPlus.Open.ResearchFormalization.R1203

open MathlibPlus.ResearchFormalization.R1203Claim41970
open MathlibPlus.ResearchFormalization.R1203Claim41969

/-- Claim 41969: a scalar cocycle on a subgroup of the abelian kernel is a
homomorphism, factors through the elementary Sylow component, and extends by
the displayed formula to a matching scalar cocycle on `E(A,3)`. -/
def claim41969 : Prop :=
  ∀ (p : ℕ) [Fact (Nat.Prime p)], Nat.ModEq 3 p 1 →
    ∀ (A : Type*) [CommGroup A] [Fintype A]
      (rho : c3 →* MulAut A) (omega : ZMod p)
      (V : Sylow p A),
      MathlibPlus.Open.Research.elementaryAbelianSylow p V →
      matchingScalarAction (rho := rho) p omega V →
      ∀ (L : Subgroup A) (z : L → ZMod p),
        scalarHom L z →
        ∃ (phi : V → ZMod p) (f : eGroup A rho → ZMod p),
          scalarCocycleExtension (omega := omega) V L z phi f

end MathlibPlus.Open.ResearchFormalization.R1203
