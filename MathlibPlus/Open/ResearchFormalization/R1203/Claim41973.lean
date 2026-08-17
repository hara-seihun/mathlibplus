import Mathlib
import MathlibPlus.Open.Research.H1Shell

namespace MathlibPlus.ResearchFormalization.R1203

abbrev c3 := Multiplicative (ZMod 3)

abbrev eGroup (A : Type*) [CommGroup A]
    (rho : c3 →* MulAut A) :=
  SemidirectProduct A c3 rho

def cGenerator : c3 := Multiplicative.ofAdd (1 : ZMod 3)

def complementCoordinate {A : Type*} [CommGroup A]
    {rho : c3 →* MulAut A} (h : eGroup A rho) : ZMod 3 :=
  Multiplicative.toAdd (SemidirectProduct.rightHom h)

def matchingCharacter (p : ℕ) (omega : ZMod p)
    {A : Type*} [CommGroup A]
    {rho : c3 →* MulAut A} (h : eGroup A rho) : ZMod p :=
  omega ^ (ZMod.val (complementCoordinate h))

def matchingScalarAction (p : ℕ) (omega : ZMod p)
    {A : Type*} [CommGroup A] {rho : c3 →* MulAut A}
    (V : Sylow p A) : Prop :=
  omega ^ 3 = 1 ∧ omega ≠ 1 ∧ omega ≠ 0 ∧
    (∀ x : V, rho cGenerator x.1 = x.1 ^ omega.val) ∧
    (∀ x : V, rho cGenerator x.1 = x.1 → x = 1)

def matchingModule {p : ℕ} [Fact (Nat.Prime p)] {omega : ZMod p}
    {A : Type*} [CommGroup A]
    {rho : c3 →* MulAut A} (W : Type*) [AddCommGroup W]
    [Module (ZMod p) W] [DistribMulAction (eGroup A rho) W] : Prop :=
  (∀ (a : A) (w : W),
      (SemidirectProduct.inl a : eGroup A rho) • w = w) ∧
    (∀ (w : W),
      (SemidirectProduct.mk (1 : A) cGenerator : eGroup A rho) • w =
        omega • w)

def vectorCocycle {p : ℕ} {A : Type*} [CommGroup A]
    {rho : c3 →* MulAut A} {W : Type*} [AddCommGroup W]
    [DistribMulAction (eGroup A rho) W]
    (f : eGroup A rho → W) : Prop :=
  ∀ h k, f (h * k) = f h + h • f k

def subgroupCocycle {p : ℕ} {A : Type*} [CommGroup A]
    {rho : c3 →* MulAut A} {W : Type*} [AddCommGroup W]
    [DistribMulAction (eGroup A rho) W]
    (L : Subgroup (eGroup A rho)) (f : L → W) : Prop :=
  ∀ h k, f (h * k) = f h + (h : eGroup A rho) • f k

end MathlibPlus.ResearchFormalization.R1203

namespace MathlibPlus.Open.ResearchFormalization.R1203

open MathlibPlus.ResearchFormalization.R1203

def claim41973 : Prop :=
  ∀ (p : ℕ) [Fact (Nat.Prime p)], Nat.ModEq 3 p 1 →
    ∀ (A : Type*) [CommGroup A] [Fintype A]
      (rho : c3 →* MulAut A) (omega : ZMod p)
      (V : Sylow p A),
      MathlibPlus.Open.Research.elementaryAbelianSylow p V →
      matchingScalarAction (rho := rho) p omega V →
      ∀ (d : ℕ) (W : Type*) [AddCommGroup W]
        [Module (ZMod p) W] [FiniteDimensional (ZMod p) W]
        [DistribMulAction (eGroup A rho) W],
        1 ≤ d → Module.finrank (ZMod p) W = d →
        matchingModule (p := p) (omega := omega) (A := A) (rho := rho) W →
        ∀ (L : Subgroup (eGroup A rho)) (z : L → W),
          subgroupCocycle (p := p) L z →
          ∃ f : eGroup A rho → W,
            vectorCocycle (p := p) f ∧ ∀ h : L, f h = z h

end MathlibPlus.Open.ResearchFormalization.R1203
