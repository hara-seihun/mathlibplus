import Mathlib
import MathlibPlus.Open.Research.H1Shell

namespace MathlibPlus.ResearchFormalization.R1203Claim41970

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

def scalarHom {p : ℕ} (L : Type*) [Group L]
    (z : L → ZMod p) : Prop :=
  z 1 = 0 ∧ ∀ x y : L, z (x * y) = z x + z y

def subgroupCocycle {p : ℕ} {A : Type*} [CommGroup A]
    {rho : c3 →* MulAut A} {omega : ZMod p}
    (L : Subgroup (eGroup A rho)) (z : L → ZMod p) : Prop :=
  ∀ x y : L,
    z (x * y) = z x + matchingCharacter p omega (x : eGroup A rho) * z y

def matchingScalarCocycle {p : ℕ} {A : Type*} [CommGroup A]
    {rho : c3 →* MulAut A} {omega : ZMod p}
    (f : eGroup A rho → ZMod p) : Prop :=
  ∀ h k, f (h * k) = f h + matchingCharacter p omega h * f k

def restrictedProjection {A : Type*} [CommGroup A]
    {rho : c3 →* MulAut A} (L : Subgroup (eGroup A rho)) :
    L →* c3 :=
  (SemidirectProduct.rightHom : eGroup A rho →* c3).comp L.subtype

abbrev kernelInL {A : Type*} [CommGroup A]
    {rho : c3 →* MulAut A} (L : Subgroup (eGroup A rho)) : Subgroup L :=
  (restrictedProjection L).ker

def coboundary {p : ℕ} {A : Type*} [CommGroup A]
    {rho : c3 →* MulAut A} (omega s : ZMod p)
    (h : eGroup A rho) : ZMod p :=
  s * (1 - matchingCharacter p omega h)

end MathlibPlus.ResearchFormalization.R1203Claim41970

namespace MathlibPlus.Open.ResearchFormalization.R1203

open MathlibPlus.ResearchFormalization.R1203Claim41970

def claim41970 : Prop :=
  ∀ (p : ℕ) [Fact (Nat.Prime p)], Nat.ModEq 3 p 1 →
    ∀ (A : Type*) [CommGroup A] [Fintype A]
      (rho : c3 →* MulAut A) (omega : ZMod p)
      (V : Sylow p A),
      MathlibPlus.Open.Research.elementaryAbelianSylow p V →
      matchingScalarAction (rho := rho) p omega V →
      ∀ (L : Subgroup (eGroup A rho)),
        Function.Surjective (restrictedProjection L) →
        ∀ (z : L → ZMod p),
          subgroupCocycle (omega := omega) L z →
          ∃ (g : eGroup A rho → ZMod p) (s : ZMod p)
            (e : (L ⧸ kernelInL L) ≃* c3)
            (q : (L ⧸ kernelInL L) → ZMod p) (t : L) (a : A)
            (epsilon : ZMod 3),
            matchingScalarCocycle (omega := omega) g ∧
            (∀ u : kernelInL L, g (u : eGroup A rho) = z u) ∧
            (∀ x : L,
              e (QuotientGroup.mk' (kernelInL L) x) = restrictedProjection L x) ∧
            (∀ x : L,
              z x - g x = q (QuotientGroup.mk' (kernelInL L) x)) ∧
            t.1 = SemidirectProduct.mk a (Multiplicative.ofAdd epsilon) ∧
            (epsilon = 1 ∨ epsilon = 2) ∧
            IsUnit (1 - omega ^ epsilon.val) ∧
            matchingCharacter (A := A) (rho := rho) p omega
                (t : eGroup A rho) = omega ^ epsilon.val ∧
            coboundary (A := A) (rho := rho) omega s
                (t : eGroup A rho) = z t - g t ∧
            matchingScalarCocycle (omega := omega)
              (fun h : eGroup A rho =>
                g h + coboundary (A := A) (rho := rho) omega s h) ∧
            (∀ x : L,
              g x + coboundary (A := A) (rho := rho) omega s
                (x : eGroup A rho) = z x)

end MathlibPlus.Open.ResearchFormalization.R1203
