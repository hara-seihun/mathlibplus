import Mathlib
import MathlibPlus.Open.ResearchFormalization.Batch1484

namespace MathlibPlus.Open.ResearchFormalization.R1575

noncomputable section

private abbrev F7 := ZMod 7
private abbrev H := MathlibPlus.Open.ResearchFormalization.Batch1484.H
private abbrev W := MathlibPlus.Open.ResearchFormalization.Batch1484.W 2
private abbrev G := W × H

private def hMul : H → H → H :=
  MathlibPlus.Open.ResearchFormalization.Batch1484.hMul

private def hOne : H :=
  MathlibPlus.Open.ResearchFormalization.Batch1484.hOne

private def hInv : H → H
  | (a, i) => (-((2 : F7) ^ ((3 - i.val) % 3)) * a, -i)

private def chi : H → F7 :=
  MathlibPlus.Open.ResearchFormalization.Batch1484.matchingScalarCharacter

private def hPeriod (lam : H → F7) : Set H :=
  {h | ∀ k : H, lam (hMul h k) = lam k}

private def hSubgroup (Q : Set H) : Prop :=
  hOne ∈ Q ∧
    (∀ h : H, h ∈ Q → hInv h ∈ Q) ∧
      ∀ h k : H, h ∈ Q → k ∈ Q → hMul h k ∈ Q

private def hPow (g : H) : ℕ → H
  | 0 => hOne
  | n + 1 => hMul (hPow g n) g

private def hCyclicOrder (Q : Set H) (n : ℕ) : Prop :=
  ∃ g : H,
    Q = {x : H | ∃ j : Fin n, hPow g j.val = x} ∧
      Set.ncard Q = n

private def normalizedProfile (lam : H → F7) (tau : H → W) : Prop :=
  lam hOne = 0 ∧ tau hOne = 0

private def rankOneNilpotent (N : W →ₗ[F7] W) : Prop :=
  N ≠ 0 ∧ N.comp N = 0 ∧
    Module.finrank F7 (LinearMap.range N) = 1

private def linearProfile (lam : H → F7) (N : W →ₗ[F7] W) (h : H) : W →ₗ[F7] W :=
  LinearMap.id + (lam h) • N

private def linearProfileInv
    (lam : H → F7) (N : W →ₗ[F7] W) (h : H) : W →ₗ[F7] W :=
  LinearMap.id - (lam h) • N

private def gMul (p q : G) : G :=
  (p.1 + chi p.2 • q.1, hMul p.2 q.2)

private def gInv (p : G) : G :=
  (-(chi (hInv p.2)) • p.1, hInv p.2)

private def profileMap
    (lam : H → F7) (tau : H → W) (N : W →ₗ[F7] W) : G → G
  | p => (linearProfile lam N p.2 p.1 + tau p.2, p.2)

private def profileMapInv
    (lam : H → F7) (tau : H → W) (N : W →ₗ[F7] W) : G → G
  | p => (linearProfileInv lam N p.2 (p.1 - tau p.2), p.2)

private def relativeDerivative
    (lam : H → F7) (tau : H → W) (N : W →ₗ[F7] W)
    (h k : H) (x w : W) : W :=
  (profileMapInv lam tau N
    (gMul
      (profileMap lam tau N (gMul (w, h) (x, k)))
      (gInv (profileMap lam tau N (x, k))))).1

private def defect (tau : H → W) (h k : H) : W :=
  tau (hMul h k) - tau h - chi h • tau k

private def derivativeStep
    (lam : H → F7) (tau : H → W) (N : W →ₗ[F7] W) (h : H)
    (u v : W) : Prop :=
  ∃ (x : W) (k : H), relativeDerivative lam tau N h k x u = v

private def derivativeOrbit
    (lam : H → F7) (tau : H → W) (N : W →ₗ[F7] W) (h : H) (w : W) : Set W :=
  {v | Relation.EqvGen (derivativeStep lam tau N h) w v}

private def coset (S : Submodule F7 W) (w : W) : Set W :=
  {v | v - w ∈ S}

/-- Fixed rank-one nilpotent profile over the matching scalar `E(C₇,3)` model. -/
def claim_39296 : Prop :=
  ∀ (N : W →ₗ[F7] W), rankOneNilpotent N →
    LinearMap.range N = LinearMap.ker N ∧
      Module.finrank F7 (LinearMap.range N) = 1 ∧
        ∀ (lam : H → F7) (tau : H → W),
          normalizedProfile lam tau →
            ∀ (w : W) (h : H),
              profileMap lam tau N (w, h) =
                (linearProfile lam N h w + tau h, h)

/-- Exact normalized relative-derivative formula. -/
def claim_39297 : Prop :=
  ∀ (N : W →ₗ[F7] W), rankOneNilpotent N →
    ∀ (lam : H → F7) (tau : H → W), normalizedProfile lam tau →
      ∀ (h k : H) (x w : W),
        relativeDerivative lam tau N h k x w =
          ((LinearMap.id : W →ₗ[F7] W) +
              (lam (hMul h k) - lam h) • N) w +
            (chi h * (lam (hMul h k) - lam k)) • N x +
              ((LinearMap.id : W →ₗ[F7] W) - (lam h) • N) (defect tau h k)

/-- The left-period subgroup and its nonzero-profile trichotomy. -/
def claim_39298 : Prop :=
  ∀ (lam : H → F7), lam hOne = 0 →
    let Q := hPeriod lam
    hSubgroup Q ∧
      (lam ≠ 0 →
        Q = {hOne} ∨ hCyclicOrder Q 7 ∨ hCyclicOrder Q 3)

/-- Exact derivative orbits outside the left-period subgroup. -/
def claim_39299 : Prop :=
  ∀ (N : W →ₗ[F7] W), rankOneNilpotent N →
    ∀ (lam : H → F7) (tau : H → W), normalizedProfile lam tau →
      ∀ (h : H), h ∉ hPeriod lam →
        let U := LinearMap.range N
        let D := Submodule.span F7 (Set.range (fun k : H => defect tau h k))
        (∀ (u : W), u ∈ U → ∀ (w : W),
          ∃ (x y : W) (k : H),
            relativeDerivative lam tau N h k x w -
              relativeDerivative lam tau N h k y w = u) ∧
          (∀ (k : H) (x w : W),
            Submodule.mkQ U
                (relativeDerivative lam tau N h k x w - w) =
              Submodule.mkQ U (defect tau h k)) ∧
          (∀ (w : W),
            derivativeOrbit lam tau N h w = coset (U ⊔ D) w) ∧
          (∀ (w : W),
            linearProfile lam N h '' derivativeOrbit lam tau N h w =
              derivativeOrbit lam tau N h w) ∧
          (∀ (w : W), linearProfile lam N h w - w ∈ U)

end
end MathlibPlus.Open.ResearchFormalization.R1575
