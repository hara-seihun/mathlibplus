import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1386Claims38478_38480

noncomputable section

abbrev BaseGroup (q : ℕ) := QuaternionGroup q
abbrev FullGroup (p q : ℕ) := QuaternionGroup (p * q)
abbrev LayerPoint (q : ℕ) := Fin 4 × ZMod q

structure TriangularPresentation (p q : ℕ) where
  chi : BaseGroup q →* (ZMod p)ˣ
  sigma : BaseGroup q → BaseGroup q
  lambda : BaseGroup q → (ZMod p)ˣ
  tau : BaseGroup q → ZMod p
  f : Equiv.Perm (FullGroup p q)
  chartG : FullGroup p q ≃ (ZMod p × BaseGroup q)
  chartH : BaseGroup q ≃ LayerPoint q

def affineOnFourLayers {p q : ℕ}
    (P : TriangularPresentation p q) : Prop :=
  ∃ π : Equiv.Perm (Fin 4),
    ∀ i : Fin 4, ∃ u : (ZMod q)ˣ, ∃ t : ZMod q,
      ∀ y : ZMod q,
        P.chartH (P.sigma (P.chartH.symm (i, y))) =
          (π i, (u : ZMod q) * y + t)

def chartIsSemidirect {p q : ℕ}
    (P : TriangularPresentation p q) : Prop :=
  ∀ x y : FullGroup p q,
    P.chartG (x * y) =
      ((P.chartG x).1 +
          (P.chi (P.chartG x).2 : ZMod p) * (P.chartG y).1,
        (P.chartG x).2 * (P.chartG y).2)

def triangularAffineForm {p q : ℕ}
    (P : TriangularPresentation p q) : Prop :=
  ∀ (x : ZMod p) (h : BaseGroup q),
    P.chartG (P.f (P.chartG.symm (x, h))) =
      ((P.lambda h : ZMod p) * x + P.tau h, P.sigma h)

def normalizedPresentation {p q : ℕ}
    (P : TriangularPresentation p q) : Prop :=
  P.f 1 = 1 ∧
    P.lambda 1 = 1 ∧
    P.tau 1 = 0 ∧
    P.sigma 1 = 1

def validTriangularPresentation {p q : ℕ}
    (P : TriangularPresentation p q) : Prop :=
  chartIsSemidirect P ∧
    affineOnFourLayers P ∧
    triangularAffineForm P ∧
    normalizedPresentation P

def scalarProfile {p q : ℕ} (P : TriangularPresentation p q)
    (h : BaseGroup q) : (ZMod p)ˣ :=
  P.lambda h * P.chi h * (P.chi (P.sigma h))⁻¹

def wholeBaseLeftPeriod {p q : ℕ}
    (P : TriangularPresentation p q) : Prop :=
  ∀ x h : BaseGroup q, scalarProfile P (x * h) = scalarProfile P h

def inverseClosed {G : Type*} [Group G] (S : Set G) : Prop :=
  ∀ s, s ∈ S → s⁻¹ ∈ S

def identityFree {G : Type*} [Group G] (S : Set G) : Prop :=
  (1 : G) ∉ S

def normalizedRelativeDerivative {p q : ℕ}
    (P : TriangularPresentation p q) (u : FullGroup p q)
    (x : FullGroup p q) : FullGroup p q :=
  P.f.symm (P.f (x * u) * (P.f u)⁻¹)

def invariantUnderRelativeDerivatives {p q : ℕ}
    (P : TriangularPresentation p q) (S : Set (FullGroup p q)) : Prop :=
  ∀ u x, x ∈ S → normalizedRelativeDerivative P u x ∈ S

/-- Claim 38478: in the actual quaternion carrier with a multiplication-linked
semidirect chart, a normalized triangular affine presentation with whole-base
left period has unit scalar profile, equivalently the displayed lambda ratio. -/
def claim38478 : Prop :=
  ∀ p q : ℕ,
    Nat.Prime p → Nat.Prime q → Odd p → Odd q → q < p →
      ∀ P : TriangularPresentation p q,
        validTriangularPresentation P →
        wholeBaseLeftPeriod P →
          (∀ h : BaseGroup q, scalarProfile P h = 1) ∧
          (∀ h : BaseGroup q,
            P.lambda h = P.chi (P.sigma h) * (P.chi h)⁻¹)

/-- Claim 38480: every identity-free inverse-closed connection set in the
actual quaternion group satisfying the normalized relative-derivative
invariance and whole-period hypotheses is sent through the triangular map to
its image under a genuine group automorphism. -/
def claim38480 : Prop :=
  ∀ p q : ℕ,
    Nat.Prime p → Nat.Prime q → Odd p → Odd q → q < p →
      ∀ P : TriangularPresentation p q,
        validTriangularPresentation P →
        ∀ S : Set (FullGroup p q),
          inverseClosed S →
          identityFree S →
          inverseClosed (P.f '' S) →
          invariantUnderRelativeDerivatives P S →
          wholeBaseLeftPeriod P →
            ∃ α : FullGroup p q ≃* FullGroup p q,
              P.f '' S = α '' S

end
end MathlibPlus.Open.ResearchFormalization.R1386Claims38478_38480
