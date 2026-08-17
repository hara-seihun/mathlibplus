import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1223QuadraticLift

noncomputable section

abbrev Fp (p : ℕ) := ZMod p
abbrev Plane (p : ℕ) := Fin 2 → Fp p
abbrev Fibre (p : ℕ) := Fin 3 → Fp p
abbrev H (p : ℕ) := Plane p × Fibre p
abbrev E (p : ℕ) := Fp p × H p

def quadraticF (p : ℕ) (u : Plane p) : Fibre p :=
  ![u 0 * (u 0 - 1),
    (2 * u 0 - 1) * u 1,
    u 1 ^ 2]

def qPhi (p : ℕ) (φ : Plane p → Fp p) (x : E p) : E p :=
  (x.1 + φ x.2.1, (x.2.1, x.2.2 + quadraticF p x.2.1))

def qPhiInv (p : ℕ) (φ : Plane p → Fp p) (x : E p) : E p :=
  (x.1 - φ x.2.1, (x.2.1, x.2.2 - quadraticF p x.2.1))

def translation (p : ℕ) (t : E p) : E p → E p :=
  fun x => x + t

def translationCopy (p : ℕ) : Set (E p → E p) :=
  Set.range (translation p)

def conjugatedTranslationCopy
    (p : ℕ) (φ : Plane p → Fp p) : Set (E p → E p) :=
  {f | ∃ t : E p,
    f = qPhiInv p φ ∘ translation p t ∘ qPhi p φ}

def phiDerivative
    (φ : Plane p → Fp p) (u c : Plane p) : Fp p :=
  φ (u + c) - φ u - φ c

/-- The same relative scalar difference read directly from the first coordinate
of the displayed `q_phi`. -/
def qPhiScalarDerivative
    (p : ℕ) (φ : Plane p → Fp p) (u c : Plane p) : Fp p :=
  (qPhi p φ (0, (u + c, 0))).1 -
    (qPhi p φ (0, (u, 0))).1 -
    (qPhi p φ (0, (c, 0))).1

def quadraticDerivative
    (p : ℕ) (u c : Plane p) : Fibre p :=
  quadraticF p (u + c) - quadraticF p u - quadraticF p c

def firstPlaneVector (p : ℕ) (u : Plane p) : Fibre p :=
  ![u 0, u 1, 0]

def secondPlaneVector (p : ℕ) (u : Plane p) : Fibre p :=
  ![0, u 0, u 1]

def displacementPlane (p : ℕ) (u : Plane p) : Submodule (Fp p) (Fibre p) :=
  Submodule.span (Fp p)
    ({firstPlaneVector p u, secondPlaneVector p u} : Set (Fibre p))

def expectedQuadraticDerivative
    (p : ℕ) (u c : Plane p) : Fibre p :=
  (2 * c 0) • firstPlaneVector p u +
    (2 * c 1) • secondPlaneVector p u

/-- Claim 30305: on the displayed odd-prime E=F_p plus H translation carrier,
the relative derivatives of q_phi are the stated scalar/vector differences,
and every nonzero quadratic direction has the displayed injective image. -/
def claim30305 : Prop :=
  ∀ (p : ℕ), Nat.Prime p → Odd p →
    ∀ (φ : Plane p → Fp p), φ 0 = 0 →
      let T : Set (E p → E p) := translationCopy p
      let q := qPhi p φ
      let Tq := conjugatedTranslationCopy p φ
      Function.Bijective q ∧
        (∀ x : E p, qPhiInv p φ (q x) = x ∧ q (qPhiInv p φ x) = x) ∧
        (∀ f, f ∈ T → Function.Bijective f) ∧
        (∀ f, f ∈ Tq → Function.Bijective f) ∧
        (∀ u c : Plane p,
          qPhiScalarDerivative p φ u c = phiDerivative φ u c ∧
          quadraticDerivative p u c = expectedQuadraticDerivative p u c) ∧
        (∀ u : Plane p, u ≠ 0 →
          Function.Injective (quadraticDerivative p u) ∧
          Set.range (quadraticDerivative p u) =
            (displacementPlane p u : Set (Fibre p)))

end
end MathlibPlus.Open.ResearchFormalization.R1223QuadraticLift
