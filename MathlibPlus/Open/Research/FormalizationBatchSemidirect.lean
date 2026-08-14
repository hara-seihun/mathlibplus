import Mathlib

namespace MathlibPlus.Open.Research.BatchSemidirect

def semidirectMultiply {p : ℕ} {H : Type*} [Group H]
    (χ : H →* (ZMod p)ˣ)
    (a b : ZMod p × H) : ZMod p × H :=
  (a.1 + (χ a.2 : ZMod p) * b.1, a.2 * b.2)

def semidirectInverse {p : ℕ} {H : Type*} [Group H]
    (χ : H →* (ZMod p)ˣ)
    (a : ZMod p × H) : ZMod p × H :=
  (-((χ a.2⁻¹ : ZMod p) * a.1), a.2⁻¹)

def fibreAffineMap {p : ℕ} {H : Type*}
    [Group H] (lam : H → (ZMod p)ˣ) (tau : H → ZMod p)
    (a : ZMod p × H) : ZMod p × H :=
  ((lam a.2 : ZMod p) * a.1 + tau a.2, a.2)

def fibreAffineInverse {p : ℕ} {H : Type*}
    [Group H] (lam : H → (ZMod p)ˣ) (tau : H → ZMod p)
    (a : ZMod p × H) : ZMod p × H :=
  ((lam a.2 : ZMod p)⁻¹ * (a.1 - tau a.2), a.2)

def normalizedFibreDerivative {p : ℕ} {H : Type*}
    [Group H] (χ : H →* (ZMod p)ˣ)
    (lam : H → (ZMod p)ˣ) (tau : H → ZMod p)
    (g a : ZMod p × H) : ZMod p × H :=
  fibreAffineInverse lam tau
    (semidirectMultiply χ
      (fibreAffineMap lam tau (semidirectMultiply χ a g))
      (semidirectInverse χ (fibreAffineMap lam tau g)))

/-- The normalized relative-derivative formula from admitted Claim 47409. -/
def semidirectDerivativeFormula : Prop :=
  ∀ (p : ℕ), Nat.Prime p →
    ∀ (H : Type*) [Group H],
    ∀ (χ : H →* (ZMod p)ˣ)
      (lam : H → (ZMod p)ˣ) (tau : H → ZMod p),
    ∀ (x y : ZMod p) (h k : H),
      normalizedFibreDerivative χ lam tau (y, k) (x, h) =
        ( ((lam (h * k) : ZMod p) * (lam h : ZMod p)⁻¹) * x
            + (χ h : ZMod p) *
                (((lam (h * k) : ZMod p) - (lam k : ZMod p)) *
                  (lam h : ZMod p)⁻¹) * y
            + (tau (h * k) - (χ h : ZMod p) * tau k - tau h) *
                (lam h : ZMod p)⁻¹,
          h)

end MathlibPlus.Open.Research.BatchSemidirect
