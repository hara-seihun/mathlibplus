import Mathlib
import MathlibPlus.Open.ResearchFormalization.R1205SupportOne

namespace MathlibPlus.Open.ResearchFormalization.R1205.Claim32242

open MathlibPlus.Open.ResearchFormalization.R1205SupportOne

noncomputable section

abbrev Cp (p : ℕ) := Multiplicative (ZMod p)
abbrev A4 := alternatingGroup (Fin 4)
abbrev CpA4 (p : ℕ) := Cp p × A4

def transportedInversion (q : Equiv.Perm A4) (a : A4) : A4 :=
  q.symm ((q a)⁻¹)

def relativeDerivative (p : ℕ) (f : Equiv.Perm (CpA4 p))
    (connection vertex : CpA4 p) : CpA4 p :=
  f.symm (f (connection * vertex) * (f vertex)⁻¹)

def fiberTranslation (p : ℕ) (τ : ZMod p) : Equiv.Perm (Cp p) :=
  Equiv.mulRight (Multiplicative.ofAdd τ)

def activeDerivativeWithBase (p : ℕ) (q : Equiv.Perm A4)
    (σ : A4 → Equiv.Perm (Cp p)) (a : A4) (y : ZMod p) :
    Equiv.Perm (Cp p) :=
  (fiberTranslation p
      (y - Multiplicative.toAdd (σ a (Multiplicative.ofAdd y)))).trans
    (σ (transportedInversion q a)).symm

def activeDerivativeRealization (p : ℕ) (q : Equiv.Perm A4)
    (σ : A4 → Equiv.Perm (Cp p)) (f : Equiv.Perm (CpA4 p))
    (a : A4) (y : ZMod p) : Prop :=
  ∀ x : Cp p,
    relativeDerivative p f
        (Multiplicative.ofAdd y, a⁻¹) (x, a) =
      (activeDerivativeWithBase p q σ a y x,
        transportedInversion q a)

/-- Claim 32242: in the exact normalized support-one common-coordinate
carrier, a translated active chart yields the displayed `-τ` or `-2τ`
derivative according to `r = j_q(a)`, and both displacements are nonzero for
prime `p ≥ 5`. -/
def claim32242 : Prop :=
  ∀ (p : ℕ), Nat.Prime p → 5 ≤ p →
    ∀ (q : Equiv.Perm A4) (σ : A4 → Equiv.Perm (Cp p))
      (f : Equiv.Perm (CpA4 p)),
      normalizedSupportOneData p q σ f →
      ∀ a : A4, σ a ≠ 1 →
        ∀ τ : ZMod p, τ ≠ 0 → σ a = fiberTranslation p τ →
          (transportedInversion q a ≠ a →
            ∀ y : ZMod p,
              activeDerivativeRealization p q σ f a y ∧
                activeDerivativeWithBase p q σ a y =
                  fiberTranslation p (-τ)) ∧
          (transportedInversion q a = a →
            ∀ y : ZMod p,
              activeDerivativeRealization p q σ f a y ∧
                activeDerivativeWithBase p q σ a y =
                  fiberTranslation p (-2 * τ)) ∧
          (-τ ≠ 0 ∧ -2 * τ ≠ 0)

end
end MathlibPlus.Open.ResearchFormalization.R1205.Claim32242
