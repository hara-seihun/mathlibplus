import Mathlib
import MathlibPlus.Open.ResearchFormalization.R1205SupportOne

namespace MathlibPlus.Open.ResearchFormalization.R1205.Claim32241

open MathlibPlus.Open.ResearchFormalization.R1205SupportOne

noncomputable section

abbrev Cp (p : ℕ) := Multiplicative (ZMod p)
abbrev A4 := alternatingGroup (Fin 4)
abbrev CpA4 (p : ℕ) := Cp p × A4

/-- The base section selected by the transported inversion. -/
def transportedInversion (q : Equiv.Perm A4) (a : A4) : A4 :=
  q.symm ((q a)⁻¹)

/-- The actual relative derivative of the common-coordinate permutation. -/
def relativeDerivative (p : ℕ) (f : Equiv.Perm (CpA4 p))
    (connection vertex : CpA4 p) : CpA4 p :=
  f.symm (f (connection * vertex) * (f vertex)⁻¹)

/-- Translation on the prime fibre, using its additive `C_p` group law. -/
def fiberTranslation (p : ℕ) (τ : ZMod p) : Equiv.Perm (Cp p) :=
  Equiv.mulRight (Multiplicative.ofAdd τ)

/-- The formula with the transported landing section made explicit. -/
def activeDerivativeWithBase (p : ℕ) (q : Equiv.Perm A4)
    (σ : A4 → Equiv.Perm (Cp p)) (a : A4) (y : ZMod p) :
    Equiv.Perm (Cp p) :=
  (fiberTranslation p
      (y - Multiplicative.toAdd (σ a (Multiplicative.ofAdd y)))).trans
    (σ (transportedInversion q a)).symm

/-- The exact derivative formula uses `r = j_q(a)` and is tied to the
actual relative derivative of `f`, rather than being a free callback. -/
def activeDerivativeRealization (p : ℕ) (q : Equiv.Perm A4)
    (σ : A4 → Equiv.Perm (Cp p)) (f : Equiv.Perm (CpA4 p))
    (a : A4) (y : ZMod p) : Prop :=
  ∀ x : Cp p,
    relativeDerivative p f
        (Multiplicative.ofAdd y, a⁻¹) (x, a) =
      (activeDerivativeWithBase p q σ a y x,
        transportedInversion q a)

def isFiberTranslation (p : ℕ) (e : Equiv.Perm (Cp p)) : Prop :=
  ∃ τ : ZMod p, e = fiberTranslation p τ

def conjugateToNonzeroTranslation (p : ℕ) (e : Equiv.Perm (Cp p)) : Prop :=
  ∃ τ : ZMod p, ∃ g : Equiv.Perm (Cp p),
    τ ≠ 0 ∧ g * e * g.symm = fiberTranslation p τ

/-- Claim 32241: under the exact normalized support-one common-coordinate
carrier, a nontranslation active chart has a derivative quotient conjugate in
`Sym(C_p)` to a nonzero translation. -/
def claim32241 : Prop :=
  ∀ (p : ℕ), Nat.Prime p → 5 ≤ p →
    ∀ (q : Equiv.Perm A4) (σ : A4 → Equiv.Perm (Cp p))
      (f : Equiv.Perm (CpA4 p)),
      normalizedSupportOneData p q σ f →
      ∀ a : A4, σ a ≠ 1 → ¬ isFiberTranslation p (σ a) →
        ∃ y z : ZMod p,
          activeDerivativeRealization p q σ f a y ∧
            activeDerivativeRealization p q σ f a z ∧
            conjugateToNonzeroTranslation p
              (activeDerivativeWithBase p q σ a y *
                (activeDerivativeWithBase p q σ a z)⁻¹)

end
end MathlibPlus.Open.ResearchFormalization.R1205.Claim32241
