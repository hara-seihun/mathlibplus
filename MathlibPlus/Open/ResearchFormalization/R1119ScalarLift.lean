import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1119

abbrev S3 := Equiv.Perm (Fin 3)

def orderThreeUnit {p : ℕ} (ω : (ZMod p)ˣ) : Prop :=
  orderOf ω = 3

def scalarLiftFormula {p : ℕ} (ω : (ZMod p)ˣ)
    (σ : Equiv.Perm S3) (e : S3 → ZMod 3)
    (z : ZMod p) (h : S3) : ZMod p × S3 :=
  ((((ω ^ (e h).val : (ZMod p)ˣ) : ZMod p) * z), σ h)

/-- Claim 29117: the normalized order-three scalar lift on the product of the
prime cyclic fiber and the underlying set of S₃. -/
def normalizedOrderThreeScalarLift : Prop :=
  ∀ (p : ℕ), Nat.Prime p → p % 3 = 1 →
    ∀ (ω : (ZMod p)ˣ), orderThreeUnit ω →
      ∀ (σ : Equiv.Perm S3), σ 1 = 1 →
        ∀ (e : S3 → ZMod 3), e 1 = 0 →
          ∃ f : Equiv.Perm (ZMod p × S3),
            ∀ (z : ZMod p) (h : S3),
              f (z, h) = scalarLiftFormula ω σ e z h

end MathlibPlus.Open.ResearchFormalization.R1119
