import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.Claim41031

noncomputable section

abbrev V (p : ℕ) := ZMod p × ZMod p

def quadraticC (p : ℕ) (t : ZMod p) : ZMod p :=
  (2 : ZMod p)⁻¹ * t * (t - 1)

def shearA (p : ℕ) (z : V p) : V p :=
  (z.1, z.2 + quadraticC p z.1)

def shearAInverse (p : ℕ) (z : V p) : V p :=
  (z.1, z.2 - quadraticC p z.1)

def shearB (p : ℕ) (z : V p) : V p :=
  (z.1 + quadraticC p z.2, z.2)

def mixedQuadraticShear (p : ℕ) (z : V p) : V p :=
  (z.1 + quadraticC p (z.2 - quadraticC p z.1),
    z.2 - quadraticC p z.1)

def affinePermutation (p : ℕ) (f : V p → V p) : Prop :=
  Function.Bijective f ∧
    ∃ L : V p →ₗ[ZMod p] V p, ∃ b : V p,
      ∀ z : V p, f z = L z + b

def fixedPointCard (p : ℕ) (f : V p → V p) : ℕ :=
  Set.ncard {z : V p | f z = z}

def mixedFixedPointSet (p : ℕ) : Set (V p) :=
  {z | (z.1 = 0 ∨ z.1 = 1) ∧ (z.2 = 0 ∨ z.2 = 1)}

def mixedIsBAInverse (p : ℕ) : Prop :=
  ∀ z : V p, mixedQuadraticShear p z =
    shearB p (shearAInverse p z)

/-- The affine fixed-space cardinality dichotomy and the exact four-point
fixed-set obstruction for the specified mixed map `g = B A⁻¹`. -/
def claim41031 : Prop :=
  ∀ p : ℕ, Nat.Prime p → Odd p →
    (∀ f : V p → V p,
      affinePermutation p f → f ≠ (id : V p → V p) →
        fixedPointCard p f = 0 ∨
          fixedPointCard p f = 1 ∨
            fixedPointCard p f = p ∨
              fixedPointCard p f = p ^ 2) ∧
    mixedIsBAInverse p ∧
    (∀ z : V p,
      mixedQuadraticShear p z = z ↔ z ∈ mixedFixedPointSet p) ∧
    fixedPointCard p (mixedQuadraticShear p) = 4 ∧
    ¬ affinePermutation p (mixedQuadraticShear p)

end

end MathlibPlus.Open.ResearchFormalization.Claim41031
