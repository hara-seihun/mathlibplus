import Mathlib

namespace MathlibPlus.Open.Research.CharacteristicP

noncomputable section

/-! The truncated polynomial and divided-power expressions occurring in the
characteristic-p degree-p claims. -/

abbrev Vec (p : ℕ) := Fin 3 → ZMod p

def truncationIdeal (p : ℕ) :
    Ideal (MvPolynomial (Fin 3) (ZMod p)) :=
  Ideal.span (Set.range (fun i : Fin 3 =>
    (MvPolynomial.X i : MvPolynomial (Fin 3) (ZMod p)) ^ p))

abbrev TruncatedPolynomial (p : ℕ) :=
  (MvPolynomial (Fin 3) (ZMod p)) ⧸ truncationIdeal p

def truncationMap (p : ℕ) :
    MvPolynomial (Fin 3) (ZMod p) →+* TruncatedPolynomial p :=
  Ideal.Quotient.mk _

def zvar (p : ℕ) (i : Fin 3) : TruncatedPolynomial p :=
  truncationMap p (MvPolynomial.X i)

abbrev Exponents (p : ℕ) := Fin 3 → Fin p

def pvec (p : ℕ) (a b c : ZMod p) : Vec p := ![a, b, c]

def boundedExponents (p m : ℕ) : Finset (Exponents p) :=
  Finset.univ.filter
    (fun α => ∑ i : Fin 3, (α i).val = m)

def zmonomial (p : ℕ) (α : Exponents p) : TruncatedPolynomial p :=
  ∏ i : Fin 3, zvar p i ^ (α i).val

def homogeneousComponent (p m : ℕ) :
    Submodule (ZMod p) (TruncatedPolynomial p) :=
  Submodule.span (ZMod p)
    (Set.range (fun α : {α : Exponents p // α ∈ boundedExponents p m} =>
      zmonomial p α.1))

def ell (p : ℕ) (d : Vec p) : TruncatedPolynomial p :=
  ∑ i : Fin 3, algebraMap (ZMod p) (TruncatedPolynomial p) (d i) * zvar p i

def gamma (p : ℕ) (d : Vec p) : TruncatedPolynomial p :=
  Finset.sum (boundedExponents p p) (fun α =>
    algebraMap (ZMod p) (TruncatedPolynomial p)
      (∏ i : Fin 3, (d i) ^ (α i).val *
        ((Nat.factorial (α i).val : ZMod p))⁻¹) * zmonomial p α)

def gammaInLinearPart (p : ℕ) (d : Vec p) : Prop :=
  ∃ h : TruncatedPolynomial p,
    h ∈ homogeneousComponent p (p - 1) ∧ gamma p d = ell p d * h

def coordinatePlane (p : ℕ) : Submodule (ZMod p) (Vec p) :=
  Submodule.span (ZMod p)
    (Set.range (fun j : Fin 2 =>
      if j = 0 then pvec p 1 0 0 else pvec p 0 1 0))

/-- Faithful open statement for Claim 56711. -/
def claim56711 : Prop :=
  ∀ p : ℕ, Nat.Prime p → p % 2 = 1 →
    (∀ a b : ZMod p, gammaInLinearPart p (pvec p a b 0)) ∧
    (∀ g : Vec p ≃ₗ[ZMod p] Vec p, ∀ d : Vec p,
      d ∈ (coordinatePlane p).map g.toLinearMap → gammaInLinearPart p d)

def gammaDecomposition (p : ℕ) (d : Vec p) : Prop :=
  ∃ h q : TruncatedPolynomial p,
    h ∈ homogeneousComponent p (p - 1) ∧
    q ∈ homogeneousComponent p (p - 3) ∧
    gamma p d = ell p d * h + zvar p 0 * zvar p 1 * zvar p 2 * q

/-- Faithful open statement for Claim 56712. -/
def claim56712 : Prop :=
  ∀ p : ℕ, Nat.Prime p → p % 2 = 1 → ∀ d : Vec p,
    gammaDecomposition p d ∧
    ((∃ i : Fin 3, d i = 0) →
      ∃ h : TruncatedPolynomial p,
        h ∈ homogeneousComponent p (p - 1) ∧ gamma p d = ell p d * h)

end
end MathlibPlus.Open.Research.CharacteristicP
