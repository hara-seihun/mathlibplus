import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R0322Claim19813

open scoped BigOperators Classical

noncomputable section

abbrev Sym := MvPolynomial ℕ ℚ
abbrev RationalFunction3 := FractionRing (MvPolynomial (Fin 3) ℚ)
abbrev Multiplicity (ell N : ℕ) :=
  {t : ℕ →₀ ℕ //
    t.sum (fun _ n => n) = ell ∧
      t.sum (fun j n => j * n) = N}
abbrev Partition (k : ℕ) :=
  {parts : List ℕ //
    parts.Pairwise (· ≥ ·) ∧
      (∀ a ∈ parts, 0 < a) ∧
      parts.sum = k}

def coordinate (i : Fin 3) : RationalFunction3 :=
  algebraMap (MvPolynomial (Fin 3) ℚ) RationalFunction3 (MvPolynomial.X i)

def x : RationalFunction3 := coordinate 0

def y : RationalFunction3 := coordinate 1

def z : RationalFunction3 := coordinate 2

def A : RationalFunction3 := x * (y - z)

def W : RationalFunction3 := y - 1

def w₁ : RationalFunction3 := x * (W + 1) / A

def w₂ : RationalFunction3 := (W + 1) / W

def p (m : ℕ) : Sym := MvPolynomial.X m

def twoLetterValue (m : ℕ) : RationalFunction3 :=
  w₁ * A ^ m + w₂ * W ^ m

def γ : Sym →ₐ[ℚ] RationalFunction3 :=
  MvPolynomial.aeval twoLetterValue

def pPartition {k : ℕ} (part : Partition k) : Sym :=
  (part.1.map p).prod

def degreeKSpan (k : ℕ) : Set Sym :=
  Set.range (fun part : Partition k => pPartition part)

def rankGamma (k : ℕ) : ℕ :=
  Module.finrank ℚ
    (Submodule.span ℚ
      (Set.image (fun f : Sym => γ f) (degreeKSpan k)))

def monomialProduct (t : ℕ →₀ ℕ) : MvPolynomial (Fin 2) ℚ :=
  t.support.prod (fun j =>
    (1 + MvPolynomial.X (0 : Fin 2) *
      MvPolynomial.X (1 : Fin 2) ^ j) ^ t j)

def D (ell N : ℕ) : ℕ :=
  Module.finrank ℚ
    (Submodule.span ℚ
      (Set.range (fun t : Multiplicity ell N => monomialProduct t.1)))

def rankDecompositionIntoMonomialSpans_claim19813 : Prop :=
  ∀ k : ℕ, 1 ≤ k →
    rankGamma k = ∑ ell ∈ Finset.Icc 1 k, D ell (k - ell)

end

end MathlibPlus.Open.ResearchFormalization.R0322Claim19813
