import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R5238ShiftedTopLayer

open scoped BigOperators

noncomputable section

/-- The staircase cell set for the partition `(d,d-1,...,1)`, with
zero-based row indices. -/
abbrev StaircaseCell (d : ℕ) := Σ i : Fin d, Fin (d - i.val)

/-- Semistandard tableaux on the staircase: rows are weakly increasing and
columns are strictly increasing. -/
def staircaseSemistandard {d : ℕ}
    (T : StaircaseCell d → Fin d) : Prop :=
  (∀ a b : StaircaseCell d,
    a.1 = b.1 → a.2.val ≤ b.2.val → T a ≤ T b) ∧
  (∀ a b : StaircaseCell d,
    a.2.val = b.2.val → a.1.val < b.1.val → T a < T b)

/-- The staircase Schur polynomial, defined by its semistandard-tableau
monomial expansion. -/
noncomputable def staircaseSchur {R : Type*} [CommSemiring R]
    (d : ℕ) : MvPolynomial (Fin d) R := by
  classical
  exact ∑ T : StaircaseCell d → Fin d,
    if staircaseSemistandard T then
      ∏ c : StaircaseCell d, MvPolynomial.X (T c)
    else 0

/-- The variables `X₁,...,X_d` in the shifted polynomial. -/
def shiftedX {R : Type*} [CommSemiring R] {d : ℕ}
    (i : Fin d) : MvPolynomial (Fin (d + 1)) R :=
  MvPolynomial.X i.castSucc

/-- The final variable is the shift variable `u`. -/
def shiftedU {R : Type*} [CommSemiring R] (d : ℕ) :
    MvPolynomial (Fin (d + 1)) R :=
  MvPolynomial.X (Fin.last d)

/-- The positive square-node substitution `X_i + i²u`, with one-based
indices as in the source. -/
def shiftedArgument {R : Type*} [CommSemiring R] {d : ℕ}
    (i : Fin d) : MvPolynomial (Fin (d + 1)) R :=
  shiftedX i + MvPolynomial.C ((i.val + 1) ^ 2 : R) * shiftedU d

/-- Schur evaluation after the joint square-node shift. -/
noncomputable def shiftedSchur {R : Type*} [CommSemiring R]
    (d : ℕ) : MvPolynomial (Fin (d + 1)) R :=
  MvPolynomial.eval₂ (MvPolynomial.C) (shiftedArgument (R := R))
    (staircaseSchur (R := R) d)

def staircaseScaleFactor (d : ℕ) : ℕ :=
  ∏ i ∈ Finset.range d, i.factorial

def staircaseLeadingScale (d : ℕ) : ℕ :=
  2 ^ d * d.factorial * staircaseScaleFactor d

/-- The natural-coefficient form of the shifted top layer. -/
noncomputable def shiftedTopLayerNat (d : ℕ) :
    MvPolynomial (Fin (d + 1)) ℕ :=
  MvPolynomial.C (staircaseLeadingScale d) * shiftedSchur (R := ℕ) d

/-- The integer-coefficient form of the exact top homogeneous layer
`A_d s_δ(X₁+1²u,...,X_d+d²u)`. -/
noncomputable def shiftedTopLayer (d : ℕ) :
    MvPolynomial (Fin (d + 1)) ℤ :=
  MvPolynomial.C (staircaseLeadingScale d : ℤ) * shiftedSchur (R := ℤ) d

/-- Coefficientwise equality with the natural expansion records that the
positive square-node substitutions introduce no cancellation. -/
def positiveShiftNoCancellation (d : ℕ) : Prop :=
  ∀ e : (Fin (d + 1) →₀ ℕ),
    (shiftedTopLayer d).coeff e =
      ((MvPolynomial.coeff e (shiftedTopLayerNat d) : ℕ) : ℤ)

/-- Claim 53839: every coefficient of the exact shifted top layer is a
nonnegative integer, and every nonzero coefficient is at least `A_d`; the
natural expansion also records the no-cancellation conclusion. -/
def claim53839 : Prop :=
  ∀ d : ℕ, 1 ≤ d →
    (∀ e : (Fin (d + 1) →₀ ℕ),
      0 ≤ (shiftedTopLayer d).coeff e ∧
        ((shiftedTopLayer d).coeff e ≠ 0 →
          (staircaseLeadingScale d : ℤ) ≤ (shiftedTopLayer d).coeff e)) ∧
    positiveShiftNoCancellation d

end
end MathlibPlus.Open.ResearchFormalization.R5238ShiftedTopLayer
