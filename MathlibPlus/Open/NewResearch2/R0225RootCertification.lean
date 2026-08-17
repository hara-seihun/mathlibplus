import Mathlib

namespace MathlibPlus.Open.NewResearch2.R0225RootCertification

open Classical

noncomputable section

/-- The closed rational rectangle used by the exact root certificate. -/
def rationalRectangleClosed (a b c d : ℚ) : Set ℂ :=
  {z : ℂ |
    (a : ℝ) ≤ z.re ∧ z.re ≤ (b : ℝ) ∧
      (c : ℝ) ≤ z.im ∧ z.im ≤ (d : ℝ)}

/-- The open interior of a rational rectangle. -/
def rationalRectangleInterior (a b c d : ℚ) : Set ℂ :=
  {z : ℂ |
    (a : ℝ) < z.re ∧ z.re < (b : ℝ) ∧
      (c : ℝ) < z.im ∧ z.im < (d : ℝ)}

/-- The boundary of the closed rational rectangle. -/
def rationalRectangleBoundary (a b c d : ℚ) : Set ℂ :=
  rationalRectangleClosed a b c d \ rationalRectangleInterior a b c d

/-- A finite exact root table, with a rational polynomial certificate for every
listed complex root.  The multiset equality retains root multiplicities. -/
def finiteExactRootTable (P : Polynomial ℚ)
    (n : ℕ) (roots : Fin n → ℂ)
    (algebraicCertificates : Fin n → Polynomial ℚ) : Prop :=
  let Pℂ := P.map (algebraMap ℚ ℂ)
  P ≠ 0 ∧
    Pℂ.roots = Multiset.map roots (Finset.univ : Finset (Fin n)).1 ∧
      (∀ i : Fin n,
        (algebraicCertificates i).Monic ∧
          Polynomial.IsRoot
            ((algebraicCertificates i).map (algebraMap ℚ ℂ)) (roots i) ∧
          Polynomial.IsRoot Pℂ (roots i))

/-- The exact interior root count of the polynomial. -/
def polynomialInteriorRootCount (a b c d : ℚ) (P : Polynomial ℚ) : ℕ :=
  let _ : DecidablePred (rationalRectangleInterior a b c d) :=
    Classical.decPred _
  ((P.map (algebraMap ℚ ℂ)).roots.filter
    (rationalRectangleInterior a b c d)).card

/-- The exact interior root count read from a finite root table. -/
def tableInteriorRootCount (a b c d : ℚ) (n : ℕ)
    (roots : Fin n → ℂ) : ℕ :=
  let _ : DecidablePred
      (fun i : Fin n => rationalRectangleInterior a b c d (roots i)) :=
    Classical.decPred _
  (Finset.univ.filter
    (fun i : Fin n => rationalRectangleInterior a b c d (roots i))).card

/-- One finite root card consists of a rational polynomial certificate and a
rational isolating box for its algebraic root. -/
abbrev RootCardCode := List ℚ × ℚ × ℚ × ℚ × ℚ

/-- A finite code consists only of exact rational root cards, a Boolean
boundary decision, and the resulting natural root count. -/
abbrev RootCertificateCode := Bool × ℕ × List RootCardCode

/-- Interpret the finite algebraic root certificates in a code. -/
def codeCertificatePolynomials (n : ℕ)
    (codes : List RootCardCode) : Fin n → Polynomial ℚ :=
  fun i =>
    ∑ k ∈ Finset.range (codes.getD i.1 ([], 0, 0, 0, 0)).1.length,
      Polynomial.C
          ((codes.getD i.1 ([], 0, 0, 0, 0)).1.getD k 0) *
        Polynomial.X ^ k

/-- Interpret the rational isolating box in a finite root card. -/
def codeRootBoxes (n : ℕ) (codes : List RootCardCode) : Fin n → Set ℂ :=
  fun i =>
    {z : ℂ |
      ((codes.getD i.1 ([], 0, 0, 0, 0)).2.1 : ℝ) ≤ z.re ∧
        z.re ≤ ((codes.getD i.1 ([], 0, 0, 0, 0)).2.2.1 : ℝ) ∧
        ((codes.getD i.1 ([], 0, 0, 0, 0)).2.2.2.1 : ℝ) ≤ z.im ∧
        z.im ≤ ((codes.getD i.1 ([], 0, 0, 0, 0)).2.2.2.2 : ℝ)}

/-- Every root card carries a nondegenerate rational box. -/
def codeRootBoxesNondegenerate (n : ℕ)
    (codes : List RootCardCode) : Prop :=
  ∀ i : Fin n,
    (codes.getD i.1 ([], 0, 0, 0, 0)).2.1 <
        (codes.getD i.1 ([], 0, 0, 0, 0)).2.2.1 ∧
      (codes.getD i.1 ([], 0, 0, 0, 0)).2.2.2.1 <
        (codes.getD i.1 ([], 0, 0, 0, 0)).2.2.2.2

/-- The rational boxes are isolating for the corresponding roots of `P`. -/
def codeRootBoxesIsolating (P : Polynomial ℚ) (n : ℕ)
    (roots : Fin n → ℂ) (codes : List RootCardCode) : Prop :=
  ∀ i : Fin n, ∀ z : ℂ,
    Polynomial.IsRoot (P.map (algebraMap ℚ ℂ)) z →
      z ∈ codeRootBoxes n codes i → z = roots i

/-- Exact validity of a finite rational/algebraic certificate code.  The code
is accepted only when its finite root table accounts for the full polynomial
root multiset, its rational polynomials certify the listed algebraic roots,
its Boolean decides boundary nonvanishing versus an exhibited boundary root,
and its natural number is the exact interior count. -/
def finiteExactCertificateCodeValid (a b c d : ℚ) (P : Polynomial ℚ)
    (code : RootCertificateCode) : Prop :=
  ∃ (n : ℕ) (roots : Fin n → ℂ)
    (boundaryRoot : Option (Fin n)),
    code.2.2.length = n ∧
      codeRootBoxesNondegenerate n code.2.2 ∧
      (∀ i : Fin n, roots i ∈ codeRootBoxes n code.2.2 i) ∧
      codeRootBoxesIsolating P n roots code.2.2 ∧
      finiteExactRootTable P n roots
        (codeCertificatePolynomials n code.2.2) ∧
      ((code.1 = false ∧ boundaryRoot = none ∧
          (∀ i : Fin n,
            ¬ rationalRectangleBoundary a b c d (roots i)) ∧
          (∀ z : ℂ,
            rationalRectangleBoundary a b c d z →
              Polynomial.eval z (P.map (algebraMap ℚ ℂ)) ≠ 0)) ∨
        (code.1 = true ∧ ∃ i : Fin n,
          boundaryRoot = some i ∧
            rationalRectangleBoundary a b c d (roots i) ∧
            Polynomial.IsRoot
              (P.map (algebraMap ℚ ℂ)) (roots i))) ∧
      code.2.1 = tableInteriorRootCount a b c d n roots

/-- Claim 18985: for every nonzero rational polynomial and every nondegenerate
rational rectangle, one uniform effective finite exact procedure emits a
rational/algebraic certificate deciding the boundary question and recording the
exact interior root count.  The `false` branch certifies boundary nonvanishing;
the `true` branch gives an exact boundary root, so boundary nonvanishing is not
asserted for rectangles whose boundary contains a root. -/
def claim18985 : Prop :=
  ∃ procedure : (List ℚ × ℚ × ℚ × ℚ × ℚ) → RootCertificateCode,
    Computable procedure ∧
      (∀ (a b c d : ℚ) (P : Polynomial ℚ),
        a < b → c < d → P ≠ 0 →
          ∃ coefficients : List ℚ,
            P = (∑ i ∈ Finset.range coefficients.length,
              Polynomial.C (coefficients.getD i 0) * Polynomial.X ^ i) ∧
            finiteExactCertificateCodeValid a b c d P
              (procedure (coefficients, a, b, c, d)))

end

end MathlibPlus.Open.NewResearch2.R0225RootCertification
