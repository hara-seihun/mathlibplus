import MathlibPlus.Open.Basic

/-!
# Gap-free HCIZ determinant comparison

Statement-fidelity registry node for admitted claim 390 from legacy packet `C-0024`.
The packet's Vandermonde products are represented by determinants of mathlib's
Vandermonde matrices.  Both the displayed row determinant and its stated column
transpose version are retained.
-/

namespace MathlibPlus.Open.Analysis.HCIZ

/-- Moving each real exponent `αⱼ` to a complex exponent `βⱼ` with no smaller real
part changes the normalized exponential determinant by at most the corresponding
Vandermonde ratio, independently of the node gaps. -/
def gapFreeDeterminantComparison : Prop :=
  ∀ (n : ℕ) (u α : Fin n → ℝ) (β : Fin n → ℂ),
    0 < n →
    (∀ i, 0 ≤ u i) →
    StrictMono u →
    StrictMono α →
    (∀ j, α j ≤ (β j).re) →
    let complexMatrix : Matrix (Fin n) (Fin n) ℂ :=
      Matrix.of fun i j => Complex.exp (-(β j) * (u i : ℂ))
    let realMatrix : Matrix (Fin n) (Fin n) ℝ :=
      Matrix.of fun i j => Real.exp (-(α j) * u i)
    ‖complexMatrix.det‖ / |realMatrix.det| ≤
        ‖(Matrix.vandermonde β).det‖ / (Matrix.vandermonde α).det ∧
      ‖complexMatrix.transpose.det‖ / |realMatrix.transpose.det| ≤
        ‖(Matrix.vandermonde β).det‖ / (Matrix.vandermonde α).det

end MathlibPlus.Open.Analysis.HCIZ
