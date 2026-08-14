import Mathlib

namespace MathlibPlus.Open.ResearchFormalization

/-- Claim 18905: congruence preserves the generalized-eigenvalue predicate. -/
def claim18905 : Prop :=
  ∀ (n : ℕ) (G Δ S : Matrix (Fin n) (Fin n) ℝ),
    (∀ x : Fin n → ℝ, x ≠ 0 →
      0 < ∑ i : Fin n, x i * (G.mulVec x) i) →
    G.transpose = G →
    Δ.transpose = Δ →
    Matrix.det S ≠ 0 →
      ∀ lam : ℝ,
        ((∃ x : Fin n → ℝ,
            x ≠ 0 ∧ Δ.mulVec x = lam • G.mulVec x) ↔
          (∃ x : Fin n → ℝ,
            x ≠ 0 ∧
              (S.transpose * Δ * S).mulVec x =
                lam • (S.transpose * G * S).mulVec x))

/-- Claim 19230: a positive-definite symmetric pencil has only real,
nonzero generalized eigenvalues, including the determinant formulation. -/
def claim19230 : Prop :=
  ∀ (n : ℕ) (T D : Matrix (Fin n) (Fin n) ℝ),
    (∀ x : Fin n → ℝ, x ≠ 0 →
      0 < ∑ i : Fin n, x i * (T.mulVec x) i) →
    T.transpose = T →
    D.transpose = D →
    Matrix.det D ≠ 0 →
      let CT : Matrix (Fin n) (Fin n) ℂ := fun i j => T i j
      let CD : Matrix (Fin n) (Fin n) ℂ := fun i j => D i j
      let q : Polynomial ℂ :=
        Matrix.det (fun i j =>
          Polynomial.C (CT i j) - Polynomial.X * Polynomial.C (CD i j))
      (∀ z : ℂ, z ∈ q.roots → z.im = 0 ∧ z ≠ 0) ∧
        (∀ lam : ℂ,
          Matrix.det (CT - lam • CD) = 0 → lam.im = 0 ∧ lam ≠ 0) ∧
        (∀ lam : ℂ, ∀ x : Fin n → ℂ,
          x ≠ 0 → CT.mulVec x = lam • CD.mulVec x → lam.im = 0 ∧ lam ≠ 0)

end MathlibPlus.Open.ResearchFormalization
